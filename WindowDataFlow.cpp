#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
using namespace llvm;

#define DEBUG_TYPE "WindowDataFlow"

static cl::opt<std::string> WindowBeginLocation("WindowBeginLocation", cl::desc("Begin of vulnerability window"));
static cl::opt<std::string> WindowEndLocation("WindowEndLocation", cl::desc("End of vulnerability window"));

STATISTIC(BasicBlockCounter, "Number of basic blocks in the window");
STATISTIC(InstructionWindowCounter, "Number of instructions in the window");

namespace {
    struct WindowDataFlow : public ModulePass {
        static char ID; // LLVM required stuff
        WindowDataFlow() : ModulePass(ID), DL(nullptr) {}

        const DataLayout *DL;

        Instruction* beginWindowInst;
        Instruction* endWindowInst;

        Value* checkRuntimeFunction;
        Value* taintInputFunction;

        void checkUses(User* user);
        void checkLoadInstruction(LoadInst* li);
        void taintArgvAsInput(Module &M);

        bool doInitialization(Module &M) override;
        bool runOnModule(Module &M) override;

        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.addRequired<LoopInfo>();
        }
    };
}

char WindowDataFlow::ID = 0;
static RegisterPass<WindowDataFlow> Y("WindowDataFlow", "WindowDataFlow Pass");

bool WindowDataFlow::doInitialization(Module &M) {
    DataLayoutPass *DLP = getAnalysisIfAvailable<DataLayoutPass>();
    if (!DLP) {
        report_fatal_error("data layout missing");
    }
    DL = &DLP->getDataLayout();

    IRBuilder<> IRB(M.getContext());
    checkRuntimeFunction = M.getOrInsertFunction("dfrtl_check", IRB.getVoidTy(), IRB.getInt8PtrTy(), IRB.getInt64Ty(), nullptr);
    taintInputFunction = M.getOrInsertFunction("dfrtl_add_input_label", IRB.getVoidTy(), IRB.getInt8PtrTy(), IRB.getInt64Ty(), nullptr);
    return false;
}

bool WindowDataFlow::runOnModule(Module &M) {
    if (!DL) return false;

    // Get instructions that mark the beginning and end of the window
    for (Module::iterator f = M.begin(), fe = M.end(); f != fe; ++f) {
        for (Function::iterator b = (&*f)->begin(), be = f->end(); b != be; ++b) {
            for (BasicBlock::iterator i = b->begin(), ie = b->end(); i != ie; ++i) {
                Instruction* Inst = (&*i);
                if (MDNode *N = Inst->getMetadata("dbg")) {
                    DILocation Loc(N);
                    SmallString<128> location;
                    location += Loc.getDirectory(); 
                    location += "/" + std::string(Loc.getFilename());
                    location += ":" + itostr(Loc.getLineNumber());
                    location += ":" + itostr(Loc.getColumnNumber());

                    //errs() << location << "\n";
                    if (location.compare(WindowBeginLocation) == 0) {
                        beginWindowInst = Inst;
                    } else if (location.compare(WindowEndLocation) == 0) {
                        endWindowInst = Inst;
                    }
                } 
            }
        }
    }
    if (!beginWindowInst) {
        errs() << "Failed to find instruction of location " << WindowBeginLocation << ". Check if the LLVM assembly was compiled with debug information (command-line option:'-g')" << "\n";
        exit(1);
    }
    if (!endWindowInst) {
        errs() << "Failed to find instruction of location " << WindowEndLocation << ". Check if the LLVM assembly was compiled with debug information (command-line option:'-g')" << "\n";
        exit(1);
    }
    errs() << "BeginWindowInst \n\t(location: '" << WindowBeginLocation << "'): \n\t" << *beginWindowInst << "\n";
    errs() << "EndWindowInst \n\t(location: '" << WindowEndLocation << "'): \n\t" << *endWindowInst << "\n";

    // Phase 2: Search all possible paths between begin and end
    std::vector<Instruction*> discover;
    SmallSet<Instruction*, 8> visited;
    discover.push_back(beginWindowInst);
    std::vector<BranchInst*> brInsts;
    std::vector<LoadInst*> loadInsts;
    std::vector<StoreInst*> storeInsts;

    while(true) {
        if (discover.size() == 0) {
            break;
        }

        Instruction* inst = discover.back();
        discover.pop_back();
        if(visited.count(inst)) {
            continue;
        }
        visited.insert(inst);

        BasicBlockCounter++;

        BasicBlock *BB = inst->getParent();
        BasicBlock::iterator it(inst);

        LoopInfo& LI = getAnalysis<LoopInfo>(*BB->getParent());
        //for (LoopInfo::iterator it = LI.begin(), ie = LI.end(); it != ie; ++it) {
            ////errs() << "Got it:" << it << "\n";
            //errs() << "Got *it:" << *it << "\n";
        //}

        bool isLoopHeader = LI.isLoopHeader(BB);

        bool foundEndInst = false;
        for(BasicBlock::iterator be = inst->getParent()->end(); it != be; ++it) {
            InstructionWindowCounter++;
            //errs() << *it << "\n";
            
            if (isLoopHeader) {
                if (BranchInst* brInst = dyn_cast<BranchInst>(it)) {
                    brInsts.push_back(brInst);
                }
            }

            //if (LoadInst* loadInst = dyn_cast<LoadInst>(it)) {
                //loadInsts.push_back(loadInst);
            //}
            //if (StoreInst* storeInst = dyn_cast<StoreInst>(it)) {
                //storeInsts.push_back(storeInst);
            //}
            if (&*it == endWindowInst) {
                foundEndInst = true;
                break;
            }
        }
        if (foundEndInst) {
            continue;
        }

        for (succ_iterator PI = succ_begin(BB), E = succ_end(BB); PI != E; ++PI) {
            BasicBlock *succ = *PI;
            Instruction* firstInstruction = &*(succ->begin());
            discover.push_back(firstInstruction);
        }
    }

    // Phase 3: Instrument!
    taintArgvAsInput(M);

    for (BranchInst* inst : brInsts) {
        if (inst->isUnconditional()) {
            continue;
        }
        errs() << "Branches:" << *inst << "\n";

        checkUses(inst);
    }

    return true;
}

void WindowDataFlow::checkUses(User* user) {
    for (Use &U : user->operands()) {
        Value *v = U.get();

        if (LoadInst* li = dyn_cast<LoadInst>(v)) {
            checkLoadInstruction(li);
            continue;
        }

        if (User* u = dyn_cast<User>(v)) {
            checkUses(u);
        }
    }
}

void WindowDataFlow::checkLoadInstruction(LoadInst* li) {
    BasicBlock::iterator bb(li);
    ++bb;
    // Add check after load
    IRBuilder<> Builder(&*bb);

    Value* loadAddr = li->getPointerOperand();
    Type* loadAddrType = loadAddr->getType();
    unsigned loadAddrTypeSize = DL->getTypeStoreSize(loadAddrType->getPointerElementType());

    if(loadAddrTypeSize == 2) {
        // FIXME this is just to ignore labels, can be improved
        return;
    }

    ConstantInt* elementSize = ConstantInt::get(Builder.getInt64Ty(), loadAddrTypeSize);
    errs() << "Load:" << *li << " addr:" << *loadAddr << " type:" << *loadAddrType << " size:" << *elementSize << "\n";
    Value* loadAddrI8Ptr = Builder.CreateBitCast(loadAddr, Builder.getInt8PtrTy());
    Builder.CreateCall2(checkRuntimeFunction, loadAddrI8Ptr, elementSize);
}

void WindowDataFlow::taintArgvAsInput(Module &M) {
    // Taint argv
    errs() << "Tainting argv in main\n"; 
    Function* mainFunc = M.getFunction("main"); 
    Function::arg_iterator args = mainFunc->getArgumentList().begin();
    Value* argc = &*args;
    ++args;
    Value* argv = &*args;
    //errs() << "argc" << *argc << "argv" << *argv << "\n";

    User *U = *(argv->users().begin());
    // the first use of an argument seems to be the one that give us the associated alloca address
    Instruction *argvStoreInst = dyn_cast<Instruction>(U);
    Value* argvAddr = argvStoreInst->getOperand(1);
    //errs() << "argvAddr" << *argvAddr << "\n";

    BasicBlock::iterator it(argvStoreInst);
    ++it;

    IRBuilder<> Builder(&*it);

    unsigned sizeOfAPointer = DL->getTypeStoreSize(argv->getType());
    Value* argcI64 = Builder.CreateSExtOrBitCast(argc, Builder.getInt64Ty());
    ConstantInt* sizeOfAPointerVal = ConstantInt::get(Builder.getInt64Ty(), sizeOfAPointer);
    Value* argvAddrI8Ptr = Builder.CreateBitCast(argvAddr, Builder.getInt8PtrTy());
    Value* argvSize = Builder.CreateMul(argcI64, sizeOfAPointerVal, "sizeOfArgv");
    Builder.CreateCall2(taintInputFunction, argvAddrI8Ptr, argvSize);
    return;
}
