#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

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

static cl::opt<unsigned> WindowBeginLine("WindowBeginLine", cl::desc("Line Begin of vulnerability window"));
static cl::opt<unsigned> WindowEndLine("WindowEndLine", cl::desc("Line End of vulnerability window"));
static cl::opt<std::string> WindowBeginFile("WindowBeginFile", cl::desc("TODO"));
static cl::opt<std::string> WindowEndFile("WindowEndFile", cl::desc("TODO"));

STATISTIC(LoopCounter, "Number of times in the loop 'basic block in window'");
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

        void prependWithDataFlowCheck(Instruction* inst, Value* v);
        void taintArgvAsInput(Module &M);

        bool doInitialization(Module &M) override;
        bool runOnModule(Module &M) override;

        // Nothing useful for AnalysisUsage for now (mateus)
        //void getAnalysisUsage(AnalysisUsage &AU) const override {
        //}
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
    checkRuntimeFunction = M.getOrInsertFunction("dfs$dfrtl_check", IRB.getVoidTy(), Type::getInt16PtrTy(M.getContext()), IRB.getInt8PtrTy(), IRB.getInt64Ty(), nullptr);
    taintInputFunction = M.getOrInsertFunction("dfs$dfrtl_add_input_label", IRB.getVoidTy(), IRB.getInt8PtrTy(), IRB.getInt64Ty(), nullptr);
    return false;
}

bool WindowDataFlow::runOnModule(Module &M) {
    if (!DL) return false;

    // Find begin and end inst
    for (Module::iterator f = M.begin(), fe = M.end(); f != fe; ++f) {
        for (Function::iterator b = (&*f)->begin(), be = f->end(); b != be; ++b) {
            for (BasicBlock::iterator i = b->begin(), ie = b->end(); i != ie; ++i) {
                Instruction* Inst = (&*i);
                if (MDNode *N = Inst->getMetadata("dbg")) {
                    DILocation Loc(N);
                    unsigned currLN = Loc.getLineNumber();
                    if (currLN == WindowBeginLine) {
                        beginWindowInst = Inst;
                    } else if (currLN == WindowEndLine) {
                        endWindowInst = Inst;
                    }
                } 
            }
        }
    }
    if (!beginWindowInst) {
        errs() << "Failed to find LLVM Instruction associated with line " << WindowBeginLine << ". Check if the LLVM assembly was compiled with debug information (command-line option:'-g')" << "\n";
        exit(1);
    }
    if (!endWindowInst) {
        errs() << "Failed to find LLVM Instruction associated with line " << WindowBeginLine << ". Check if the LLVM assembly was compiled with debug information (command-line option:'-g')" << "\n";
        exit(1);
    }

    errs() << "Got LLVM Instruction associated with begin line " << WindowBeginLine << ": '" << *beginWindowInst << "\n";
    errs() << "Got LLVM Instruction associated with end line " << WindowEndLine << ": '" << *endWindowInst << "\n";

    GlobalVariable* globalInputLabelVar = M.getGlobalVariable("globalInputLabel");


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
        LoopCounter++;

        Instruction* inst = discover.back();
        discover.pop_back();

        if(visited.count(inst)) {
            continue;
        }

        visited.insert(inst);

        BasicBlock *BB = inst->getParent();
        BasicBlock::iterator it(inst);

        bool foundEndInst = false;
        for(BasicBlock::iterator be = inst->getParent()->end(); it != be; ++it) {
            InstructionWindowCounter++;
            //errs() << *it << "\n";
            if (BranchInst* brInst = dyn_cast<BranchInst>(it)) {
                brInsts.push_back(brInst);
            }
            if (LoadInst* loadInst = dyn_cast<LoadInst>(it)) {
                loadInsts.push_back(loadInst);
            }
            if (StoreInst* storeInst = dyn_cast<StoreInst>(it)) {
                storeInsts.push_back(storeInst);
            }
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
            if(visited.count(firstInstruction)) {
                continue;
            }

            discover.push_back(firstInstruction);
        }
    }

    //for (auto inst : brInsts) {
    //if (inst->isUnconditional()) {
    //continue;
    //}
    //errs() << "Branches:" << *inst << "\n";
    //IRBuilder<> Builder(inst);
    //Value* vI32 = Builder.CreateZExt(inst->getCondition(), Builder.getInt32Ty());
    //Builder.CreateCall(checkRuntimeFunction, vI32);
    //}

    for (auto inst : loadInsts) {
        errs() << "Load:" << *inst << "\n";
        BasicBlock::iterator bb(inst);
        ++bb;

        IRBuilder<> Builder(&*bb);
        //Value* vI32 = Builder.CreatePtrToInt(inst, Builder.getInt32Ty());
        //Value* vI32 = Builder.CreateZExt(inst, Builder.getInt32Ty());
        Value* loadAddr = inst->getPointerOperand();
        Type* loadAddrType = loadAddr->getType();
        unsigned loadAddrTypeSize = DL->getTypeStoreSize(loadAddrType->getPointerElementType());

        if(loadAddrTypeSize == 2) {
            continue;
        }

        ConstantInt* elementSize = ConstantInt::get(Builder.getInt64Ty(), loadAddrTypeSize);
        errs() << "Inst:" << *inst << " addr:" << *loadAddr << " type:" << *loadAddrType << " size:" << *elementSize << "\n";
        Value* loadAddrI8Ptr = Builder.CreateBitCast(loadAddr, Builder.getInt8PtrTy());
        Builder.CreateCall3(checkRuntimeFunction, globalInputLabelVar, loadAddrI8Ptr, elementSize);
    }

    for (auto inst : storeInsts) {
        errs() << "Store:" << *inst << "\n";
        BasicBlock::iterator bb(inst);
        ++bb;

        IRBuilder<> Builder(&*bb);
        Value* storeAddr = inst->getPointerOperand();
        Type* storeAddrType = storeAddr->getType();
        unsigned storeAddrTypeSize = DL->getTypeStoreSize(storeAddrType->getPointerElementType());
        if(storeAddrTypeSize == 2) {
            continue;
        }


        ConstantInt* elementSize = ConstantInt::get(Builder.getInt64Ty(), storeAddrTypeSize);
        errs() << "Inst:" << *inst << " addr:" << *storeAddr << " type:" << *storeAddrType << " size:" << *elementSize << "\n";
        Value* storeAddrI8Ptr = Builder.CreateBitCast(storeAddr, Builder.getInt8PtrTy());
        Builder.CreateCall3(checkRuntimeFunction, globalInputLabelVar, storeAddrI8Ptr, elementSize);
    }
    //IRBuilder<> Builder(endWindowInst);
    //Value* vI32 = Builder.CreateZExt(inst->getCondition(), Builder.getInt32Ty());
    //Builder.CreateCall(checkRuntimeFunction, vI32);
    //errs() << "Will check if " << *endWindowInst->getOperand(1) << " is tainted.\n\n";
    //prependWithDataFlowCheck(endWindowInst, endWindowInst->getOperand(1));


    //taintArgvAsInput(M);


    return true;
}

void WindowDataFlow::prependWithDataFlowCheck(Instruction* inst, Value* v) {
}

//void WindowDataFlow::taintArgvAsInput(Module &M) {
//// Taint argv
//errs() << "Tainting argv in main\n"; 
//Function* mainFunc = M.getFunction("main"); 
//Function::arg_iterator args = mainFunc->getArgumentList().begin();
//Value* argc = &*args;
//++args;
//Value* argv = &*args;
////errs() << "argc" << *argc << "argv" << *argv << "\n";

//User *U = *(argv->users().begin());
//// the first use of an argument seems to be the one that give us the associated alloca address
//Instruction *argvStoreInst = dyn_cast<Instruction>(U);
//Value* argvAddr = argvStoreInst->getOperand(1);
////errs() << "argvAddr" << *argvAddr << "\n";

//BasicBlock::iterator it(argvStoreInst);
//++it;

//IRBuilder<> Builder(&*it);

//unsigned sizeOfAPointer = DL->getTypeStoreSize(argv->getType());
//Value* argcI64 = Builder.CreateSExtOrBitCast(argc, Builder.getInt64Ty());
//ConstantInt* sizeOfAPointerVal = ConstantInt::get(Builder.getInt64Ty(), sizeOfAPointer);
//Value* argvAddrI8Ptr = Builder.CreateBitCast(argvAddr, Builder.getInt8PtrTy());
//Value* argvSize = Builder.CreateMul(argcI64, sizeOfAPointerVal, "sizeOfArgv");
//Builder.CreateCall2(taintInputFunction, argvAddrI8Ptr, argvSize);
//Builder.CreateCall2(checkRuntimeFunction, argvAddrI8Ptr, argvSize);
//return;
//}
