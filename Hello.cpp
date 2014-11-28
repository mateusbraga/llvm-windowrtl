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
    // WindowDataFlow - The second implementation with getAnalysisUsage implemented.
    struct WindowDataFlow : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        WindowDataFlow() : ModulePass(ID), DL(nullptr) {}

        const DataLayout *DL;

        Instruction* beginWindowInst;
        Instruction* endWindowInst;

        Value* DFSanGetLabel;
        Value* DFSanHasLabel;
        Value* checkRuntimeFunction;
        Value* taintInputFunction;

        void prependWithDataFlowCheck(Instruction* inst, Value* v);

        bool doInitialization(Module &M) override;
        bool runOnModule(Module &M) override;
        // We don't modify the program, so we preserve all analyses.
        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.setPreservesAll();
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
    DFSanGetLabel = M.getOrInsertFunction("dfsan_get_label", IRB.getInt32Ty(), IRB.getInt64Ty(), nullptr);
    DFSanHasLabel = M.getOrInsertFunction("dfsan_has_label", IRB.getInt32Ty(), IRB.getInt16Ty(), IRB.getInt16Ty(), nullptr);
    checkRuntimeFunction = M.getOrInsertFunction("dfs$dfrtl_check", IRB.getVoidTy(), IRB.getInt32Ty(), nullptr);
    taintInputFunction = M.getOrInsertFunction("dfs$dfrtl_add_input_label", IRB.getVoidTy(), IRB.getInt8PtrTy(), IRB.getInt64Ty(), nullptr);
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

    std::vector<Instruction*> discover;
    SmallSet<Instruction*, 8> visited;
    discover.push_back(beginWindowInst);

    while(true) {
        if (discover.size() == 0) {
            break;
        }
        LoopCounter++;

        Instruction* inst = discover.back();
        discover.pop_back();

        visited.insert(inst);

        BasicBlock *BB = inst->getParent();
        BasicBlock::iterator it(inst);

        bool foundEndInst = false;
        for(BasicBlock::iterator be = inst->getParent()->end(); it != be; ++it) {
            InstructionWindowCounter++;
            //errs() << *it << "\n";
            if (&*it == endWindowInst) {
                foundEndInst = true;
                break;
            }
        }
        if (foundEndInst) {
            errs() << "Will check if " << *endWindowInst->getOperand(1) << " is tainted.\n\n";
            prependWithDataFlowCheck(endWindowInst, endWindowInst->getOperand(1));
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

    // taint argv
    errs() << "Tainting argv in main\n"; 
   Function* mainFunc = M.getFunction("main"); 
   Function::arg_iterator args = mainFunc->getArgumentList().begin();
   Value* argc = &*args;
   ++args;
   Value* argv = &*args;
   //errs() << "argc" << *argc << "argv" << *argv << "\n";

   User *U = *(argv->users().begin());
   Instruction *argvStoreInst = dyn_cast<Instruction>(U);
   Value* argvAddr = argvStoreInst->getOperand(1);
   //errs() << "argvAddr" << *argvAddr << "\n";

   BasicBlock::iterator it(argvStoreInst);
   ++it;

   IRBuilder<> Builder(&*it);
   Value* argvAddrI8Ptr = Builder.CreateBitCast(argvAddr, Builder.getInt8PtrTy());
   Value* argcI64 = Builder.CreateSExtOrBitCast(argc, Builder.getInt64Ty());

   Builder.CreateCall2(taintInputFunction, argvAddrI8Ptr, argcI64);

   Value* vI32 = Builder.CreatePtrToInt(argv, Builder.getInt32Ty());
   Builder.CreateCall(checkRuntimeFunction, vI32);

   return true;
}

void WindowDataFlow::prependWithDataFlowCheck(Instruction* inst, Value* v) {
    //AllocaInst* labelAlloca = Builder.CreateAlloca(Builder.getInt32Ty(), 0, "label");
    //CallInst* callGetLabel = Builder.CreateCall(DFSanGetLabel, v, "label");
    ////StoreInst* storeLabel = Builder.CreateCall(DFSanGetLabel, v);
    //CallInst* callHasLabel = Builder.CreateCall(DFSanHasLabel, callGetLabel, globalInputLabel, "hasLabelResult");
    //Value* icmpResult = Builder.CreateICmpNE(callHasLabel, 0, "hasLabel");
    //BranchInst* branchInst = Builder.CreateCondBr(icmpResult, 0, "hasLabel");

    IRBuilder<> Builder(inst);
    //CallInst* callDataFlowRuntime = Builder.CreateCall(checkRuntimeFunction, v, "dfrtl_check");
   Value* vI32 = Builder.CreatePtrToInt(v, Builder.getInt32Ty());
    Builder.CreateCall(checkRuntimeFunction, vI32);
    return;
}
