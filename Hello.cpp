//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

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

#define DEBUG_TYPE "priNTAccesses"

static cl::opt<unsigned> RaceLineNumber("RaceLineNumber", cl::desc("Race associated line number"));
static cl::opt<std::string> RaceFilename("RaceFilename", cl::desc("Race associated line number"));
static cl::opt<bool> RaceIsRead("RaceIsRead", cl::desc("Race associated line number"));

STATISTIC(HelloCounter, "Counts number of functions greeted");
STATISTIC(NumInstrumentedReads, "Number of instrumented reads");
STATISTIC(NumInstrumentedWrites, "Number of instrumented writes");
STATISTIC(NumOmittedReadsBeforeWrite,
        "Number of reads ignored due to following writes");
STATISTIC(NumAccessesWithBadSize, "Number of accesses with bad size");
STATISTIC(NumInstrumentedVtableWrites, "Number of vtable ptr writes");
STATISTIC(NumInstrumentedVtableReads, "Number of vtable ptr reads");
STATISTIC(NumOmittedReadsFromConstantGlobals,
        "Number of reads from constant globals");
STATISTIC(NumOmittedReadsFromVtable, "Number of vtable reads");

namespace {
    // PrintAccesses - The second implementation with getAnalysisUsage implemented.
    struct PrintAccesses : public FunctionPass {
        static char ID; // Pass identification, replacement for typeid
        PrintAccesses() : FunctionPass(ID), DL(nullptr) {}

        void chooseInstructionsToInstrument(SmallVectorImpl<Instruction*> &Local, SmallVectorImpl<Instruction*> &All);
        bool addrPointsToConstantData(Value *Addr);
        bool instrumentLoadOrStore(Instruction *I);
        const DataLayout *DL;
        MemoryDependenceAnalysis* memdep;
        AliasAnalysis* aliasAnalysis;
        Instruction* raceInstruction1;

        bool doInitialization(Module &M) override;
        bool runOnFunction(Function &F) override;
        // We don't modify the program, so we preserve all analyses.
        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.addRequired<MemoryDependenceAnalysis>();
            AU.addRequired<AliasAnalysis>();
            AU.setPreservesAll();
        }
    };
}

char PrintAccesses::ID = 0;
static RegisterPass<PrintAccesses> Y("PrintAccesses", "PrintAccesses Pass");

static bool isAtomic(Instruction *I) {
    if (LoadInst *LI = dyn_cast<LoadInst>(I))
        return LI->isAtomic() && LI->getSynchScope() == CrossThread;
    if (StoreInst *SI = dyn_cast<StoreInst>(I))
        return SI->isAtomic() && SI->getSynchScope() == CrossThread;
    if (isa<AtomicRMWInst>(I))
        return true;
    if (isa<AtomicCmpXchgInst>(I))
        return true;
    if (isa<FenceInst>(I))
        return true;
    return false;
}

static bool isVtableAccess(Instruction *I) {
    if (MDNode *Tag = I->getMetadata(LLVMContext::MD_tbaa))
        return Tag->isTBAAVtableAccess();
    return false;
}


bool PrintAccesses::doInitialization(Module &M) {
    DataLayoutPass *DLP = getAnalysisIfAvailable<DataLayoutPass>();
    if (!DLP) {
        report_fatal_error("data layout missing");
    }
    DL = &DLP->getDataLayout();
    //memdep = &getAnalysis<MemoryDependenceAnalysis>();
    //if (!memdep) {
        //report_fatal_error("memdep missing");
    //}

    //bool found = false;
    //for (Module::iterator f = M.begin(), fe = M.end(); f != fe; ++f) {
        //for (Function::iterator b = (&*f)->begin(), be = f->end(); b != be; ++b) {
            //for (BasicBlock::iterator i = b->begin(), ie = b->end(); i != ie; ++i) {
                //Instruction* Inst = (&*i);
                //if (MDNode *N = Inst->getMetadata("dbg")) {
                    //DILocation Loc(N);
                    //unsigned currLN = Loc.getLineNumber();
                    //if (currLN == RaceLineNumber) {
                        //if (found) {
                            //errs() << "Found two instructions in the same line number!" << "\n";
                            //errs() << "    1: " << *raceInstruction1 << "\n";
                            //errs() << "    2: " << *Inst << "\n";
                        //}

                        //found = true;
                        //raceInstruction1 = Inst;
                        //errs() << "Got LLVM Instruction associated with line " << RaceLineNumber << ": '" << *Inst << "' in " << (&*f)->getName() << "\n";
                    //}
                //} 
            //}
        //}
    //}

    //if (!found) {
        //errs() << "Failed to find LLVM Instruction associated with line " << RaceLineNumber << ". Check if the LLVM assembly was compiled with debug information (command-line option:'-g')" << "\n";
        //exit(1);
    //}
}

bool PrintAccesses::runOnFunction(Function &F) {
    if (!DL) return false;
    //initializeCallbacks(*F.getParent());
    SmallVector<Instruction*, 8> RetVec;
    SmallVector<Instruction*, 8> AllLoadsAndStores;
    SmallVector<Instruction*, 8> LocalLoadsAndStores;
    SmallVector<Instruction*, 8> AtomicAccesses;
    SmallVector<Instruction*, 8> MemIntrinCalls;
    //bool Res = false;
    bool HasCalls = false;
    //bool SanitizeFunction = F.hasFnAttribute(Attribute::SanitizeThread);

    memdep = &getAnalysis<MemoryDependenceAnalysis>();
    aliasAnalysis = &getAnalysis<AliasAnalysis>();

    bool found = false;
    // Traverse all instructions, collect loads/stores/returns, check for calls.
    for (auto &BB : F) {
        for (auto &Inst : BB) {
            if (isAtomic(&Inst))
                AtomicAccesses.push_back(&Inst);
            else if (isa<LoadInst>(Inst) || isa<StoreInst>(Inst))
                LocalLoadsAndStores.push_back(&Inst);
            else if (isa<ReturnInst>(Inst))
                RetVec.push_back(&Inst);
            else if (isa<CallInst>(Inst) || isa<InvokeInst>(Inst)) {
                if (isa<MemIntrinsic>(Inst))
                    MemIntrinCalls.push_back(&Inst);
                HasCalls = true;
                chooseInstructionsToInstrument(LocalLoadsAndStores, AllLoadsAndStores);
            //MemDepResult result = memdep->getDependency(&Inst);
            //errs() << "Call: " << Inst << "\n";
            //errs() << *(result.getInst()) << "\n";
            //errs() << "\n";
            }
            if (MDNode *N = Inst.getMetadata("dbg")) {
                DILocation Loc(N);
                unsigned currLN = Loc.getLineNumber();
                if (currLN == RaceLineNumber) {
                    if (!found) {
                        errs() << "Found instructions with line number:" << RaceLineNumber << "\n";
                    }

                    errs() << "    " << Inst << "\n";
                    found = true;
                    if (RaceIsRead && isa<LoadInst>(&Inst)){
                        raceInstruction1 = &Inst;
                    }
                }
            } 
        }
        chooseInstructionsToInstrument(LocalLoadsAndStores, AllLoadsAndStores);
    }
    if(!found){
        return false;
    }
    errs() << "Got LLVM Instruction associated with line " << RaceLineNumber << ": '" << *raceInstruction1 << "' in " << F.getName() << "\n";

    MemDepResult result = memdep->getDependency(raceInstruction1);
    if (LoadInst *raceLoad = dyn_cast<LoadInst>(raceInstruction1)) {
        AliasAnalysis::Location loc = aliasAnalysis->getLocation(raceLoad);
        result = memdep->getPointerDependencyFrom(loc, RaceIsRead, (*F.begin()).begin(), &*F.begin());
    } else if (StoreInst *raceStore = dyn_cast<StoreInst>(raceInstruction1)) {
        AliasAnalysis::Location loc = aliasAnalysis->getLocation(raceStore);
        result = memdep->getPointerDependencyFrom(loc, RaceIsRead, (*F.begin()).begin(), &*F.begin());
    }
    errs() << "Dependency to it:" << "\n";
    //errs() << "    " << *(result.getInst())<< "\n";
    errs() << "    " << (result.isDef())<< "\n";
    errs() << "    " << (result.isClobber())<< "\n";
    errs() << "    " << (result.isUnknown())<< "\n";
    errs() << "    " << (result.isNonLocal())<< "\n";
    errs() << "    " << (result.isNonFuncLocal())<< "\n";
    Value *Addr, *val;
    for (auto Inst : AllLoadsAndStores) {
        if (LoadInst *LI = dyn_cast<LoadInst>(Inst)) {
            Addr = LI->getPointerOperand();
            val = LI;

            MemDepResult result = memdep->getDependency(LI);
            errs() << "LOAD: " << *LI << "\n";
            errs() << *(result.getInst()) << "\n";
            errs() << "\n";

            AliasAnalysis::AliasResult resultAlias;
            if (LoadInst *raceLoad = dyn_cast<LoadInst>(raceInstruction1)) {
                resultAlias = aliasAnalysis->alias(aliasAnalysis->getLocation(raceLoad), aliasAnalysis->getLocation(LI));
            } else if (StoreInst *raceStore = dyn_cast<StoreInst>(raceInstruction1)) {
                resultAlias = aliasAnalysis->alias(aliasAnalysis->getLocation(raceStore), aliasAnalysis->getLocation(LI));
            }
            errs() << "ALIAS:" << resultAlias << "\n";
        } else if (StoreInst *SI = dyn_cast<StoreInst>(Inst)) {
            Addr = SI->getPointerOperand();
            val = SI->getValueOperand();

            MemDepResult result = memdep->getDependency(SI);
            errs() << "STORE: " << *SI << "\n";
            errs() << *(result.getInst()) << "\n";
            errs() << "\n";

            AliasAnalysis::AliasResult resultAlias;
            if (LoadInst *raceLoad = dyn_cast<LoadInst>(raceInstruction1)) {
                resultAlias = aliasAnalysis->alias(aliasAnalysis->getLocation(raceLoad), aliasAnalysis->getLocation(SI));
            } else if (StoreInst *raceStore = dyn_cast<StoreInst>(raceInstruction1)) {
                resultAlias = aliasAnalysis->alias(aliasAnalysis->getLocation(raceStore), aliasAnalysis->getLocation(SI));
            }
            errs() << "ALIAS:" << resultAlias << "\n";
        } else { 
            llvm_unreachable("unknown Instruction type");
        }
        AliasAnalysis::ModRefResult resultAA;
        if (LoadInst *raceLoad = dyn_cast<LoadInst>(raceInstruction1)) {
            AliasAnalysis::Location loc = aliasAnalysis->getLocation(raceLoad);
            resultAA = aliasAnalysis->getModRefInfo(Inst, loc);
        } else if (StoreInst *raceStore = dyn_cast<StoreInst>(raceInstruction1)) {
            AliasAnalysis::Location loc = aliasAnalysis->getLocation(raceStore);
            resultAA = aliasAnalysis->getModRefInfo(Inst, loc);
        }
        errs() << "\n";
        errs() << *Inst << "\n";
        errs() << resultAA << "\n";
    }

    return false;
}

bool PrintAccesses::instrumentLoadOrStore(Instruction *I) {
    //IRBuilder<> IRB(I);
    //bool IsWrite = isa<StoreInst>(*I);
    //Value *Addr = IsWrite
    //? cast<StoreInst>(I)->getPointerOperand()
    //: cast<LoadInst>(I)->getPointerOperand();
    //int Idx = getMemoryAccessFuncIndex(Addr);
    //if (Idx < 0)
    //return false;
    //if (IsWrite && isVtableAccess(I)) {
    //DEBUG(dbgs() << "  VPTR : " << *I << "\n");
    //Value *StoredValue = cast<StoreInst>(I)->getValueOperand();
    //// StoredValue may be a vector type if we are storing several vptrs at once.
    //// In this case, just take the first element of the vector since this is
    //// enough to find vptr races.
    //if (isa<VectorType>(StoredValue->getType()))
    //StoredValue = IRB.CreateExtractElement(
    //StoredValue, ConstantInt::get(IRB.getInt32Ty(), 0));
    //if (StoredValue->getType()->isIntegerTy())
    //StoredValue = IRB.CreateIntToPtr(StoredValue, IRB.getInt8PtrTy());
    //// Call TsanVptrUpdate.
    //IRB.CreateCall2(TsanVptrUpdate,
    //IRB.CreatePointerCast(Addr, IRB.getInt8PtrTy()),
    //IRB.CreatePointerCast(StoredValue, IRB.getInt8PtrTy()));
    //NumInstrumentedVtableWrites++;
    //return true;
    //}
    //if (!IsWrite && isVtableAccess(I)) {
    //IRB.CreateCall(TsanVptrLoad,
    //IRB.CreatePointerCast(Addr, IRB.getInt8PtrTy()));
    //NumInstrumentedVtableReads++;
    //return true;
    //}
    //Value *OnAccessFunc = IsWrite ? TsanWrite[Idx] : TsanRead[Idx];
    //IRB.CreateCall(OnAccessFunc, IRB.CreatePointerCast(Addr, IRB.getInt8PtrTy()));
    //if (IsWrite) NumInstrumentedWrites++;
    //else         NumInstrumentedReads++;
    //return true;
}

static ConstantInt *createOrdering(IRBuilder<> *IRB, AtomicOrdering ord) {
    uint32_t v = 0;
    switch (ord) {
        case NotAtomic:              assert(false);
        case Unordered:              // Fall-through.
        case Monotonic:              v = 0; break;
                                     // case Consume:                v = 1; break;  // Not specified yet.
        case Acquire:                v = 2; break;
        case Release:                v = 3; break;
        case AcquireRelease:         v = 4; break;
        case SequentiallyConsistent: v = 5; break;
    }
    return IRB->getInt32(v);
}


// Instrumenting some of the accesses may be proven redundant.
// Currently handled:
//  - read-before-write (within same BB, no calls between)
//
// We do not handle some of the patterns that should not survive
// after the classic compiler optimizations.
// E.g. two reads from the same temp should be eliminated by CSE,
// two writes should be eliminated by DSE, etc.
//
// 'Local' is a vector of insns within the same BB (no calls between).
// 'All' is a vector of insns that will be instrumented.
void PrintAccesses::chooseInstructionsToInstrument(
        SmallVectorImpl<Instruction*> &Local,
        SmallVectorImpl<Instruction*> &All) {
    SmallSet<Value*, 8> WriteTargets;
    // Iterate from the end.
    for (SmallVectorImpl<Instruction*>::reverse_iterator It = Local.rbegin(),
            E = Local.rend(); It != E; ++It) {
        Instruction *I = *It;
        //if (StoreInst *Store = dyn_cast<StoreInst>(I)) {
        //WriteTargets.insert(Store->getPointerOperand());
        //} else {
        //LoadInst *Load = cast<LoadInst>(I);
        //Value *Addr = Load->getPointerOperand();
        //if (WriteTargets.count(Addr)) {
        //// We will write to this temp, so no reason to analyze the read.
        //NumOmittedReadsBeforeWrite++;
        //continue;
        //}
        //if (addrPointsToConstantData(Addr)) {
        //// Addr points to some constant data -- it can not race with any writes.
        //continue;
        //}
        //}
        All.push_back(I);
    }
    Local.clear();
}

bool PrintAccesses::addrPointsToConstantData(Value *Addr) {
    // If this is a GEP, just analyze its pointer operand.
    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(Addr))
        Addr = GEP->getPointerOperand();

    if (GlobalVariable *GV = dyn_cast<GlobalVariable>(Addr)) {
        if (GV->isConstant()) {
            // Reads from constant globals can not race with any writes.
            NumOmittedReadsFromConstantGlobals++;
            return true;
        }
    } else if (LoadInst *L = dyn_cast<LoadInst>(Addr)) {
        if (isVtableAccess(L)) {
            // Reads from a vtable pointer can not race with any writes.
            NumOmittedReadsFromVtable++;
            return true;
        }
    }
    return false;
}

