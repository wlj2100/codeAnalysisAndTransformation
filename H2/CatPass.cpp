#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include <assert.h>
#include <string.h>
#include <vector>
#include <set>

using namespace llvm;
using namespace std;

namespace {
  struct CAT : public FunctionPass {
    static char ID; 

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      //errs() << "Hello LLVM World at \"doInitialization\"\n" ;
      return false;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed

    int getCatType(Function *callee) const{
      std::string funcName = callee->getName();
      if (funcName == "CAT_binary_add") 
        return 0;
      if (funcName == "CAT_binary_sub") 
        return 1;
      if (funcName == "CAT_create_signed_value") 
        return 2;
      if (funcName == "CAT_get_signed_value") 
        return 3;
      return -1;
    }

    bool runOnFunction (Function &F) override {
      //errs() << "Hello LLVM World at \"runOnFunction\"\n" ;
      bool modified = false;
      std::vector<Instruction *> insV;
      std::vector<std::set<Instruction *>> genSets;
      std::vector<std::set<Instruction *>> killSets;
      for (auto& B : F) {
        for (auto& I : B) {
          insV.push_back(&I);
          genSets.push_back(std::set<Instruction *>());
          killSets.push_back(std::set<Instruction *>());
          if (auto* call = dyn_cast<CallInst>(&I)) {
            Function *callee;
            callee = call->getCalledFunction();
            switch(getCatType(callee)) {
              case 0:
              case 1: genSets.back().insert(&I);
                      if (auto* subIns = dyn_cast<Instruction>(call->getArgOperand(0))) {
                        killSets.back().insert(subIns);
                        //for (auto& U : subIns->uses()) {
                        //  User* user = U.getUser();
                        for (auto user : subIns->users()) {
                          if (auto* i = dyn_cast<CallInst>(user)) {
                            if (getCatType(i->getCalledFunction()) != -1 && getCatType(i->getCalledFunction()) != 3 ) {
                                auto* subsub = dyn_cast<Instruction>(i->getArgOperand(0));
                                if (&I == subIns || &I == subsub || subIns == subsub) {
                                  killSets.back().insert(i);
                                }
                                // && killSets.back().find(i) != killSets.back().end()
                            }
                              
                          }
                        }
                        if (killSets.back().find(&I) !=killSets.back().end()) {
                          killSets.back().erase(&I);
                        }
                      }
                      break;
              case 2: genSets.back().insert(&I);
                      for (auto U : I.users()) {
                        if (auto* i = dyn_cast<CallInst>(U)) {
                          if (getCatType(i->getCalledFunction()) != -1 && getCatType(i->getCalledFunction()) != 3) {
                              //errs() << "type is :" << i->getType() << "\n";
                            auto* subIns = dyn_cast<Instruction>(i->getArgOperand(0));
                            if (&I == subIns) {
                              killSets.back().insert(i);
                            }
                          }
                        }
                      }
                      //if 
                      break;
              case 3:
              default:
                      break;
            }
          } 
        }
        
      }
      errs() << "START FUNCTION: " << F.getName() << '\n';
      for (int i = 0; i < insV.size(); i++) {
        Instruction* I = insV[i];
        errs() << "INSTRUCTION: " << *I << "\n";
        errs() << "***************** GEN\n{\n";
        for (auto it = genSets[i].begin(); it != genSets[i].end(); ++it) {
          errs() << " " << **it << "\n";
        }
        errs() << "}\n**************************************\n***************** KILL\n{\n";
        for (auto it = killSets[i].begin(); it != killSets[i].end(); ++it) {
          errs() << " " << **it << "\n";
        }
        errs() << "}\n**************************************\n\n\n\n";
      }
      insV.clear();
      genSets.clear();
      killSets.clear();

      return modified;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      //errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;
      AU.setPreservesAll();
    }
  };
}

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT * _PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT());}}); // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT()); }}); // ** for -O0
