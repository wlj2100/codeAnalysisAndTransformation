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
#include "llvm/IR/CFG.h"
#include <assert.h>
#include <string.h>
#include <vector>
#include <set>
#include <algorithm>
#include <iterator>
#include "llvm/IR/Constants.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/DependenceAnalysis.h"

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

// function to help distinguishing CAT function
    int getCatType(Function* callee) const{
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

// function to generate gen & kill set for one instruction, return a pair of sets
    std::pair<std::set<Instruction*>, std::set<Instruction*>> getGenKillPair(Instruction &I) {
      std::set<Instruction*> genSet;
      std::set<Instruction*> killSet;
      if (auto* call = dyn_cast<CallInst>(&I)) {
        Function* callee;
        callee = call->getCalledFunction();
        switch(getCatType(callee)) {
          case 0:
          case 1: genSet.insert(&I);
                  if (auto* subIns = dyn_cast<Instruction>(call->getArgOperand(0))) {
                    killSet.insert(subIns);
                    for (auto user : subIns->users()) {
                      if (auto* i = dyn_cast<CallInst>(user)) {
                        if (getCatType(i->getCalledFunction()) != -1 && getCatType(i->getCalledFunction()) != 3) {
                          auto* subsub = dyn_cast<Instruction>(i->getArgOperand(0));
                          if (&I == subIns || &I == subsub || subIns == subsub) {
                            killSet.insert(i);
                          }
                        }
                      }
                    }
                    if (killSet.find(&I) !=killSet.end()) {
                      killSet.erase(&I);
                    }
                  }
                  break;
          case 2: genSet.insert(&I);
                  for (auto U : I.users()) {
                    if (auto* i = dyn_cast<CallInst>(U)) {
                      if (getCatType(i->getCalledFunction()) != -1 && getCatType(i->getCalledFunction()) != 3) {
                              //errs() << "type is :" << i->getType() << "\n";
                        auto* subIns = dyn_cast<Instruction>(i->getArgOperand(0));
                        if (&I == subIns) {
                          killSet.insert(i);
                        }
                      }
                    }
                  }
                  break;
          case 3:
          default: break;
        }
      }
      return std::make_pair(genSet, killSet);
    }

    void printSets(Function &F, std::vector<Instruction *> insV, std::vector<std::set<Instruction *>> sets1, std::vector<std::set<Instruction *>> sets2, std::string s1, std::string s2) {
      errs() << "START FUNCTION: " << F.getName() << '\n';
      for (int i = 0; i < insV.size(); i++) {
        Instruction* I = insV[i];
        errs() << "INSTRUCTION: " << *I << "\n";
        errs() << "***************** " << s1 << "\n{\n";
        for (auto it = sets1[i].begin(); it != sets1[i].end(); ++it) {
          errs() << " " << **it << "\n";
        }
        errs() << "}\n**************************************\n***************** " << s2 << "\n{\n";
        for (auto it = sets2[i].begin(); it != sets2[i].end(); ++it) {
          errs() << " " << **it << "\n";
        }
        errs() << "}\n**************************************\n\n\n\n";
      }
    }

    // deal phinode and nested phinode
    // return pair of flag and preValue
    // right now works, just do not do (nested) propagate inside this function
    std::pair<bool, int64_t> phiNodeHelper(PHINode* node) {
      bool flag = true;
      int64_t preValue = 0;
      for (int i = 0; i < node->getNumIncomingValues(); i++) {
        auto nodeValue = node->getIncomingValue(i);
        // escape if from argument
        if (isa<Argument>(nodeValue)) {
          flag = false;
          break;
        } else if (isa<PHINode>(nodeValue)) {
          // if a phinode inside a phinode
          auto boolIntPair = phiNodeHelper(cast<PHINode>(nodeValue));
          // if inside phinode cannot do constant propagation, this neighter
          if (!boolIntPair.first) {
            flag = false;
            break;
          } else {
            flag = true;
          }
          // if inside phinode value is not the same as preValue
          if (preValue != boolIntPair.second && i != 0) {
            flag = false;
            break;
          } else {
            preValue = boolIntPair.second;
          }
        } 
        else {
          auto nodeInst = dyn_cast<CallInst>(nodeValue);
          if (auto opValue = nodeInst->getArgOperand(0)) {
            if (auto constPtr = dyn_cast<ConstantInt>(opValue)) {
              if (i == 0) {
                preValue = constPtr->getSExtValue();
              } else {
                if (preValue != constPtr->getSExtValue()) {
                  flag = false;
                  break;
                }
              }
            }
          }
        }
      }
      return std::make_pair(flag, preValue);
    }

    bool runOnFunction (Function &F) override {
      //errs() << "Hello LLVM World at \"runOnFunction\"\n" ;
      bool modified = false;
      std::vector<Instruction *> insV;
      std::vector<std::set<Instruction *>> genSets;
      std::vector<std::set<Instruction *>> killSets;

      std::vector<std::set<Instruction *>> inSets;
      std::vector<std::set<Instruction *>> outSets;
      for (auto& B : F) {
        for (auto& I : B) {
          insV.push_back(&I);
          auto genKillPair = getGenKillPair(I);
          genSets.push_back(genKillPair.first);
          killSets.push_back(genKillPair.second);
          // initial outset for each instruction
          outSets.push_back(std::set<Instruction *>());
          inSets.push_back(std::set<Instruction *>());
        }
      }

      std::set<Instruction *> tempOutSet;
      bool change = true;
      while(change) {
        int insIndex = 0;
        change = false;
        for (auto& B : F) {
          int blkCount = 0;
          for (auto& I : B) {
            // inset
            // if it is the first instruction of all the program, no inset
            if (insIndex != 0) {
              // if it is the first instruction of a basic block,
              // the in set should be all predecesor block's last instruction
              if (blkCount == 0) {
                inSets[insIndex].clear();
                for (auto PI = pred_begin(&B), E = pred_end(&B); PI != E; ++PI) {
                  BasicBlock *Pred = *PI;
                  if (Pred != NULL) {
                    auto preIn = Pred->getTerminator();
                    if (preIn != NULL) {
                      int preinsIndex = std::find(insV.begin(), insV.end(), preIn) - insV.begin();
                      inSets[insIndex].insert(outSets[preinsIndex].begin(), outSets[preinsIndex].end());
                    }
                  }
                }
              } else {
                inSets[insIndex].clear();
                inSets[insIndex].insert(outSets[insIndex-1].begin(), outSets[insIndex-1].end());
              }
            }
            // outset
            tempOutSet.clear();
            tempOutSet.insert(genSets[insIndex].begin(), genSets[insIndex].end());
            std::set_difference(inSets[insIndex].begin(), inSets[insIndex].end(), killSets[insIndex].begin(), killSets[insIndex].end(), std::inserter(tempOutSet, tempOutSet.end()));
            if (tempOutSet != outSets[insIndex]) {
              change = true;
              outSets[insIndex].clear();
              outSets[insIndex].insert(tempOutSet.begin(), tempOutSet.end());
            }
            // index value
            blkCount++;
            insIndex++;
          }
        }
      }
      // constant propagation with data dependence
      // H4 starts here
      // modified to H6 version
      DependenceAnalysis &deps = getAnalysis<DependenceAnalysis>();
      std::set<Instruction*> escapeSet;
      for (int i = 0; i < insV.size(); i++) {
        // for every cat value get pointed, recognized as escaping
        if (isa<StoreInst>(insV[i])) {
          auto* ptrInst = cast<StoreInst>(insV[i]);
          if (auto* escapeInst = dyn_cast<Instruction>(ptrInst->getValueOperand())) {
            escapeSet.insert(escapeInst);
          }
        }
      }
      for(int i = 0; i < insV.size(); i++) {
        if (auto* call = dyn_cast<CallInst>(insV[i])) {
          Function* callee = call->getCalledFunction();
          // if from get_signed_value
          if (getCatType(callee) == 3) {
            Instruction* reachDef = NULL;
            auto* argValue = call->getArgOperand(0);
            // if not use value from function argument
            if (!isa<Argument>(argValue)) {
              // check phi node
              if (isa<PHINode>(argValue)) {
                auto* phiNode = cast<PHINode>(argValue);
                if (phiNodeHelper(phiNode).first) {
                  reachDef = cast<Instruction>(phiNode->getIncomingValue(0));
                }
              } else {
                if (Instruction* operandInst = dyn_cast<Instruction>(argValue)) {
                  // if not from mem
                  if (!isa<LoadInst>(operandInst)) {
                    auto operandCall = cast<CallInst>(operandInst);
                    // the operand of get value func should be create cat right now, if from argument, ignore
                    if(!isa<Argument>(operandCall->getArgOperand(0))) {
                      std::set<Instruction*> inSet = inSets[i];
                      for (auto* inInst : inSet) {
                        if (auto* subInst = dyn_cast<CallInst>(inInst)) {
                          if (inInst == operandInst) {
                            reachDef = subInst;
                          } else {
                            if (subInst->getArgOperand(0) == operandInst) {
                              reachDef = NULL;
                              break;
                            }
                            if (escapeSet.find(operandInst) != escapeSet.end()) {
                              // check depend on add or sub instruction in escape
                              if (getCatType(subInst->getCalledFunction()) <= 1) {
                                if (deps.depends(call, subInst, false)) {
                                  reachDef = NULL;
                                  break;
                                } else {
                                  reachDef = subInst;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }

            if (reachDef != NULL) {
              if (auto* reachCall = dyn_cast<CallInst>(reachDef)) {
                auto* value = reachCall->getArgOperand(0);
                if (isa<ConstantInt>(value)) {
                  ConstantInt *c = cast<ConstantInt>(value);
                  BasicBlock::iterator ii(insV[i]);
                  ReplaceInstWithValue(insV[i]->getParent()->getInstList(), ii, c);
                  modified = true;
                }
              }
            }
          }
        }
      }
      //printSets(F, insV, inSets, outSets, "IN", "OUT");
      insV.clear();
      genSets.clear();
      killSets.clear();
      inSets.clear();
      outSets.clear();
      return modified;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      //errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;
      //AU.setPreservesAll();
      AU.addRequiredTransitive<DependenceAnalysis>();
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
