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
#include <map>

using namespace llvm;
using namespace std;

namespace {
  struct funcSum {
    // store the comparasion inst
    std::vector<Value*> cmpV;
    // store the create cat inst
    std::vector<Value*> catV;
  };

  struct CAT : public FunctionPass {
    static char ID;
    std::map<Function*,funcSum> sumMap;
    CAT() : FunctionPass(ID) {}

    // 
    std::pair<bool, std::vector<Value*>> funcPhiNodeHelper(PHINode* node) {
      bool flag = true;
      std::vector<Value*> v;
      Instruction* fromInst;
      for (int i = 0; i < node->getNumIncomingValues(); i++) {
        auto nodeValue = node->getIncomingValue(i);
        // if is from branch of create cat
        if (auto callInst = dyn_cast<CallInst>(nodeValue)) {
          if (getCatType(callInst->getCalledFunction()) == 2) {
            v.push_back(callInst->getOperand(0));
            continue;
          }
        }
        flag = false;
        break;
      }
      return std::make_pair(flag, v);
    }
    // This function is invoked once at the initialization phase of the compiler    
    bool doInitialization (Module &M) override {
      //errs() << "CATPass: doInitialization for \"" << M.getName() <<"\"\n";
      for (auto &F : M) {
        if (F.getName() != "main" && !F.isDeclaration()){
          for (auto &B : F){
            for (auto &I : B){
              if(auto* retnInst = dyn_cast<ReturnInst>(&I)){
                // if return nothing, do nothing
                if(retnInst->getNumOperands()!= 1){
                  continue;
                }
                // otherwise, chech the return operand
                // dont know which type will get
                auto* retnOperand = retnInst->getOperand(0);
                // if is return operand is a call of a function
                if(auto* callInst = dyn_cast<CallInst>(retnOperand)){
                  if(getCatType(callInst->getCalledFunction()) == 2){
                    // if return create cat, thus this function return a constant
                    sumMap[&F] = funcSum();
                    auto* catInst = callInst->getOperand(0);
                    sumMap[&F].catV.push_back(catInst);
                  } 
                  continue;
                } 
                if(auto* phiNode = dyn_cast<PHINode>(retnOperand)) {
                  // if is return operand is a phinode
                  std::pair<bool, std::vector<Value*>> temp = funcPhiNodeHelper(phiNode);

                  // if function can be summarized
                  if(temp.first) {
                    sumMap[&F] = funcSum();
                    sumMap[&F].catV = temp.second;
                    // do function summary (simple version): only deal one condition 
                    auto* phiInst = cast<Instruction>(phiNode->getIncomingValue(0));
                    auto* phiBlock = phiInst->getParent();
                    auto* prePhiBlock = *(pred_begin(phiBlock));
                    for (auto &inst : *prePhiBlock) {
                      if (auto cmpInst = dyn_cast<CmpInst>(&inst)) {
                        sumMap[&F].cmpV.push_back(cmpInst);
                      }
                    }
                  }
                } 
              }
            }
          }          
        }
      }
      findSameArg(M);
      return true;
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
      Instruction* fromInst;
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

    // <result> = icmp <cond> <ty> <op1>, <op2>   ; yields i1 or <N x i1>:result
    // simple version for one compare
      // dont understand why icmp has a cond with two operand
      // just fix with a num
    // int getValueHelper(funcSum summary, CallInst* callInst) {

    //   return 0;
    // }

    Value* getValue(funcSum summary, CallInst* callInst) {
      // if (summary.cmpV.size() != 0) {
      //   return summary.catV[getValueHelper(summary, callInst)];
      // }
      return summary.catV[0];
    }

    bool findSameArg(Module &M) {
      bool changed = true;
      bool flag = false;
      while (changed) {
        changed = false;
        flag = false;
        Value* opValue;
        CallInst* callInst;
        for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) {
          if (!F->isDeclaration() && F->getName() != "main") {
            int argValue;
            int userCount = 0;
            for (auto& U : F->uses()) {
              User* user = U.getUser();
              if (auto funcCall = dyn_cast<CallInst>(user)) {
                if (funcCall->getNumArgOperands() > 0) {
                  if (callInst = dyn_cast<CallInst>(funcCall->getArgOperand(0))) {
                    if (getCatType(callInst->getCalledFunction()) == 2) {
                      opValue = callInst->getOperand(0);
                      if (auto intValue = dyn_cast<ConstantInt>(opValue)) {
                        if (userCount == 0) {
                          argValue == intValue->getSExtValue();
                        } else {
                          if (argValue != intValue->getSExtValue()) {
                            flag = true;
                            break;
                          } 
                        }
                      }
                    }
                  }
                }
              }
              userCount++;
            }
            if (flag) {
              continue;
            }
            changed = doPropagate(*F, opValue, callInst);
          }
        }
      }
      return !flag;
    }

    bool doPropagate(Function &F, Value* argValue, Value* callInst) {
      bool modified = false;
      std::vector<Instruction*> instVec;
      for (auto& B : F) {
        for (auto& I : B) {
          instVec.push_back(&I);
        }
      }
      for (auto* inst : instVec) {
        if (auto* callInst = dyn_cast<CallInst>(inst)) {
          if (getCatType(callInst->getCalledFunction()) == 3) {
            if (isa<Argument>(callInst->getArgOperand(0))) {
              auto* b = inst->getParent();
              BasicBlock::iterator ii(inst);
              ReplaceInstWithValue(b->getInstList(), ii, argValue);
              modified = true;
            }
          }
        }
        if (isa<ReturnInst>(inst)) {
          if (inst->getNumOperands() > 0 && isa<Argument>(inst->getOperand(0))) {
            auto* func = inst->getParent()->getParent();
            if (sumMap.find(func) != sumMap.end() ) {
              sumMap[func].catV[0] =  callInst;
            }
          }
        }
      }
      return modified;
    }

    bool runOnFunction (Function &F) override {
      //errs() << "Hello LLVM World at \"runOnFunction\"\n" ;
      bool modified = false;
      if (F.isDeclaration()) {
        return modified;
      }
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
      // modified to H7 version
      DependenceAnalysis &deps = getAnalysis<DependenceAnalysis>();
      std::set<Instruction*> escapeSet;
      std::set<Instruction*> escapeSetSpecific;
      for (int i = 0; i < insV.size(); i++) {
        // for every cat value get pointed, recognized as escaping
        if (isa<StoreInst>(insV[i])) {
          auto* ptrInst = cast<StoreInst>(insV[i]);
          if (auto* escapeInst = dyn_cast<Instruction>(ptrInst->getValueOperand())) {
            escapeSet.insert(escapeInst);
          }
        }
        if (auto* tempInst= dyn_cast<CallInst>(insV[i])) {
          if (tempInst->getNumArgOperands() > 0) {
            if (getCatType(tempInst->getCalledFunction()) == -1) {
              if (auto* escapeInst = dyn_cast<CallInst>(tempInst->getArgOperand(0))) {
                if (getCatType(escapeInst->getCalledFunction()) == 2) {
                  escapeSet.insert(escapeInst);
                }
              }
              for (int j = 0; j < tempInst->getNumArgOperands(); j++) {
                if (auto* escapeInst = dyn_cast<CallInst>(tempInst->getArgOperand(j))) {
                  if (getCatType(escapeInst->getCalledFunction()) == 2) {
                    escapeSetSpecific.insert(escapeInst);
                    // errs()<< *escapeInst <<  "\n";
                  }
                }
              }
            }
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
                  if (sumMap.find(operandCall->getCalledFunction()) != sumMap.end()) {
                    funcSum summary = sumMap[operandCall->getCalledFunction()];
                    auto* funcValue = getValue(summary, operandCall); 
                    if (summary.cmpV.size()==0 && isa<ConstantInt>(funcValue)) {
                      // errs() << summary.cmpV.size() << "\n";
                      BasicBlock::iterator ii(insV[i]);
                      ReplaceInstWithValue(insV[i]->getParent()->getInstList(),ii,funcValue);
                      modified = true;
                      continue;
                    }
                  }
                  std::set<Instruction*> inSet = inSets[i];
                  for (auto* inInst : inSet) {
                    if (auto* subInst = dyn_cast<CallInst>(inInst)) {
                      if (inInst == operandInst) {
                        if (escapeSetSpecific.find(operandInst) != escapeSetSpecific.end()) {
                          // errs()<<*operandInst << "\n";
                          reachDef = NULL;
                          break;
                        }
                        reachDef = subInst;
                      } else {
                        if (subInst->getNumOperands() > 0 && subInst->getArgOperand(0) == operandInst) {
                          reachDef = NULL;
                          break;
                        }

                        if (escapeSet.find(operandInst) != escapeSet.end()) {
                              //check depend on add or sub instruction in escape

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
      // errs() << "Function \"" << F.getName() << "\"\n";
      // F.dump();
      return modified;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      //errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;
      // AU.setPreservesAll();
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
