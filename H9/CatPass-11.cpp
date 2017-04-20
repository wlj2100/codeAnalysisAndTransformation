#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include <iostream>
#include <map>
#include <vector>
#include <set>
#include "llvm/IR/BasicBlock.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SparseBitVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/Analysis/DependenceAnalysis.h"



using namespace llvm;

namespace {
  std::pair<bool,int64_t> getIntegerValue(Value* value, CallInst* callin);
  bool compare_result(int64_t predicate, int64_t first_integer,int64_t second_integer);
  bool ArgumentsToBePropagate(Module &M);
  bool PropagateConstantIntoArguments(Function &F, std::map<int,std::pair<bool,Value*>> const_value);
  // SUMMARY struct
  struct function_info {
    bool constant;
    std::map<bool,Value*> value;
    int64_t predicate;
    Value* firstWhat;
    Value* secondWhat;
  };
  struct CAT : public FunctionPass {
    static char ID; 
    std::map<Function*,function_info> summary;
    std::string cat_api[4] = {"CAT_binary_add", "CAT_binary_sub", "CAT_create_signed_value","CAT_get_signed_value"};
    std::set<Function*> function_with_cat;

    std::set<BasicBlock*> bbWorkList;
    std::set<Instruction*> instWorkList;
    CAT() : FunctionPass(ID) {}

    // get the summary of all functions, except main
    // set function_info.constant = true if the function returns a constant CAT_data
    // 1. the function returns a CAT_create_signed_value instruction
    // 2. the function returns a phinode that has only CAT_create_signed_value instruction as incoming values, store the conditions
    // 3. the function returns a function which is a constant function, update the conditions and store it in the new function summary
    bool doInitialization (Module &M) override {

      for(int i = 0; i < 4; i++){
        Function *CAT_function;
        CAT_function = M.getFunction(cat_api[i]);
        if(CAT_function == NULL){
          continue;
        }
        //errs() << "The users are: \n";
        for(auto& U: CAT_function->uses()){
          User* user = U.getUser();
          //errs() << *user << "\n";
          if(auto* i = dyn_cast<Instruction>(user)){
            instWorkList.insert(i);

            BasicBlock* bb = i->getParent();
            bbWorkList.insert(bb);

            Function* f = bb->getParent();
            function_with_cat.insert(f);
          }
        }
      }


      for (auto &F : M) {
        if (F.getName() != "main"){
          //errs() << F.getName() << "\n";
          if(F.isDeclaration()){
            summary[&F] = function_info();
            summary[&F].constant = false;
            continue;
          }
          // initialize objects in the summary map
          summary[&F] = function_info();
          summary[&F].constant = false;
          for (auto &bb : F){
            for (auto &i : bb){
              // look for the return value
              if(auto* ret = dyn_cast<ReturnInst>(&i)){
                Value* retOperand;
                if(ret->getNumOperands()>0){
                  retOperand = ret->getOperand(0);
                }
                else{
                  continue;
                }
                if(auto* call = dyn_cast<CallInst>(retOperand)){
                  // 1. the function returns a CAT_create_signed_value instruction
                  if(call->getCalledFunction()->getName() == cat_api[2]){
                    summary[&F].constant = true;
                    Value* v = call->getOperand(0);
                    summary[&F].value[true] = v;
                  }
                  else{
                    // 3. the function returns a function which is a constant function, update the conditions and store it in the new function summary
                    if(summary.find(call->getCalledFunction())!= summary.end() && summary[call->getCalledFunction()].constant){
                      function_info called_function_info = summary[call->getCalledFunction()];
                      std::pair<bool,int64_t> first_integer = getIntegerValue(called_function_info.firstWhat,call);
                      std::pair<bool,int64_t> second_integer = getIntegerValue(called_function_info.secondWhat,call);
                      if(!first_integer.first || !second_integer.first){
                        // the value is an argument
                        if(isa<ConstantInt>(call->getArgOperand(0))){
                          //errs() << "It is a constant\n";
                          summary[&F].constant = true;
                          summary[&F].firstWhat = call->getArgOperand(0);
                          summary[&F].secondWhat = called_function_info.secondWhat;
                          summary[&F].predicate = called_function_info.predicate;
                          summary[&F].value[true] = called_function_info.value[true];
                          summary[&F].value[false] = called_function_info.value[false];
                        }
                        else{
                          summary[&F].constant = false;
                          //errs() << "It is not a constant\n";
                        }
                      }

                    }
                  }
                }
                else if(auto* phi = dyn_cast<PHINode>(retOperand)){
                  // 2. the function returns a phinode that has only CAT_create_signed_value instruction as incoming values, store the conditions
                  std::vector<Value*> value;
                  bool allConst = true;
                  bool argInPhi = false;
                  // check that all incomming values are constant
                  for(int i = 0; i < phi->getNumIncomingValues(); i++){
                    if(!isa<CallInst>(phi->getIncomingValue(i))){
                      if(isa<Argument>(phi->getIncomingValue(i))){
                        allConst = false;
                        argInPhi = true;
                        Value* v = phi->getIncomingValue(i);
                        value.push_back(v);
                      }
                      else{
                        allConst = false;
                        break;
                      }
                    }
                    else{
                      if(cast<CallInst>(phi->getIncomingValue(i))->getCalledFunction()->getName() != cat_api[2]){
                        allConst = false;
                        break;
                      }
                      else{
                        Value* v = cast<CallInst>(phi->getIncomingValue(i))->getOperand(0);
                        value.push_back(v);
                      }
                    }
                  }
                  if(allConst){
                    summary[&F].constant = true;
                    summary[&F].value[true] = value[0];
                    summary[&F].value[false] = value[1];
                    Instruction* i = cast<Instruction>(phi->getIncomingValue(0));
                    auto* bb = i->getParent();
                    BasicBlock* bb_cmp = *(pred_begin(bb));
                    for(auto &i: *bb_cmp){
                      // find the "if" instruction condition
                      if(auto cmp_inst = dyn_cast<CmpInst>(&i)){
                        summary[&F].predicate = cmp_inst->getPredicate();
                        if(cmp_inst->getNumOperands() > 1){
                          summary[&F].firstWhat = cmp_inst->getOperand(0);
                          summary[&F].secondWhat = cmp_inst->getOperand(1);
                        }
                      }
                    }
                  }
                  else if(argInPhi){
                    // if there is an argument in the phinode check the value in runOnModule
                    summary[&F].constant = false;
                    summary[&F].value[true] = value[0];
                    summary[&F].value[false] = value[1];
                    Instruction* i;
                    if(isa<Argument>(value[0])){
                      i = cast<Instruction>(phi->getIncomingValue(1));
                    }
                    else if(isa<Argument>(value[1])){
                      i = cast<Instruction>(phi->getIncomingValue(0));
                    }
                    // else if(isa<Argument>(value[0]) && isa<Argument>(value[1])){
                    // }
                    auto* bb = i->getParent();
                    BasicBlock* bb_cmp = *(pred_begin(bb));
                    for(auto &i: *bb_cmp){
                      // find the "if" instruction condition
                      if(auto cmp_inst = dyn_cast<CmpInst>(&i)){
                        summary[&F].predicate = cmp_inst->getPredicate();
                        if(cmp_inst->getNumOperands() > 1){
                          summary[&F].firstWhat = cmp_inst->getOperand(0);
                          errs() << *(cmp_inst->getOperand(0)) << "\n";
                          summary[&F].secondWhat = cmp_inst->getOperand(1);
                        }
                      }
                    }

                  }
                  else{
                    // some incoming values are not constant
                    summary[&F].constant = false;
                  }
                }
                else{
                  // other return values
                  summary[&F].constant = false;
                }
              }
            }
          }           
        }
      }
      bool resultIPCP = ArgumentsToBePropagate(M);
      return false;
    }

    // -------------------------
    // some utility functions
    // --------------------------

    private: class GEN_KILL{
    private:
      std::vector<Instruction*> gen;
      std::vector<Instruction*> kill;
    public:
      GEN_KILL(){
      }
      void insert_gen(Instruction &i){
        gen.push_back(&i);
      }
      void insert_kill(Instruction &i){
        kill.push_back(&i);
      }
      std::vector<Instruction*> get_gen(){
        return gen;
      }
      std::vector<Instruction*> get_kill(){
         return kill;
      } 
    };

    std::pair<bool,int64_t> check_value(Value* value){
      if(isa<Argument>(value))
        return std::make_pair(false,0);
      auto instruction = dyn_cast<Instruction>(value);
      if(isa<LoadInst>(instruction))
        return std::make_pair(false,0);
      if(isa<PHINode>(value)){
        std::pair<bool,int64_t> phi_pair = check_phi(cast<PHINode>(value));
        if(phi_pair.first == false)
          return std::make_pair(false,0);
        else
          return phi_pair;
      }
      if(auto call = dyn_cast<CallInst>(instruction)){
        Value* v = call->getArgOperand(0);
        if(isa<ConstantInt>(v)){
          ConstantInt* ci = cast<ConstantInt>(v);
          int64_t real_value = ci->getSExtValue();
          return std::make_pair(true,real_value);
        }
      }
      return std::make_pair(false,0);
    }

    std::pair<bool,int64_t> check_phi(PHINode* node){
      int64_t final_value;
      for(int i = 0; i < node->getNumIncomingValues()-1; i++){
        Value* value_1 = node->getIncomingValue(i);
        Value* value_2 = node->getIncomingValue(i+1);
        std::pair<bool,int64_t> value_pair_1 = check_value(value_1);

        if(value_pair_1.first == false)
          return std::make_pair(false,0);

        std::pair<bool,int64_t> value_pair_2 = check_value(value_2);

        if(value_pair_2.first == false)
          return std::make_pair(false,0);
        else if(value_pair_1.second != value_pair_2.second)
          return std::make_pair(false,0);
        else{
          final_value = value_pair_1.second;
        }
      }
      return std::make_pair(true,final_value);
    }

    // Get integer value for function summary
    std::pair<bool,int64_t> getIntegerValue(Value* value, CallInst* callin){
      // The value is already a constant
      if(isa<ConstantInt>(value)){
        ConstantInt* constant = cast<ConstantInt>(value);
        return std::make_pair(true,constant->getSExtValue());
      }
      else if(isa<Argument>(value)){
        return std::make_pair(false,0);
      }
      else if(isa<CallInst>(value)){
        CallInst* value_instruction = cast<CallInst>(value);
        if(value_instruction->getCalledFunction()->getName() == cat_api[3]){
          value = value_instruction->getOperand(0);
          if(isa<Argument>(value)){
            // if the CAT_data comes from argument, get the value at runtime
            Value* runtime_value = callin->getArgOperand(0);
            if(CallInst* runtime_instruction = dyn_cast<CallInst>(runtime_value)){
              if(runtime_instruction->getCalledFunction()->getName() == cat_api[2]){
                runtime_value = runtime_instruction->getArgOperand(0);
                if(isa<ConstantInt>(runtime_value)){
                  ConstantInt* constant = cast<ConstantInt>(runtime_value);
                  return std::make_pair(true,constant->getSExtValue());
                }
              }
            }
          }
          else if(isa<CallInst>(value)){
            // if the CAT_data is created in the function
            Value* arg_create = cast<CallInst>(value)->getArgOperand(0);
            if(isa<ConstantInt>(arg_create)){
              ConstantInt* constant = cast<ConstantInt>(arg_create);
              return std::make_pair(true,constant->getSExtValue());
            }
          }
        }
      }
    }

    // Compare function for function summary
    bool compare_result(int64_t predicate, int64_t first_integer,int64_t second_integer){
      switch(predicate){
        case 32:
          if(first_integer == second_integer)
            return true;
          else
            return false;
          break;
        case 33:
          if(first_integer != second_integer)
            return true;
          else
            return false;
          break;
        case 34:
          if(first_integer > second_integer)
            return true;
          else
            return false;
          break;
        case 35:
          if(first_integer >= second_integer)
            return true;
          else
            return false;
          break;
        case 36:
          if(first_integer < second_integer)
            return true;
          else
            return false;
          break;
        case 37:
          if(first_integer <= second_integer)
            return true;
          else
            return false;
          break;
        case 38:
          if(first_integer > second_integer)
            return true;
          else
            return false;
          break;
        case 39:
          if(first_integer >= second_integer)
            return true;
          else
            return false;
          break;
        case 40:
          if(first_integer < second_integer)
            return true;
          else
            return false;
          break;
        case 41:
        if(first_integer <= second_integer)
            return true;
          else
            return false;
          break;
      }
      return false;
    }

    bool ArgumentsToBePropagate(Module &M){
      bool LocalChange = true;
      while (LocalChange) {
        LocalChange = false;
        for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I){
          if (!I->isDeclaration()) {
            if((*I).getName() != "main"){
              int count_user = 0;
              int count_arg = 0;
              SymbolTableList<Argument> &ALT = (*I).getArgumentList();
              for(auto &arg : ALT){
                count_arg++;
              }
              std::map<int,int64_t> first_arg_values;
              std::map<int,int64_t> arg_values;
              std::map<int,std::pair<bool,Value*>> value_propagate;
              bool all_calls_constant = false;

              for(int j = 0; j < count_arg; j++){
                first_arg_values[j] = NULL;
                value_propagate[j].first = false;
              }
              // For uses of a function, if it is a function call:
              // For all function calls, propagate constant value into argument only if all calls passes the same constant value into the function:
              for(auto& U: (*I).uses()){
                User* user = U.getUser();
                for(int j = 0; j < count_arg; j++){
                  arg_values[j] = NULL;
                }
                if(auto call_function = dyn_cast<CallInst>(user)){
                  // for each argument of this call
                  for(int j = 0 ; j < call_function->getNumArgOperands(); j++){
                    if(auto call = dyn_cast<CallInst>(call_function->getArgOperand(j))){
                      if(call->getCalledFunction()->getName() == cat_api[2]){
                        // get the argument that is propagate into the CAT function
                        Value* v = call->getOperand(0);
                        if(isa<ConstantInt>(v)){
                          int64_t tmp_value = (cast<ConstantInt>(v))->getSExtValue();
                          // if it is the first user
                          if(count_user == 0){
                            first_arg_values[j] = tmp_value;
                            value_propagate[j] = std::make_pair(true,v);
                          }
                          else
                            arg_values[j] = tmp_value;
                        }
                      }
                    }
                  }
                }
                // compare the values between each call of the function
                if(count_user != 0){
                  for(int c = 0; c < count_arg ; c++){
                    if(value_propagate[c].first == false)
                      continue;
                    else{
                      if(first_arg_values[c] != arg_values[c])
                        value_propagate[c].first = false;
                      else
                        continue;
                    }
                  }
                }
                count_user++;
              }
              LocalChange = PropagateConstantIntoArguments(*I,value_propagate);
            }
          }

        }
      }
      return true;
    }

    bool PropagateConstantIntoArguments(Function &F, std::map<int,std::pair<bool,Value*>> const_value){
      bool modified = false;
      std::vector<Instruction*> inst_vec;
      std::map<Value*,int> arg_map;

      for (auto &bb : F){
        for (auto &i : bb){
          inst_vec.push_back(&i);
        }
      }

      int count = 0;
      SymbolTableList<Argument> &ALT = F.getArgumentList();
      for(auto &arg : ALT){
        arg_map[&arg] = count;
        count++;
      }

      for (Instruction* i : inst_vec){
          if(auto* call = dyn_cast<CallInst>(i)){
            if(call->getCalledFunction()->getName() == cat_api[3]){
              Value* arg_to_be_replaced = call->getArgOperand(0);
              if(isa<Argument>(arg_to_be_replaced)){
                int index = arg_map[arg_to_be_replaced];
                if(const_value[index].first){
                  Value* replace = const_value[index].second;
                  if(isa<ConstantInt>(replace)){
                    // update info for function summary, if the get_signed_value will be replaced
                    for(auto& U: call->uses()){
                      User* user = U.getUser();
                      Instruction* inst = cast<Instruction>(user);
                      if(isa<CmpInst>(inst)){
                        Function* function = i->getParent()->getParent();
                        if(summary.find(function)!= summary.end()&& summary[function].constant == false){
                          summary[function].constant = true;
                          if(i == summary[function].firstWhat){
                            summary[function].firstWhat = replace; 
                          }
                          else if(i == summary[function].secondWhat){
                            summary[function].secondWhat = replace;
                          }
                        }                      
                      }
                    }
                    // propagate the constant value
                    ConstantInt* ci = cast<ConstantInt>(replace);
                    BasicBlock *bb = i->getParent();
                    BasicBlock::iterator ii(i);
                    ReplaceInstWithValue(bb->getInstList(),ii,replace);
                    modified = true;
                  }
                }
              }
            }
          }
          else if(isa<ReturnInst>(i)){
            // if the function returns an argument, and the argument is constant
            if(i->getNumOperands() > 0){
              if(isa<Argument>(i->getOperand(0))){
                int index = arg_map[i->getOperand(0)];
                if(const_value[index].first){
                  Function* function = i->getParent()->getParent();
                  if(summary.find(function)!= summary.end()){
                    // update the summary of the called function
                    function_info current_f_info = summary[function];
                    summary[function].constant = true;
                    summary[function].value[true] = const_value[index].second;
                  }
                }                
              }
              else if(isa<PHINode>(i->getOperand(0))){
                // if the function may return an argument and the argument is constant
                for(int j = 0; j < cast<PHINode>(i->getOperand(0))->getNumIncomingValues() ; j++){
                  if(isa<Argument>(cast<PHINode>(i->getOperand(0))->getIncomingValue(j))){
                    Argument* a = cast<Argument>(cast<PHINode>(i->getOperand(0))->getIncomingValue(j));
                    int index = arg_map[a];
                    if(const_value[index].first){
                      Function* function = i->getParent()->getParent();
                      if(summary.find(function)!= summary.end()){
                        // update the summary of the called function
                        function_info current_f_info = summary[function];
                        summary[function].constant = true;
                        if(summary[function].value[true] == a){
                          summary[function].value[true] = const_value[index].second;
                        }
                        else
                          summary[function].value[false] = const_value[index].second;
                      }

                    }                   
                  }
                }

              }
            }
          }
      }
      return modified;
    }

    bool runOnFunction (Function &F) override{
      bool modified = false;
      std::set<Function*>::iterator it = function_with_cat.find(&F);
      if(it == function_with_cat.end()){
        return false;
      }
      
      std::map<Instruction*, GEN_KILL> map;
      std::vector<Instruction*> inst_set;

      // GEN and KILL
      for (auto &bb : F){
        for (auto &i : bb){
          map[&i] = GEN_KILL();
          inst_set.push_back(&i);
          if (auto* call = dyn_cast<CallInst>(&i))
          {
            // store GEN set
            if(call->getCalledFunction()->getName() == cat_api[0]||call->getCalledFunction()->getName() == cat_api[1]||call->getCalledFunction()->getName() == cat_api[2])
            {
              std::map<Instruction*, GEN_KILL>::iterator it = map.find(call);
              if(it != map.end()){
                it->second.insert_gen(*call);
              }
            }

            // store KILL set
            if(call->getCalledFunction()->getName() == cat_api[0]||call->getCalledFunction()->getName() == cat_api[1])
            {
              if(auto* inst = dyn_cast<Instruction>(call->getArgOperand(0)))
              {
                // insert arg(0) to current instruction: KILL set
                std::map<Instruction*, GEN_KILL>::iterator it_1 = map.find(call);  
                if(it_1 != map.end())
                  it_1->second.insert_kill(*inst);
                
                std::map<Instruction*, GEN_KILL>::iterator it_2 = map.find(inst);
                if(it_2 != map.end())
                {
                  // find arg(0) instruction, add current instruction to arg(0): KILL set
                  it_2->second.insert_kill(*call);

                  // add arg(0) KILL set to current inst: KILL set, add current inst to arg(0): KILL set instruction
                  std::vector<Instruction *> kill_set_of_arg = it_2->second.get_kill();
                  for(auto it = kill_set_of_arg.begin();it!=kill_set_of_arg.end();it++){
                    if(*it!=&i)
                    {
                      std::map<Instruction*, GEN_KILL>::iterator find_the_killed = map.find(*it);
                      if(find_the_killed!=map.end())
                      {
                      find_the_killed->second.insert_kill(*call);
                      it_1->second.insert_kill(*(find_the_killed->first));
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }

      // IN and OUT
      std::vector<std::set<Instruction*>> in_set;
      std::vector<std::set<Instruction*>> out_set;
      std::map<Instruction*, int> inst_map;

      // initialize in and out sets
      for(int count = 0; count < inst_set.size() ; count++){
        in_set.push_back(std::set<Instruction*>());
        std::set<Instruction*> gen_set;
        for(auto* i: map[inst_set[count]].get_gen())
          gen_set.insert(i);
        out_set.push_back(gen_set);
        inst_map[inst_set[count]] = count;
      }
      
      //bool out_change = true;

      std::vector<BasicBlock*> bb_worklist;

      for(auto &bb : F){
        bb_worklist.push_back(&bb);
      }
      bool firstTime = true;
      while (bb_worklist.size() !=0 ){
        BasicBlock* bb = bb_worklist.front();
        bb_worklist.erase(bb_worklist.begin());
        bool out_change = false;
        
        int num_inst = 0;
        if (!firstTime) {
          if (bbWorkList.find(bb) != bbWorkList.end()) {
            continue;
          }
        }
        for(auto &i: *bb)
        {
          if (!firstTime) {
            if (instWorkList.find(&i) != instWorkList.end()) {
             continue;
            }
          }
          //get index of a instruction
          int num = inst_map[&i];
          // for first instruction in block
          if( num_inst == 0 )
          {
            std::vector<Instruction*> inst_pre;
            // get predecessors of each block
            for(auto it = pred_begin(bb),et = pred_end(bb);it != et; ++it ){
              BasicBlock *predecessor = *it;
              inst_pre.push_back(&(*predecessor->getTerminator()));
            }
            // union predecessor
            for(auto* pre: inst_pre){
              //auto position = find(inst_set.begin(),inst_set.end(),pre)-inst_set.begin();
              int position = inst_map[pre];
              in_set[num].insert(out_set[position].begin(),out_set[position].end());            
            }
          }
          // for other instruction
          else{
            in_set[num] = out_set[num-1];
          }
          // OUT set
          std::set<Instruction*> tmp_out;
          GEN_KILL gen_kill = map[&i];
          std::set_difference(in_set[num].begin(),in_set[num].end(),
                              gen_kill.get_kill().begin(),gen_kill.get_kill().end(),
                              std::inserter(tmp_out,tmp_out.end()));
          for(auto gen : gen_kill.get_gen()){
            tmp_out.insert(gen);
          }
          // check if out_set changed
          if(tmp_out != out_set[num]){
            out_set[num] = tmp_out; 
            out_change = true;
          }             
          num_inst++;
        } 

        if(out_change){
          bb_worklist.push_back(bb);
        }
        firstTime = false;
      }


      DependenceAnalysis &deps = getAnalysis<DependenceAnalysis>();
      // Reaching definition and constant propagation (without assumption)
      std::set<Instruction*> escape_var;
      for(Instruction* i : inst_set){
        // Mark excaped variables
        if(isa<StoreInst>(i)){
          StoreInst* si = cast<StoreInst>(i);
          if(auto escape = dyn_cast<CallInst>(si->getValueOperand())){
            escape_var.insert(escape);
          }
        }
        if(isa<CallInst>(i)){
          CallInst* ci = cast<CallInst>(i);
          if(ci->getNumArgOperands()>0){
            if(ci->getCalledFunction()->getName() != cat_api[3] && ci->getCalledFunction()->getName() != cat_api[0] && ci->getCalledFunction()->getName() != cat_api[1]){
              if(isa<CallInst>(ci->getArgOperand(0))){
                CallInst* esc = cast<CallInst>(ci->getArgOperand(0));
                if(esc->getCalledFunction()->getName() == cat_api[2]){
                  escape_var.insert(esc);
                }
              }
            }
          }
        }
      }

      for(Instruction* i : inst_set){
        if(auto* call = dyn_cast<CallInst>(i)){
          Function* callee = call->getCalledFunction();
          // Instruction i is a use of a variable
          if(callee->getName() == cat_api[3]){
            auto num = find(inst_set.begin(),inst_set.end(),call)-inst_set.begin();
            bool const_reach = false;
            Value* arg_of_use = call->getOperand(0);
            // If variable is coming from an argument, do not propagate
            if(isa<Argument>(arg_of_use)){
              const_reach = false;
            }
            // If variable is coming from phi node
            if(isa<PHINode>(arg_of_use)){
              PHINode* node = cast<PHINode>(arg_of_use);
              std::pair<bool,int64_t> check = check_phi(node);
              if(check.first == false){
                const_reach = false;
              }
              else{
                // if the phi node depends on other add/sub instruction in the IN set
                bool escape_and_change = false;
                for(auto* inst: in_set[num]){
                  auto* inst_call = dyn_cast<CallInst>(inst);
                  if(inst_call->getCalledFunction()->getName() == cat_api[0]||inst_call->getCalledFunction()->getName() == cat_api[1]){
                    if(deps.depends(call,inst_call,false)){
                      escape_and_change = true;
                      break;
                    }
                  }
                }
                if(!escape_and_change){
                  int64_t real_value = check.second;
                  Type* call_type = call->getType();
                  Value* value = ConstantInt::get(call_type,real_value,false);
                  BasicBlock *bb = i->getParent();
                  BasicBlock::iterator ii(i);
                  ReplaceInstWithValue(bb->getInstList(),ii, value);
                  modified = true;
                }
              }
            }
            if(isa<Instruction>(arg_of_use)){
              Instruction* def = cast<Instruction>(arg_of_use);
              // If the definition comes from memory, be conservative and do not propagate
              if(isa<LoadInst>(def)){
                continue;
              }

              CallInst* callin = cast<CallInst>(def);
              // if a variable is defined by a constant function
              if(summary.find(callin->getCalledFunction())!= summary.end() && summary[callin->getCalledFunction()].constant){
                // get the summary of the called function
                function_info current_f_info = summary[callin->getCalledFunction()];
                Value* value;
                // the function returned a constant, store the value to be propagate
                if(current_f_info.value.size() == 1){
                  //errs() << *current_f_info.value[true] << "\n";
                  value = current_f_info.value[true];
                }
                else{
                  // the function returned a comparing result
                  Value* first_value = current_f_info.firstWhat;
                  Value* second_value = current_f_info.secondWhat;
                  int64_t predicate = current_f_info.predicate;
                  
                  std::pair<bool,int64_t> first_integer = getIntegerValue(first_value, callin);
                  std::pair<bool,int64_t> second_integer = getIntegerValue(second_value, callin);

                  // Get the return value according to the comparing result from summary
                  if(first_integer.first && second_integer.first){
                    bool result = compare_result(predicate,first_integer.second,second_integer.second);
                    value = current_f_info.value[result];
                  }  
                }
                // propagate if the value is a constant
                if(isa<ConstantInt>(value)){
                  //errs() << "is a constant\n";
                  BasicBlock *bb = i->getParent();
                  BasicBlock::iterator ii(i);
                  ReplaceInstWithValue(bb->getInstList(),ii,value);
                  modified = true;
                }
                // go to next iteration
                continue;
              }


              for(auto* inst: in_set[num]){
                if(inst == def){
                  const_reach = true;
                }
                else{
                  auto* inst_call = dyn_cast<CallInst>(inst);
                  if(inst_call->getArgOperand(0) == def){
                    const_reach = false;
                    break;
                  }
                  else if(escape_var.find(def)!=escape_var.end()){
                    // if the the original variable already escaped, and is changed in between 
                    if(inst_call->getCalledFunction()->getName() == cat_api[0]||inst_call->getCalledFunction()->getName() == cat_api[1]){                    
                      if(deps.depends(call,inst_call,false)){
                        const_reach = false;
                        break;
                      }
                      else{
                        const_reach = true;
                      }
                    }
                  }
                }  
              }

              if(const_reach){
                Value* value = cast<CallInst>(def)->getArgOperand(0);
                if(isa<ConstantInt>(value)){
                  BasicBlock *bb = i->getParent();
                  BasicBlock::iterator ii(i);
                  ReplaceInstWithValue(bb->getInstList(),ii,value);
                  modified = true;
                }
              }
            }   
          }
        }
      }
      //errs() << F << "\n";
      map.clear();
      inst_map.clear();
      in_set.clear();
      out_set.clear();
      inst_set.clear();
      return modified;
    }


    void getAnalysisUsage(AnalysisUsage &AU) const override {
      //errs() << "CATPass: getAnalysisUsage\n";
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
