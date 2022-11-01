//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <iostream>
#include <vector>
#include <string>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/IntrinsicsRISCV.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/ValueSymbolTable.h"





using namespace llvm;

#define DEBUG_TYPE "hello"

STATISTIC(HelloCounter, "Counts number of functions greeted");

void packer_rvv(BasicBlock *);


namespace {
  // Hello - The first implementation, without getAnalysisUsage.
  struct Hi : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    Hi() : FunctionPass(ID) {}
    
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesCFG();
      AU.addRequired<LoopInfoWrapperPass>();
    }

    bool runOnFunction(Function &F) override {    
      uint32_t trip_count = 0;
      Module *M = F.getParent();
      LLVMContext &context = F.getContext();
      Type *sizeT = Type::getInt32Ty(context);
      ScalableVectorType *sv32T = ScalableVectorType::get(sizeT , 16);
      IntegerType *i1 = IntegerType::get(context , 1);
      Value *local_id = M->getOrInsertGlobal("local_id" , sizeT);
      Value *vl = M->getOrInsertGlobal("vl" , sizeT);
      // Value *local_id_v = M->getOrInsertGlobal("local_id_v" , sv32T);
      //function initilization

      std::vector<Type *> args;
      args.push_back(sizeT);
      ArrayRef<Type *> args_ref(args);

      Function *f1 = Intrinsic::getDeclaration(M , Intrinsic::riscv_vsetvli , args_ref);

      if(F.getName() == "workitemLoop"){
        LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
        // F.getBasicBlockList().begin();
        for(Loop *L: LI){
          errs() << *L << "\n";
          // step1 . 
          for(BasicBlock *BB : L->getBlocks()){
            
            IRBuilder<> builder(&*(BB->getFirstInsertionPt()));
            StringRef BBname = BB->getName();
            // errs() << "Basic Block : " << "\n";
            // errs() << BBname << "\n";
            
            if(BBname == "for.cond"){
              for(Instruction &Ins : *BB){
                if(Ins.getOpcode() == Instruction::ICmp){
                  trip_count = dyn_cast<ConstantInt>(Ins.getOperand(1))->getZExtValue();
                  // errs() << "trip count : " << trip_count << "\n";
                }
              }
            }else if(BBname == "for.inc"){
              // local_id = local_id + vl;
              Value *t1 = builder.CreateLoad(sizeT , vl , "t1");
              Value *t2 = builder.CreateLoad(sizeT , local_id , "t2");
              Value *t3 = builder.CreateAdd(t2 , t1 , "t3" , 0 , 0 );
              Value *t4 = builder.CreateStore(t3 , local_id , 0);
            }else if(BBname == "for.body"){
              // vl = vsetvli(trip_count - local_id + 1);
              Value *s1 = builder.CreateLoad(sizeT , local_id , "s1");
              Value *s2 = builder.CreateSub(ConstantInt::get(sizeT, trip_count) , s1 , "s2" , 0 , 0);
              Value *s3 = builder.CreateAdd(s2 , ConstantInt::get(sizeT, 1) , "s3" , 0 , 0);
              std::vector<Value *> args2;
              args2.push_back(s3);
              args2.push_back(ConstantInt::get(sizeT, 2));
              args2.push_back(ConstantInt::get(sizeT, 3));
              ArrayRef<Value *> args2_ref(args2);
              Value *s4 = builder.CreateCall(f1 , args2_ref);
              Value *s5 = builder.CreateStore(s4 , vl , 0);
              
              /* ?
                mask classes and name : 

                Entry mask : m_{block name}
                Exit mask : m_{block name}_{successor block name}
              
                Entry masks : 
                
                %m_a = alloca i1*, align 8
                // %m_b_a , %m_c_a, %m_d_a
                %1 = load i1, i1* %m_b_a;
                %2 = load i1, i1* %m_c_a;
                %3 = load i1, i1* %m_d_a;
                %4 = or i1 %1, %2
                %5 = or i1 %4, %3
                store i1 %5, i1* %m_a

                // store i1 [xxx], i1* %m
              
                Exit masks : 

                // br i1 %c, label %b, label %c

                %m_a_b = alloca il*, align 8
                %m_a_c = alloca i1*, align 8
                %1 = load i1, i1* %m
                %2 = and i1 %1, %c
                store i1 %2, i1* %m_a_b
                %3 = not i1 %c
                %4 = and i1 %1 , %2
                store i1 %3, i1* %m_a_c

                // br label %d

                %m_a_b = alloca i1*, align 8
                %1 = load i1, i1* %m
                store i1 %1, i1* %m_a_b

              */

              //entry mask generation
              Value *entry_mask = builder.CreateAlloca(Type::getInt1Ty(context), nullptr , "m_" + BBname);

              //exit masks generation
              Instruction *terminator = BB->getTerminator();
              if(terminator->getOpcode() == Instruction::Br || terminator->getOpcode() == Instruction::IndirectBr){
                BranchInst *br = dyn_cast<BranchInst>(terminator);
                builder.SetInsertPoint(terminator);
                if(br->isConditional()){

                  Value *condition = br->getCondition();
                  StringRef ctrue = br->getOperand(1)->getName();
                  StringRef cfalse = br->getOperand(2)->getName();
                  // Value *mture = builder.CreateAlloca(Type::getInt1Ty(context) , nullptr , "m_" + BBname + "_" + ctrue);
                  // Value *mfalse = builder.CreateAlloca(Type::getInt1Ty(context) , nullptr , "m_" + BBname + "_" + cfalse);
                  Twine mture_name =  "m_" + BBname + "_" + ctrue;
                  Twine mfalse_name = "m_" + BBname + "_" + cfalse;
                  Value *mture = M->getOrInsertGlobal(mture_name.str() , Type::getInt1Ty(context));
                  Value *mfalse = M->getOrInsertGlobal(mfalse_name.str() , Type::getInt1Ty(context));
                  Value *t1 = builder.CreateLoad(Type::getInt1Ty(context) , entry_mask);
                  Value *t2 = builder.CreateAnd(t1 , condition);
                  builder.CreateStore(t2 , mture);
                  Value *t3 = builder.CreateNot(condition);
                  Value *t4 = builder.CreateAnd(t1 , t3);
                  builder.CreateStore(t4 , mfalse);
                  
                }else{

                  StringRef cg = br->getOperand(0)->getName();
                  Value *mg = builder.CreateAlloca(Type::getInt1Ty(context) , nullptr , "m_" + BBname + "_" + cg);
                  Value *t1 = builder.CreateLoad(Type::getInt1Ty(context) , entry_mask);
                  builder.CreateStore(t1 , mg);

                }
              }
              
            }else{
              
              
              //entry mask generation
              Value *entry_mask = builder.CreateAlloca(Type::getInt1Ty(context), nullptr , "m_" + BBname);

              //exit masks generation
              Instruction *terminator = BB->getTerminator();
              if(terminator->getOpcode() == Instruction::Br || terminator->getOpcode() == Instruction::IndirectBr){
                BranchInst *br = dyn_cast<BranchInst>(terminator);
                builder.SetInsertPoint(terminator);
                if(br->isConditional()){

                  Value *condition = br->getCondition();
                  StringRef ctrue = br->getOperand(1)->getName();
                  StringRef cfalse = br->getOperand(2)->getName();
                  // Value *mture = builder.CreateAlloca(Type::getInt1Ty(context) , nullptr , "m_" + BBname + "_" + ctrue);
                  // Value *mfalse = builder.CreateAlloca(Type::getInt1Ty(context) , nullptr , "m_" + BBname + "_" + cfalse);
                  Twine mture_name =  "m_" + BBname + "_" + ctrue;
                  Twine mfalse_name = "m_" + BBname + "_" + cfalse;
                  Value *mture = M->getOrInsertGlobal(mture_name.str() , Type::getInt1Ty(context));
                  Value *mfalse = M->getOrInsertGlobal(mfalse_name.str() , Type::getInt1Ty(context));
                  Value *t1 = builder.CreateLoad(Type::getInt1Ty(context) , entry_mask);
                  Value *t2 = builder.CreateAnd(t1 , condition);
                  builder.CreateStore(t2 , mture);
                  Value *t3 = builder.CreateNot(condition);
                  Value *t4 = builder.CreateAnd(t1 , t3);
                  builder.CreateStore(t4 , mfalse);
                  
                }else{

                  StringRef cg = br->getOperand(0)->getName();
                  Twine mg_name =  "m_" + BBname + "_" + cg;
                  Value *mg = M->getOrInsertGlobal(mg_name.str() , Type::getInt1Ty(context));;
                  Value *t1 = builder.CreateLoad(Type::getInt1Ty(context) , entry_mask);
                  builder.CreateStore(t1 , mg);

                }
              }

            }
          }
          
          // step2
          /*
            %m_a = alloca i1*, align 8
            //%m_b_a , %m_c_a, %m_d_a
            %1 = load i1, i1* %m_b_a;
            %2 = load i1, i1* %m_c_a;
            %3 = load i1, i1* %m_d_a;
            %4 = or i1 %1, %2
            %5 = or i1 %4, %3
            store i1 %5, i1* %m_a
        */

          ValueSymbolTable *vst  = F.getValueSymbolTable();
        
          for(BasicBlock *BB : L->getBlocks()){
            
            IRBuilder<> builder(&*(BB->getFirstInsertionPt()));
            StringRef BBname = BB->getName();
            
            if(BBname == "for.cond"){
              ;
            }else if(BBname == "for.inc"){
              ;
            }else if(BBname == "for.body"){
              Twine mname = "m_" + BBname;
              Value *mask = vst->lookup(mname.str());
              uint32_t cnt = 0;
              Value *cur, *last , *sym;
              builder.SetInsertPoint(dyn_cast<Instruction>(mask)->getNextNode());
              for(BasicBlock *pred : predecessors(BB)){
                  Twine mname = "m_" + pred->getName() + "_" + BBname;
                  errs() << "test:" << mname.str() << "\n";
                  Value *sym = M->getOrInsertGlobal(mname.str() , Type::getInt1Ty(context));
                  cur = builder.CreateLoad(Type::getInt1Ty(context) , sym);
                  if(cnt > 0){
                    cur = builder.CreateOr(cur , last);
                  }
                  last = cur; //last == cur == %1 
                  cnt++;
              }
              builder.CreateStore(cur , mask);
            }else{

              Twine mname = "m_" + BBname;
              Value *mask = vst->lookup(mname.str());
              uint32_t cnt = 0;
              Value *cur, *last , *sym;
              builder.SetInsertPoint(dyn_cast<Instruction>(mask)->getNextNode());
              for(BasicBlock *pred : predecessors(BB)){
                  Twine mname = "m_" + pred->getName() + "_" + BBname;
                  errs() << "test:" << mname.str() << "\n";
                  Value *sym = M->getOrInsertGlobal(mname.str() , Type::getInt1Ty(context));
                  cur = builder.CreateLoad(Type::getInt1Ty(context) , sym);
                  if(cnt > 0){
                    cur = builder.CreateOr(cur , last);
                  }
                  last = cur; //last == cur == %1 
                  cnt++;
              }
              builder.CreateStore(cur , mask);
            }
          }
        }
      }
      M->dump(); 
    
      return false;
    }
  };
}

char Hi::ID = 0;
static RegisterPass<Hi> X("hi", "Hello World Pass");

namespace {
  // Hello2 - The second implementation with getAnalysisUsage implemented.
  struct Hello2 : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    Hello2() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
      ++HelloCounter;
      errs() << "Hello: ";
      errs().write_escaped(F.getName()) << '\n';
      return false;
    }

    // We don't modify the program, so we preserve all analyses.
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
    }
  };
}

char Hello2::ID = 0;
static RegisterPass<Hello2>
Y("hello2", "Hello World Pass (with getAnalysisUsage implemented)");

void packer_rvv(BasicBlock *BB){

  for(Instruction &ins : *BB){
    if(ins.getOpcode() == Instruction::Call){
      errs() << ins << "\n";
    }
  }

}