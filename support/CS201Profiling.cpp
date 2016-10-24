#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Instructions.h"
#include <vector>
#include <map>
#include <algorithm>
#include <utility>
#include <string>

using namespace llvm;

namespace {
    // https://github.com/thomaslee/llvm-demo/blob/master/main.cc
    static Function* printf_prototype(LLVMContext& ctx, Module *mod) {
        std::vector<Type*> printf_arg_types;
        printf_arg_types.push_back(Type::getInt8PtrTy(ctx));

        FunctionType* printf_type = FunctionType::get(Type::getInt32Ty(ctx), printf_arg_types, true);
        Function *func = mod->getFunction("printf");
        if(!func)
            func = Function::Create(printf_type, Function::ExternalLinkage, Twine("printf"), mod);
        func->setCallingConv(CallingConv::C);
        return func;
    }

    struct CS201Profiling : public FunctionPass {
        static char ID;
        LLVMContext *Context;
        CS201Profiling() : FunctionPass(ID) {}
        std::map<StringRef, GlobalVariable*> bbCounters;
        GlobalVariable *BasicBlockPrintfFormatStr = NULL;
        Function *printf_func = NULL;
        std::vector<std::vector<BasicBlock*>> domSet;
        std::map<StringRef, std::vector<BasicBlock*>> backEdges;
        std::map<StringRef, std::vector<std::vector<BasicBlock*>>> loops;
        std::map<StringRef, GlobalVariable*> edgeCounters;
        std::map<StringRef, std::map<StringRef, GlobalVariable*>> _BBCOUNTERS;
        std::map<StringRef, std::map<StringRef, std::vector<std::vector<BasicBlock*>>>> _LOOPS;
        std::map<StringRef, std::map<StringRef, GlobalVariable*>> _EDGECOUNTERS;
        //----------------------------------
        bool doInitialization(Module &M) {
            errs() << "\n---------Starting Path Profiling---------\n";
            Context = &M.getContext();
            const char *finalPrintString = "%s: %d\n";
            Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
            BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");

            printf_func = printf_prototype(*Context, &M);

            errs() << "Module: " << M.getName() << "\n";

            return true;
        }

        //----------------------------------
        bool doFinalization(Module &M) {
            errs() << "-------Finished Path Profiling----------\n\n";

            return true;
        }

        //----------------------------------
        bool runOnFunction(Function &F) override {
            errs() << "Function: " << F.getName() << '\n';
            auto it = F.begin();
            unsigned func_size = F.size();
            std::vector<BasicBlock*> bbDomSet;
            for (auto &BB: F) {
                BB.setName("b");
                // set the start node dominator set to itself
                if (BB.getName().equals("b")) {
                    bbDomSet.push_back(&BB);
                    domSet.push_back(bbDomSet);
                }
                else {
                    bbDomSet.push_back(&BB);
                }
            }

            // set the other nodes dominator sets to all nodes in the CFG

            for (auto &BB: F) {
                if (BB.getName().equals("b")) {
                    BB.setName("b0");
                    continue;
                }
                domSet.push_back(bbDomSet);
            }

            for (auto &BB: F) {
                GlobalVariable *bbCounter = new GlobalVariable(*BB.getParent()->getParent(), Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
                bbCounters[BB.getName()] = bbCounter;
                // Add the footer to Main's BB containing the return 0; statement BEFORE calling runOnBasicBlock
                if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())) { // major hack?
                    addFinalPrintf(BB, Context, bbCounters, BasicBlockPrintfFormatStr, printf_func);
                }
                runOnBasicBlock(BB);
            }

            // Add edge block and set the counter for each edge
            for (unsigned i = 0; i < func_size; ++i) {
                initEdges(it);
                it++;
            }

            errs() << "Dominator Sets:\n";
            for (unsigned i = 0; i < domSet.size(); ++i) {
                errs() << "DomSet[b" << i << "] => ";
                for (unsigned j = 0; j < domSet.at(i).size(); ++j) {
                    errs() << domSet.at(i).at(j)->getName();
                    if (j < domSet.at(i).size()-1) {
                        errs() << ", ";
                    }
                }
                errs() << '\n';
            }

/*
            errs() << "Back edegs:\n";
            for (auto it = backEdges.begin(); it != backEdges.end(); ++it) {
                if (!it->second.empty()) {
                    for (unsigned i = 0; i < it->second.size(); ++i) {
                        errs() << it->first << "-->" << it->second.at(i)->getName() << '\n';
                    }
                }
            }
*/
            if (!loops.empty()) {
                errs() << "Loops:\n";

            }
            for (auto it = loops.begin(); it != loops.end(); ++it) {
                if (!it->second.empty()) {
                    for (unsigned i = 0; i < it->second.size(); ++i) {
                        for (unsigned j = 0; j < it->second.at(i).size(); ++j) {
                            errs() << it->second.at(i).at(j)->getName() << ' ';
                        }
                        errs() << '\n';
                    }
                }
            }

            _BBCOUNTERS[F.getName()] = bbCounters;
            _LOOPS[F.getName()] = loops;
            _EDGECOUNTERS[F.getName()] = edgeCounters;

            domSet.clear();
            backEdges.clear();
            loops.clear();
            bbCounters.clear();
            edgeCounters.clear();

            return true; // since runOnBasicBlock has modified the program
        }

        //----------------------------------
        bool runOnBasicBlock(BasicBlock &BB) {
            // find dominator set
            findDomSet(BB);
            // find back edges
            findBackEdges(BB);
            // find loops
            findLoops(BB);

            // Load BasicBlock counter
            IRBuilder<> IRB(BB.getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction
            Value *loadAddr = IRB.CreateLoad(bbCounters[BB.getName()]);
            Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
            IRB.CreateStore(addAddr, bbCounters[BB.getName()]);
/*
            // Load Edge counter
            // Value *curr = IRB.CreateGlobalString(BB.getName(), "curr");
            Constant *formatCurr = ConstantDataArray::getString(*Context, BB.getName());
            GlobalVariable *currBB = new GlobalVariable(*BB.getParent()->getParent(), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), BB.getName().size()+1), true, llvm::GlobalValue::PrivateLinkage, formatCurr, "currBB");

            if (lastBB == NULL) {
                lastBB = new GlobalVariable(*BB.getParent()->getParent(), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), BB.getName().size()+1), true, llvm::GlobalValue::PrivateLinkage, formatCurr, "lastBB");
                errs() << "BasicBlock: " << BB << '\n';
                return true;
            }

            // Insert load lastbb instruction
            LoadInst *last = IRB.CreateLoad(lastBB);

            IRB.CreateStore(last, lastBB);

            errs() << "access 174\n";
//            StringRef *lastB = dyn_cast<StringRef>(formatCurr);
//            errs() << *lastB << '\n';
            std::pair<Constant*, Constant*> edge = std::make_pair(lastBB->getInitializer(), currBB->getInitializer());

//            GlobalVariable *edgeCounter = new GlobalVariable(*BB.getParent()->getParent(), Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "edgeCounter");
//            edgeCounters[edge] = edgeCounter;
            Value *loadEdgeAddr = IRB.CreateLoad(edgeCounters[edge]);

            errs() << "access 178\n";
            Value *addEdgeAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadEdgeAddr);
            IRB.CreateStore(addEdgeAddr, edgeCounters[edge]);

            // store currBB to lastBB
            Value *curr = IRB.CreateLoad(currBB);
//            Value *loadCurr = IRB.CreateLoad(curr);
            IRB.CreateStore(curr, lastBB);
*/
            errs() << "BasicBlock: " << BB << '\n';

            return true;
        }

        unsigned BBNum(const StringRef &bname) {
            StringRef location = bname.substr(1);
            unsigned bnum;
            location.getAsInteger(0, bnum);
            return bnum;
        }


        // find BB's dominator set by intersect BB predecessors' dominator sets
        void findDomSet(BasicBlock &BB) {
            std::vector<BasicBlock*> bbDomSet;

            if (BB.getName().equals("b0")) {
                return;
            }
            else {
                std::vector<unsigned> preds;
                for (auto it = pred_begin(&BB), et = pred_end(&BB); it != et; ++it) {
                    BasicBlock *pred = *it;
                    unsigned index = BBNum(pred->getName());
                    //errs() << BB.getName() <<  " pred: " << index << '\n';
                    preds.push_back(index);
                }

                intersact(domSet, preds, bbDomSet);
                // each node dominate itself
                bbDomSet.push_back(&BB);
                unsigned bnum = BBNum(BB.getName());
                domSet.at(bnum) = bbDomSet;
            }
        }

        void intersact(std::vector<std::vector<BasicBlock*>> &sets, std::vector<unsigned> &index, std::vector<BasicBlock*> &result) {
            if (result.empty()) {
                result = sets.at(index.at(0));
                index.erase(index.begin());
            }
            if (index.empty()) {
                return;
            }
            std::vector<BasicBlock*> set = sets.at(index.at(0));
            index.erase(index.begin());
            std::vector<BasicBlock*> inter;
            unsigned i = 0;
            unsigned j = 0;
            while (i < result.size() && j < set.size()) {
                // get each node's number
                unsigned rnum = BBNum(result.at(i)->getName());
                unsigned snum = BBNum(set.at(j)->getName());
                //errs() << rnum << " " << snum << '\n';
                if (rnum < snum) {
                    ++i;
                }
                else if (rnum > snum) {
                    ++j;
                }
                else {
                    inter.push_back(result.at(i));
                    ++i;
                    ++j;
                }
            }

            result.clear();
            result = inter;

            intersact(sets, index, result);
        }

        void findBackEdges(BasicBlock &BB) {
            std::vector<BasicBlock*> backNodes;
            // if BB's successor is in its dominator set, then it is a back edge
            for (auto it = succ_begin(&BB), et = succ_end(&BB); it != et; ++it) {
                BasicBlock *succ = *it;
                std::vector<BasicBlock*> bbdom = domSet.at(BBNum(BB.getName()));
                if (std::find(bbdom.begin(), bbdom.end(), succ) != bbdom.end()) {
                    backNodes.push_back(succ);
                }
            }
            backEdges[BB.getName()] = backNodes;
        }

        static bool compBB(BasicBlock* B1, BasicBlock* B2) {
            return B1->getName() < B2->getName();
        }

        void findLoops(BasicBlock &BB) {
            std::vector<BasicBlock*> loopNodes;
            std::vector<BasicBlock*> stack;
            std::vector<BasicBlock*> backNodes = backEdges[BB.getName()];
            for (unsigned i = 0; i < backNodes.size(); ++i) {
                loopNodes.clear();
                stack.clear();
                loopNodes.push_back(backNodes[i]);
                Insert(&BB, stack, loopNodes);
                while (!stack.empty()) {
                    BasicBlock* m = stack.back();
                    stack.pop_back();
                    for (auto it = pred_begin(m), et = pred_end(m); it != et; ++it) {
                        BasicBlock *pred = *it;
                        Insert(pred, stack, loopNodes);
                    }
                }

                std::sort(loopNodes.begin(), loopNodes.end(), compBB);
                // push loopNodes to loops (a node may have many set of loops)
                loops[BB.getName()].push_back(loopNodes);
            }
        }

        void Insert(BasicBlock *BB, std::vector<BasicBlock*> &stack, std::vector<BasicBlock*> &loopNodes) {
            if (std::find(loopNodes.begin(), loopNodes.end(), BB) == loopNodes.end()) {
                loopNodes.push_back(BB);
                stack.push_back(BB);
            }
            return;
        }

        void initEdges(BasicBlock *BB) {
            // insert a basicblock in each edge
            TerminatorInst *term = BB->getTerminator();
            unsigned n = term->getNumSuccessors();
            // set BB's successor to the newly created block edgeBB and edgeBB's successor to succ
            for (unsigned i = 0; i < n; ++i) {
                BasicBlock *succ = term->getSuccessor(i);
                std::string edgeStr = BB->getName().str() + " -> " + succ->getName().str();
                StringRef edgeName = StringRef(edgeStr);

                //errs() << "edge: " << edgeName << '\n';
                BasicBlock *edgeBB = BasicBlock::Create(*Context, edgeName, BB->getParent());
                term->setSuccessor(i, edgeBB);
                BranchInst::Create(succ, edgeBB);

                runOnEdges(*edgeBB);
                // find each edge
/*                Constant *formatCurr = ConstantDataArray::getString(*Context, BB->getName());
                Constant *formatPred = ConstantDataArray::getString(*Context, pred->getName());
                std::pair<Constant*, Constant*> edge = std::make_pair(formatPred, formatCurr);

                GlobalVariable *edgeCounter = new GlobalVariable(*BB->getParent()->getParent(), Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "edgeCounter");
                edgeCounters[edge] = edgeCounter;
  */
            }
        }

        void runOnEdges(BasicBlock &BB) {
            GlobalVariable *edgeCounter = new GlobalVariable(*BB.getParent()->getParent(), Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "edgeCounter");
            edgeCounters[BB.getName()] = edgeCounter;
            errs() << "BasicBlock: " << BB.getName() << '\n';
            IRBuilder<> IRB(BB.getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction

            Value *loadAddr = IRB.CreateLoad(edgeCounters[BB.getName()]);
            Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
            IRB.CreateStore(addAddr, edgeCounters[BB.getName()]);
            errs() << BB << '\n';
            return;
        }

        //----------------------------------
        // Rest of this code is needed to: printf("%d\n", bbCounter); to the end of main, just BEFORE the return statement
        // For this, prepare the SCCGraph, and append to last BB?
        void addFinalPrintf(BasicBlock& BB, LLVMContext *Context, std::map<StringRef, GlobalVariable*> bbCounters, GlobalVariable *var, Function *printf_func) {
            IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
            std::vector<Constant*> indices;
            Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
            indices.push_back(zero);
            indices.push_back(zero);
            //indices.push_back(zero);
            Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);

            /************************Basic Block Profiling*****************************/
            const char* Bprofile = "BASIC BLOCK PROFILING:\n";
            Constant *Bstr = ConstantDataArray::getString(*Context, Bprofile);
            GlobalVariable *bbTitle = new GlobalVariable(*BB.getParent()->getParent(), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(Bprofile)+1), true, llvm::GlobalValue::PrivateLinkage, Bstr, "bbTitle");
            Constant *BBProfile = ConstantExpr::getGetElementPtr(bbTitle, indices);
            CallInst *call0 = builder.CreateCall(printf_func, BBProfile);
            call0->setTailCall(false);
            for (auto i = _BBCOUNTERS.begin(); i != _BBCOUNTERS.end(); ++i) {
                for (auto it = i->second.begin(); it != i->second.end(); ++it) {
                    Value *bbc = builder.CreateLoad(it->second);
                    Constant *bbName = ConstantDataArray::getString(*Context, it->first);
                    GlobalVariable *bname = new GlobalVariable(*BB.getParent()->getParent(), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), it->first.size()+1), true, llvm::GlobalValue::PrivateLinkage, bbName, "bname");
                    CallInst *call1 = builder.CreateCall(printf_func, {var_ref, bname, bbc});
                    call1->setTailCall(false);
                }
            }

            /****************************Edge Profiling*******************************/
            const char* edgeProfile = "\nEDGE PROFILING:\n";
            Constant *Estr = ConstantDataArray::getString(*Context, edgeProfile);
            GlobalVariable *edgeTitle = new GlobalVariable(*BB.getParent()->getParent(), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(edgeProfile)+1), true, llvm::GlobalValue::PrivateLinkage, Estr, "edgeTitle");
            Constant *eProfile = ConstantExpr::getGetElementPtr(edgeTitle, indices);
            CallInst *call2 = builder.CreateCall(printf_func, eProfile);
            call2->setTailCall(false);

            const char *edgePrintStr = "%s: %d\n";
            Constant *eStr = ConstantDataArray::getString(*Context, edgePrintStr);
            GlobalVariable *edgeFormatStr = new GlobalVariable(*BB.getParent()->getParent(), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(edgePrintStr)+1), true, llvm::GlobalValue::PrivateLinkage, eStr, "edgeFormatStr");
            Constant *edgePrint = ConstantExpr::getGetElementPtr(edgeFormatStr, indices);
            for (auto i = _EDGECOUNTERS.begin(); i != _EDGECOUNTERS.end(); ++i) {
                for (auto it = i->second.begin(); it != i->second.end(); ++it) {
                    Value *edge = builder.CreateLoad(it->second);
                    Constant *edgeName = ConstantDataArray::getString(*Context, it->first);
                    GlobalVariable *eName = new GlobalVariable(*BB.getParent()->getParent(), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), it->first.size()+1), true, llvm::GlobalValue::PrivateLinkage, edgeName, "eName");
                    CallInst *call3 = builder.CreateCall(printf_func, {edgePrint, eName, edge});
                    call3->setTailCall(false);
                }
            }

            /********************************Loop Profiling****************************/
            const char* loopProfile = "\nLOOP PROFILING:\n";
            Constant *Lstr = ConstantDataArray::getString(*Context, loopProfile);
            GlobalVariable *loopTitle = new GlobalVariable(*BB.getParent()->getParent(), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(loopProfile)+1), true, llvm::GlobalValue::PrivateLinkage, Lstr, "loopTitle");
            Constant *lProfile = ConstantExpr::getGetElementPtr(loopTitle, indices);
            CallInst *call4 = builder.CreateCall(printf_func, lProfile);
            call4->setTailCall(false);

            const char *loopPrintStr = "%s: %d\n";
            Constant *lStr = ConstantDataArray::getString(*Context, loopPrintStr);
            GlobalVariable *loopFormatStr = new GlobalVariable(*BB.getParent()->getParent(), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(loopPrintStr)+1), true, llvm::GlobalValue::PrivateLinkage, lStr, "edgeFormatStr");
            Constant *loopPrint = ConstantExpr::getGetElementPtr(loopFormatStr, indices);
            for (auto i = _LOOPS.begin(); i != _LOOPS.end(); ++i) {
                for (auto it = i->second.begin(); it != i->second.end(); ++it) {
                    if (!it->second.empty()) {
                        for (unsigned i = 0; i < it->second.size(); ++i) {
                            std::string loopStr;
                            std::string backStr;
                            for (unsigned j = 0; j < it->second.at(i).size(); ++j) {
                                loopStr += it->second.at(i).at(j)->getName();
                                if (j != it->second.at(i).size()-1) {
                                    loopStr += " ";
                                }
                            }
                            backStr = it->second.at(i).back()->getName().str() + " -> " + it->second.at(i).front()->getName().str();
                            StringRef backedge = StringRef(backStr);
                            StringRef loopN = StringRef(loopStr);
                            StringRef funcN = it->second.at(i).back()->getParent()->getName();
                            Value *loopCounter = builder.CreateLoad(_EDGECOUNTERS[funcN][backedge]);
                            Constant *loopName = ConstantDataArray::getString(*Context, loopN);
                            GlobalVariable *lName = new GlobalVariable(*BB.getParent()->getParent(), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), loopN.size()+1), true, llvm::GlobalValue::PrivateLinkage, loopName, "lName");
                            CallInst *call5 = builder.CreateCall(printf_func, {loopPrint, lName, loopCounter});
                            call5->setTailCall(false);
                        }
                    }
                }
            }
        }
    };
}

char CS201Profiling::ID = 0;
static RegisterPass<CS201Profiling> X("pathProfiling", "CS201Profiling Pass", false, false);

