//===-- TxTreeGraph.cpp - Tracer-X tree DOT graph ---------------*- C++ -*-===//
//
//               The Tracer-X KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file contains the implementation of the Tracer-X tree DOT graph, useful
/// for viewing and debugging.
///
//===----------------------------------------------------------------------===//

#include "klee/util/TxTreeGraph.h"

#include "klee/ExecutionState.h"
#include "klee/util/TxPrintUtil.h"
#include "TxTree.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#else
#include "llvm/BasicBlock.h"
#include "llvm/Function.h"
#endif

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 5)
#include <llvm/IR/DebugInfo.h>
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
#include <llvm/DebugInfo.h>
#else
#include <llvm/Analysis/DebugInfo.h>
#endif
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include <fstream>
#include <string>

using namespace klee;

/**/

std::string TxTreeGraph::NumberedEdge::render() const {
  std::ostringstream stream;
  stream << "Node" << source->nodeSequenceNumber << " -> Node"
         << destination->nodeSequenceNumber << " [style=dashed,label=\""
         << number << "\"];";
  return stream.str();
}

/**/

uint64_t TxTreeGraph::nodeCount = 1;

TxTreeGraph *TxTreeGraph::instance = 0;

std::string TxTreeGraph::recurseRender(TxTreeGraph::Node *node) {
  std::ostringstream stream;

  if (node->nodeSequenceNumber) {
    stream << "Node" << node->nodeSequenceNumber;
  } else {
    // Node sequence number is zero; this must be an internal node created due
    // to splitting in memory access
    if (!node->internalNodeId) {
      node->internalNodeId = (++internalNodeId);
    }
    stream << "InternalNode" << node->internalNodeId;
  }
  std::string sourceNodeName = stream.str();

  size_t pos = 0;
  std::string replacementName(node->name);
  std::stringstream repStream1;
  while ((pos = replacementName.find("{")) != std::string::npos) {
    if (pos != std::string::npos) {
      repStream1 << replacementName.substr(0, pos) << "\\{";
      replacementName = replacementName.substr(pos + 2);
    }
  }
  repStream1 << replacementName;
  replacementName = repStream1.str();
  std::stringstream repStream2;
  while ((pos = replacementName.find("}")) != std::string::npos) {
    if (pos != std::string::npos) {
      repStream2 << replacementName.substr(0, pos) << "\\}";
      replacementName = replacementName.substr(pos + 2);
    }
  }
  repStream2 << replacementName;
  replacementName = repStream2.str();

  stream << " [shape=record,";
  if (node->errorPath) {
    stream << "style=bold,";
  }
  stream << "label=\"{";
  if (node->nodeSequenceNumber) {
    stream << node->nodeSequenceNumber << ": " << replacementName;
  } else {
    // The internal node id must have been set earlier
    assert(node->internalNodeId && "id for internal node must have been set");
    if (node->falseTarget || node->trueTarget) {
      stream << "Internal node " << node->internalNodeId << ": ";
    } else {
      stream << "Unvisited node: ";
    }
  }
  stream << "\\l";
  for (std::map<TxPCConstraint *, std::pair<std::string, bool> >::const_iterator
           it = node->pathConditionTable.begin(),
           ie = node->pathConditionTable.end();
       it != ie; ++it) {
    stream << it->second.first;
    if (it->second.second)
      stream << " ITP";
    stream << "\\l";
  }
  if (node->markCount) {
    stream << "mark(s): " << node->markCount;
    if (node->markAddition) {
      stream << " (+" << node->markAddition << ")";
    }
    stream << "\\l";
  }
  switch (node->errorType) {
  case ASSERTION: {
    stream << "ASSERTION FAIL: " << node->errorLocation << "\\l";
    break;
  }
  case MEMORY: {
    stream << "OUT-OF-BOUND: " << node->errorLocation << "\\l";
    break;
  }
  case GENERIC: {
    stream << "GENERIC FAIL: " << node->errorLocation << "\\l";
    break;
  }
  case NONE:
  default: { break; }
  }
  if (node->subsumed) {
    stream << "(subsumed)\\l";
  } else {
    std::map<TxTreeGraph::Node *, uint64_t>::iterator it =
        leafToLeafSequenceNumber.find(node);
    if (it != leafToLeafSequenceNumber.end()) {
      // This node is a leaf
      stream << "(terminal #" << it->second << ")\\l";
    }
  }
  if (node->falseTarget || node->trueTarget)
    stream << "|{<s0>F|<s1>T}";
  stream << "}\"];\n";

  if (node->falseTarget) {
    if (node->falseTarget->nodeSequenceNumber) {
      stream << sourceNodeName << ":s0 -> Node"
             << node->falseTarget->nodeSequenceNumber;
    } else {
      if (!node->falseTarget->internalNodeId) {
        node->falseTarget->internalNodeId = (++internalNodeId);
      }
      stream << sourceNodeName << ":s0 -> InternalNode"
             << node->falseTarget->internalNodeId;
    }
    if (node->falseTarget->errorPath) {
      stream << " [style=bold,label=\"ERR\"];\n";
    } else {
      stream << ";\n";
    }
  }
  if (node->trueTarget) {
    if (node->trueTarget->nodeSequenceNumber) {
      stream << sourceNodeName + ":s1 -> Node"
             << node->trueTarget->nodeSequenceNumber;
    } else {
      if (!node->trueTarget->internalNodeId) {
        node->trueTarget->internalNodeId = (++internalNodeId);
      }
      stream << sourceNodeName << ":s1 -> InternalNode"
             << node->trueTarget->internalNodeId;
    }
    if (node->trueTarget->errorPath) {
      stream << " [style=bold,label=\"ERR\"];\n";
    } else {
      stream << ";\n";
    }
  }
  if (node->falseTarget) {
    stream << recurseRender(node->falseTarget);
  }
  if (node->trueTarget) {
    stream << recurseRender(node->trueTarget);
  }
  return stream.str();
}

std::string TxTreeGraph::render() {
  std::string res("");

  // Simply return empty string when root is undefined
  if (!root)
    return res;

  std::ostringstream stream;
  for (std::vector<TxTreeGraph::NumberedEdge *>::iterator
           it = subsumptionEdges.begin(),
           ie = subsumptionEdges.end();
       it != ie; ++it) {
    stream << (*it)->render() << "\n";
  }

  // Compute leaf indices (TxTreeGraph::leafToNumber)
  std::map<uint64_t, TxTreeGraph::Node *> sequenceNumberToNode;
  std::vector<uint64_t> leafSequenceNumbers;
  for (std::set<TxTreeGraph::Node *>::iterator it = leaves.begin(),
                                               ie = leaves.end();
       it != ie; ++it) {
    // We skip internal nodes with zero sequence number
    if ((*it)->nodeSequenceNumber) {
      uint64_t nodeSequenceNumber = (*it)->nodeSequenceNumber;
      sequenceNumberToNode[nodeSequenceNumber] = *it;
      leafSequenceNumbers.push_back(nodeSequenceNumber);
    }
  }
  std::sort(leafSequenceNumbers.begin(), leafSequenceNumbers.end());
  leafToLeafSequenceNumber.clear();
  uint64_t leafId = 0;
  for (std::vector<uint64_t>::iterator it = leafSequenceNumbers.begin(),
                                       ie = leafSequenceNumbers.end();
       it != ie; ++it) {
    TxTreeGraph::Node *node = sequenceNumberToNode[*it];
    leafToLeafSequenceNumber[node] = ++leafId;
  }

  res = "digraph search_tree {\n";
  res += recurseRender(root);
  res += stream.str();
  res += "}\n";
  return res;
}

TxTreeGraph::TxTreeGraph(TxTreeNode *_root)
    : subsumptionEdgeNumber(0), internalNodeId(0) {
  root = TxTreeGraph::Node::createNode(0);
  txTreeNodeMap[_root] = root;
  leaves.insert(root);
}

TxTreeGraph::~TxTreeGraph() {
  if (root)
    delete root;

  txTreeNodeMap.clear();

  for (std::vector<TxTreeGraph::NumberedEdge *>::iterator
           it = subsumptionEdges.begin(),
           ie = subsumptionEdges.end();
       it != ie; ++it) {
    delete *it;
  }
  subsumptionEdges.clear();

  leaves.clear();

  leafToLeafSequenceNumber.clear();
}

void TxTreeGraph::addChildren(TxTreeNode *parent, TxTreeNode *falseChild,
                              TxTreeNode *trueChild) {
  nodeCount += 2;

  if (!OUTPUT_INTERPOLATION_TREE)
    return;

  assert(TxTreeGraph::instance && "Search tree graph not initialized");

  TxTreeGraph::Node *parentNode = instance->txTreeNodeMap[parent];

  parentNode->falseTarget =
      TxTreeGraph::Node::createNode(parentNode->markCount);
  parentNode->falseTarget->parent = parentNode;
  parentNode->trueTarget = TxTreeGraph::Node::createNode(parentNode->markCount);
  parentNode->trueTarget->parent = parentNode;
  instance->txTreeNodeMap[falseChild] = parentNode->falseTarget;
  instance->txTreeNodeMap[trueChild] = parentNode->trueTarget;

  instance->leaves.erase(parentNode);
  instance->leaves.insert(parentNode->falseTarget);
  instance->leaves.insert(parentNode->trueTarget);
}

void TxTreeGraph::setCurrentNode(ExecutionState &state,
                                 const uint64_t _nodeSequenceNumber) {
  if (!OUTPUT_INTERPOLATION_TREE)
    return;

  assert(TxTreeGraph::instance && "Search tree graph not initialized");

  TxTreeNode *txTreeNode = state.txTreeNode;
  TxTreeGraph::Node *node = instance->txTreeNodeMap[txTreeNode];
  if (!node->nodeSequenceNumber) {
    std::string functionName(
        state.pc->inst->getParent()->getParent()->getName().str());
    node->name = functionName + "\\l";
    llvm::raw_string_ostream out(node->name);
    if (llvm::MDNode *n = state.pc->inst->getMetadata("dbg")) {
      // Display the line, char position of this instruction
      llvm::DILocation loc(n);
      unsigned line = loc.getLineNumber();
      llvm::StringRef file = loc.getFilename();
      out << file << ":" << line << "\n";
    } else {
      state.pc->inst->print(out);
    }
    node->name = out.str();
    node->nodeSequenceNumber = _nodeSequenceNumber;
  }

  // Increase the mark addition count when there is a return from a function
  // named tracerx_mark.
  if (llvm::ReturnInst *ri = llvm::dyn_cast<llvm::ReturnInst>(state.pc->inst)) {
    if (ri->getParent()) {
      if (llvm::Function *f = ri->getParent()->getParent()) {
        if (f->getName().str() == "tracerx_mark") {
          (node->markCount)++;
          (node->markAddition)++;
        }
      }
    }
  }
}

void TxTreeGraph::markAsSubsumed(TxTreeNode *txTreeNode,
                                 TxSubsumptionTableEntry *entry) {
  if (!OUTPUT_INTERPOLATION_TREE)
    return;

  assert(TxTreeGraph::instance && "Search tree graph not initialized");

  TxTreeGraph::Node *node = instance->txTreeNodeMap[txTreeNode];
  node->subsumed = true;
  TxTreeGraph::Node *subsuming = instance->tableEntryMap[entry];
  instance->subsumptionEdges.push_back(new TxTreeGraph::NumberedEdge(
      node, subsuming, ++(instance->subsumptionEdgeNumber)));
}

void TxTreeGraph::addPathCondition(TxTreeNode *txTreeNode,
                                   TxPCConstraint *pathCondition,
                                   ref<Expr> condition) {
  if (!OUTPUT_INTERPOLATION_TREE)
    return;

  assert(TxTreeGraph::instance && "Search tree graph not initialized");

  TxTreeGraph::Node *node = instance->txTreeNodeMap[txTreeNode];

  std::string s = TxPrettyExpressionBuilder::construct(condition);

  std::pair<std::string, bool> p(s, false);
  node->pathConditionTable[pathCondition] = p;
  instance->pathConditionMap[pathCondition] = node;
}

void TxTreeGraph::addTableEntryMapping(TxTreeNode *txTreeNode,
                                       TxSubsumptionTableEntry *entry) {
  if (!OUTPUT_INTERPOLATION_TREE)
    return;

  assert(TxTreeGraph::instance && "Search tree graph not initialized");

  TxTreeGraph::Node *node = instance->txTreeNodeMap[txTreeNode];
  instance->tableEntryMap[entry] = node;
}

void TxTreeGraph::setAsCore(TxPCConstraint *pathCondition) {
  if (!OUTPUT_INTERPOLATION_TREE)
    return;

  assert(TxTreeGraph::instance && "Search tree graph not initialized");

  instance->pathConditionMap[pathCondition]
      ->pathConditionTable[pathCondition]
      .second = true;
}

void TxTreeGraph::setError(const ExecutionState &state,
                           TxTreeGraph::Error errorType) {
  if (!OUTPUT_INTERPOLATION_TREE)
    return;

  TxTreeGraph::Node *node = instance->txTreeNodeMap[state.txTreeNode];
  node->errorType = errorType;

  node->errorLocation = "";
  llvm::raw_string_ostream out(node->errorLocation);
  if (llvm::MDNode *n = state.pc->inst->getMetadata("dbg")) {
    // Display the line, char position of this instruction
    llvm::DILocation loc(n);
    unsigned line = loc.getLineNumber();
    llvm::StringRef file = loc.getFilename();
    out << file << ":" << line << "\n";
  } else {
    state.pc->inst->print(out);
  }

  // Mark the path as leading to memory error
  while (node) {
    node->errorPath = true;
    node = node->parent;
  }
}

void TxTreeGraph::save(std::string dotFileName) {
  if (!OUTPUT_INTERPOLATION_TREE)
    return;

  assert(TxTreeGraph::instance && "Search tree graph not initialized");

  std::string g(instance->render());
  std::ofstream out(dotFileName.c_str());
  if (!out.fail()) {
    out << g;
    out.close();
  }
}

void TxTreeGraph::copyTxTreeNodeData(TxTreeNode *txTreeNode) {
  instance->txTreeNodeMap[txTreeNode]->executedBBs = txTreeNode->executedBBs;
  // printing the three
  //  llvm::errs() << "Node sequence = " << txTreeNode->getNodeSequenceNumber()
  //               << "\n";
  //  for (unsigned i = 0; i < txTreeNode->executedBBs.size(); ++i) {
  //    txTreeNode->executedBBs[i]->dump();
  //  }
  //  llvm::errs() << "==============\n\n";
}

void TxTreeGraph::generatePSSCFG1(KModule *kmodule) {
  if (instance->root == NULL) {
    return;
  }

  std::set<llvm::BasicBlock *> visitedBBs;
  std::set<llvm::Instruction *> executedInsts;
  llvm::ValueToValueMapTy vmap;
  std::vector<Node *> wl;
  wl.push_back(instance->root);
  while (!wl.empty()) {
    Node *t = wl.back();
    if (!t->isProcessed) {
      // mark & process
      t->isProcessed = true;
      for (unsigned i = 0; i < t->executedBBs.size(); ++i) {
        llvm::BasicBlock *bb = t->executedBBs[i];
        // create a new BB if existed
        bool isExisted = visitedBBs.find(bb) != visitedBBs.end();
        if (isExisted) {
          // duplicate basic block
          llvm::ValueToValueMapTy bvmap;
          llvm::BasicBlock *newBB =
              llvm::CloneBasicBlock(bb, bvmap, "", bb->getParent());
          newBB->getInstList().clear();
          t->newExecutedBBs.push_back(newBB);

          // copy instructions
          for (llvm::BasicBlock::iterator it = bb->begin(), ie = bb->end();
               it != ie; ++it) {
            llvm::Instruction *newIns = it->clone();
            newBB->getInstList().push_back(newIns);

            // update reference based on vmap
            //            llvm::errs() << "*** Size = " << vmap.size() << "
            // ***\n";
            //            llvm::errs() << "Node " << t->nodeSequenceNumber <<
            // "\n";
            //            it->dump();
            //            llvm::errs() << "------\n";
            //            newIns->dump();
            //            llvm::errs() << "------\n";

            updateRef(newIns, vmap);

            //            newIns->dump();
            //            llvm::errs() << "*** End Updating Instruction
            // ***\n\n";

            // add to vmap
            vmap[it] = newIns;
          }
        } else {
          for (llvm::BasicBlock::iterator it = bb->begin(), ie = bb->end();
               it != ie; ++it) {
            vmap[it] = it;
          }
          t->newExecutedBBs.push_back(bb);
          visitedBBs.insert(bb);
        }
      }

      if (t->trueTarget == NULL && t->trueTarget == NULL) {
        wl.pop_back();
        removeVal(vmap, t->newExecutedBBs);
      } else {
        if (t->trueTarget != NULL) {
          wl.push_back(t->trueTarget);
        }
        if (t->falseTarget != NULL) {
          wl.push_back(t->falseTarget);
        }
      }
    } else {
      wl.pop_back();
      removeVal(vmap, t->newExecutedBBs);
    }
  }

  // update branch instruction
  //  llvm::errs() << "Update Branch ============\n";
  updateBranchInsts();

  // dump to a new module
  std::string EC;
  llvm::raw_fd_ostream OS("module.bc", EC, llvm::sys::fs::F_None);
  WriteBitcodeToFile(kmodule->module, OS);
  OS.flush();
}

void TxTreeGraph::updateBranchInsts() {
  if (instance->root == NULL) {
    return;
  }

  // collect all nodes in graph using DFS
  std::vector<Node *> wl;
  wl.push_back(instance->root);
  while (!wl.empty()) {
    Node *t = wl.back();
    wl.pop_back();

    for (unsigned i = 0; i < t->newExecutedBBs.size(); ++i) {
      llvm::BasicBlock *bb = t->newExecutedBBs[i];
      if (i == t->newExecutedBBs.size() - 1) { // the last
        if (llvm::isa<llvm::BranchInst>(&bb->back())) {
          llvm::BranchInst *br = dyn_cast<llvm::BranchInst>(&bb->back());
          if (t->falseTarget != NULL && t->trueTarget != NULL) {
            br->setSuccessor(0, t->trueTarget->newExecutedBBs.front());
            br->setSuccessor(1, t->falseTarget->newExecutedBBs.front());
          }
        }
      } else { // internal
        bb->getInstList().pop_back();
        llvm::IRBuilder<> Builder(bb);
        Builder.CreateBr(t->newExecutedBBs[i + 1]);
      }
    }

    // add 2 children to work list
    if (t->trueTarget != NULL) {
      wl.push_back(t->trueTarget);
    }
    if (t->falseTarget != NULL) {
      wl.push_back(t->falseTarget);
    }
  }
}

void TxTreeGraph::updateRef(llvm::Instruction *ins,
                            llvm::ValueToValueMapTy &vmap) {
  //  llvm::errs() << "-- update ref --\n";
  if (llvm::isa<llvm::BranchInst>(ins)) {
    llvm::BranchInst *br = dyn_cast<llvm::BranchInst>(ins);
    if (br->isConditional()) {
      llvm::Value *cond = br->getCondition();
      //      cond->dump();
      if (vmap.find(cond) != vmap.end()) {
        //        vmap[cond]->dump();
        br->setCondition(vmap[cond]);
      }
    }
  } else {
    for (unsigned i = 0; i < ins->getNumOperands(); ++i) {
      llvm::Value *o = ins->getOperand(i);
      //      o->dump();
      if (vmap.find(o) != vmap.end()) {
        //        vmap[o]->dump();
        ins->setOperand(i, vmap[o]);
      }
    }
  }
  //  llvm::errs() << "-- end update ref --\n";
}

void TxTreeGraph::removeVal(llvm::ValueToValueMapTy &vmap,
                            std::vector<llvm::BasicBlock *> executedBBs) {
  for (unsigned i = 0; i < executedBBs.size(); ++i) {
    llvm::BasicBlock *bb = executedBBs[i];
    for (llvm::BasicBlock::iterator it = bb->begin(), ie = bb->end(); it != ie;
         ++it) {
      vmap.erase(it);
    }
  }
}

void TxTreeGraph::printMap(llvm::ValueToValueMapTy &vmap) {
  for (llvm::ValueToValueMapTy::iterator it = vmap.begin(), ie = vmap.end();
       it != ie; ++it) {
    it->first->dump();
    it->second->dump();
  }
}

void TxTreeGraph::printTree(KModule *kmodule) {
  if (instance->root == NULL) {
    return;
  }

  // collect all nodes in graph using DFS
  std::vector<Node *> graphNodes;
  std::vector<Node *> wl;
  wl.push_back(instance->root);
  while (!wl.empty()) {
    Node *t = wl.back();
    wl.pop_back();
    graphNodes.push_back(t);
    // add 2 children to work list
    if (t->trueTarget != NULL) {
      wl.push_back(t->trueTarget);
    }
    if (t->falseTarget != NULL) {
      wl.push_back(t->falseTarget);
    }
  }

  // print graph
  for (unsigned i = 0; i < graphNodes.size(); ++i) {
    llvm::errs() << "Node " << graphNodes[i]->nodeSequenceNumber << "\n";
    printNewExecutedBBs(graphNodes[i]);
    llvm::errs() << "====================\n";
  }
}

void TxTreeGraph::printBBs(KModule *kmodule, int id) {
  if (instance->root == NULL) {
    return;
  }

  // collect all nodes in graph using DFS
  std::vector<std::vector<llvm::BasicBlock *> > graphBBs;
  std::vector<Node *> wl;
  wl.push_back(instance->root);
  while (!wl.empty()) {
    Node *t = wl.back();
    wl.pop_back();

    if (id == 0) {
      graphBBs.push_back(t->executedBBs);
    } else {
      graphBBs.push_back(t->newExecutedBBs);
    }

    // add 2 children to work list
    if (t->trueTarget != NULL) {
      wl.push_back(t->trueTarget);
    }
    if (t->falseTarget != NULL) {
      wl.push_back(t->falseTarget);
    }
  }

  // print graph
  for (unsigned i = 0; i < graphBBs.size(); ++i) {
    llvm::errs() << "Node " << (i + 1) << "\n";
    for (unsigned j = 0; j < graphBBs[i].size(); ++j) {
      graphBBs[i][j]->dump();
    }
    llvm::errs() << "============\n\n";
  }
}

void TxTreeGraph::printDupBB(KModule *kmodule) {
  if (instance->root == NULL) {
    return;
  }

  // collect all nodes in graph using DFS
  std::set<llvm::BasicBlock *> bbs;
  std::vector<std::vector<llvm::BasicBlock *> > graphBBs;
  std::vector<Node *> wl;
  wl.push_back(instance->root);
  while (!wl.empty()) {
    Node *t = wl.back();
    wl.pop_back();

    std::vector<llvm::BasicBlock *> newBBs;
    for (unsigned i = 0; i < t->executedBBs.size(); ++i) {
      if (bbs.find(t->executedBBs[i]) == bbs.end()) {
        newBBs.push_back(t->executedBBs[i]);
        bbs.insert(t->executedBBs[i]);
      } else {
        llvm::ValueToValueMapTy VMap;
        llvm::BasicBlock *tbb = llvm::CloneBasicBlock(
            t->executedBBs[i], VMap, "", t->executedBBs[i]->getParent());
        newBBs.push_back(tbb);
      }
    }
    graphBBs.push_back(newBBs);

    // add 2 children to work list
    if (t->trueTarget != NULL) {
      wl.push_back(t->trueTarget);
    }
    if (t->falseTarget != NULL) {
      wl.push_back(t->falseTarget);
    }
  }

  // print graph
  for (unsigned i = 0; i < graphBBs.size(); ++i) {
    llvm::errs() << "Node " << (i + 1) << "\n";
    for (unsigned j = 0; j < graphBBs[i].size(); ++j) {
      graphBBs[i][j]->dump();
    }
    llvm::errs() << "============\n\n";
  }
}
