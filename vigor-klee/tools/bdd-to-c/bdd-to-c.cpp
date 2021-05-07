#include "load-call-paths.h"
#include "call-paths-to-bdd.h"
#include "ast.h"
#include "nodes.h"

#include "klee/ExprBuilder.h"
#include "klee/perf-contracts.h"
#include "klee/util/ArrayCache.h"
#include "klee/util/ExprSMTLIBPrinter.h"
#include "klee/util/ExprVisitor.h"
#include <klee/Constraints.h>
#include <klee/Solver.h>
#include "llvm/Support/CommandLine.h"

#include <algorithm>
#include <dlfcn.h>
#include <expr/Parser.h>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <regex>
#include <vector>
#include <memory>
#include <stack>
#include <utility>

namespace {
llvm::cl::list<std::string> InputCallPathFiles(llvm::cl::desc("<call paths>"),
                                               llvm::cl::Positional,
                                               llvm::cl::OneOrMore);


llvm::cl::OptionCategory SynthesizerCat("Synthesizer specific options");

llvm::cl::opt<std::string> Out(
    "out",
    llvm::cl::desc("Output file of the syntethized code. If omited, code will be dumped to stdout."),
    llvm::cl::cat(SynthesizerCat));

llvm::cl::opt<std::string> XML(
    "xml",
    llvm::cl::desc("Output file of the syntethized code's XML. If omited, XML will not be dumped."),
    llvm::cl::cat(SynthesizerCat));

llvm::cl::opt<TargetOption> Target(
    "target",
    llvm::cl::desc("Output file's target."),
    llvm::cl::cat(SynthesizerCat),
    llvm::cl::values(
      clEnumValN(SEQUENTIAL, "seq", "Sequential"),
      clEnumValN(SHARED_NOTHING, "sn", "Shared-nothing"),
      clEnumValN(LOCKS, "locks", "Lock based"),
      clEnumValN(TM, "tm", "Transactional memory"),
      clEnumValEnd
    ),
    llvm::cl::Required);
}

Node_ptr build_ast(AST& ast, const BDD::Node* root, TargetOption target) {
  std::vector<Node_ptr> nodes;

  while (root != nullptr) {
    root->dump(); std::cerr << "\n";

    switch (root->get_type()) {
    case BDD::Node::NodeType::BRANCH: {
      auto branch_node = static_cast<const BDD::Branch*>(root);

      auto on_true_bdd  = branch_node->get_on_true();
      auto on_false_bdd = branch_node->get_on_false();

      auto cond = branch_node->get_condition();

      ast.push();
      auto then_node = build_ast(ast, on_true_bdd, target);
      ast.pop();

      ast.push();
      auto else_node = build_ast(ast, on_false_bdd, target);
      ast.pop();

      auto cond_node = transpile(&ast, cond);

      auto on_true_filenames  = on_true_bdd  ? on_true_bdd->get_call_paths_filenames()  : std::vector<std::string>();
      auto on_false_filenames = on_false_bdd ? on_false_bdd->get_call_paths_filenames() : std::vector<std::string>();

      Node_ptr branch = Branch::build(cond_node, then_node, else_node, on_true_filenames, on_false_filenames);
      nodes.push_back(branch);

      root = nullptr;
      break;
    };

    case BDD::Node::NodeType::CALL: {
      auto call_bdd = static_cast<const BDD::Call*>(root);
      auto call = call_bdd->get_call();

      auto call_node = ast.node_from_call(call, target);

      if (call_node) {
        nodes.push_back(call_node);
      }

      root = root->get_next();
      break;
    };

    case BDD::Node::NodeType::RETURN_INIT: {
      auto return_init = static_cast<const BDD::ReturnInit*>(root);
      Expr_ptr ret_value;

      switch (return_init->get_return_value()) {
      case BDD::ReturnInit::ReturnType::SUCCESS: {
        ret_value = Constant::build(PrimitiveType::PrimitiveKind::INT, 1);
        break;
      };
      case BDD::ReturnInit::ReturnType::FAILURE: {
        ret_value = Constant::build(PrimitiveType::PrimitiveKind::INT, 0);
        break;
      };
      }

      nodes.push_back(Return::build(ret_value));

      root = nullptr;
      break;
    };

    case BDD::Node::NodeType::RETURN_PROCESS: {
      auto return_process = static_cast<const BDD::ReturnProcess*>(root);
      Node_ptr new_node;

      switch (return_process->get_return_operation()) {
      case BDD::ReturnProcess::Operation::FWD:
      case BDD::ReturnProcess::Operation::BCAST: {
        Expr_ptr ret_value = Constant::build(PrimitiveType::PrimitiveKind::INT, return_process->get_return_value());
        new_node = Return::build(ret_value);
        break;
      };
      case BDD::ReturnProcess::Operation::DROP: {
        Node_ptr ret = Return::build(ast.get_from_local("device"));
        Comment_ptr comm = Comment::build("dropping");
        new_node = Block::build(std::vector<Node_ptr>{ comm, ret }, false);
        break;
      };
      default: { assert(false); }
      }

      nodes.push_back(new_node);

      root = nullptr;
      break;
    };

    default: { assert(false); }
    }

  }

  assert(nodes.size());
  return Block::build(nodes);
}

void build_ast(AST& ast, const BDD::BDD& bdd, TargetOption target) {
  auto init_root = build_ast(ast, bdd.get_init(), target);
  
  Node_ptr global_code;
  std::vector<Node_ptr> intro_nodes;

  switch (target) {
    case LOCKS:
    case TM:
    case SEQUENTIAL: {
      std::vector<Node_ptr> nodes;

      auto state = ast.get_state();
      for (auto gv : state) {
        VariableDecl_ptr decl = VariableDecl::build(gv);
        decl->set_terminate_line(true);
        nodes.push_back(decl);
      }

      global_code = Block::build(nodes, false);
      break;
    }
    case SHARED_NOTHING: {
      std::vector<Node_ptr> nodes;

      auto state = ast.get_state();
      for (const auto& var : state) {
        // global
        std::string name = var->get_symbol();
        
        auto type = var->get_type();
        auto renamed = Variable::build("_" + name, type);
        auto ret = PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID);

        std::vector<ExpressionType_ptr> args = { type, renamed };

        auto def = FunctionCall::build("RTE_DEFINE_PER_LCORE", args, ret);
        def->set_terminate_line(true);
        nodes.push_back(def);

        // intro
        auto grab = FunctionCall::build("RTE_PER_LCORE", args, ret);
        grab->set_terminate_line(true);

        auto decl = VariableDecl::build(var);
        auto assignment = Assignment::build(decl, grab);
        assignment->set_terminate_line(true);

        intro_nodes.push_back(assignment);
      }

      global_code = Block::build(nodes, false);
      break;
    }
  }

  assert(init_root->get_kind() == Node::NodeKind::BLOCK);
  std::vector<Node_ptr> intro_nodes_init;

  if (target == TM) {
    auto void_ret = PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID);
    std::vector<ExpressionType_ptr> no_args;

    auto rte_lcore_id = FunctionCall::build("rte_lcore_id", no_args, void_ret);

    std::vector<ExpressionType_ptr> args = { rte_lcore_id };
    auto HTM_thr_init = FunctionCall::build("HTM_thr_init", args, void_ret);
    HTM_thr_init->set_terminate_line(true);

    intro_nodes_init.push_back(HTM_thr_init);
  }

  if (target == LOCKS || target == TM) {
    auto ret = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);
    std::vector<ExpressionType_ptr> args;

    auto rte_get_master_lcore = FunctionCall::build("rte_get_master_lcore", args, ret);
    auto rte_lcore_id = FunctionCall::build("rte_lcore_id", args, ret);

    auto cond = Not::build(Equals::build(rte_get_master_lcore, rte_lcore_id));

    auto one = Constant::build(PrimitiveType::PrimitiveKind::INT, 1);
    auto on_true = Return::build(one);

    intro_nodes_init.push_back(Branch::build(cond, on_true));
  }

  intro_nodes_init.insert(intro_nodes_init.end(), intro_nodes.begin(), intro_nodes.end());
  intro_nodes_init.push_back(Block::build(init_root, false));

  init_root = Block::build(intro_nodes_init);

  ast.set_global_code(global_code);
  ast.commit(init_root);

  auto process_root = build_ast(ast, bdd.get_process(), target);

  assert(process_root->get_kind() == Node::NodeKind::BLOCK);
  std::vector<Node_ptr> intro_nodes_process = intro_nodes;

  if (target == LOCKS) {
    intro_nodes_process.push_back(AST::grab_locks());
  }

  intro_nodes_process.push_back(Block::build(process_root, false));
  process_root = Block::build(intro_nodes_process);

  ast.commit(process_root);
}

int main(int argc, char **argv) {
  llvm::cl::ParseCommandLineOptions(argc, argv);
  std::vector<call_path_t*> call_paths;

  for (auto file : InputCallPathFiles) {
    std::cerr << "Loading: " << file << std::endl;

    std::vector<std::string> expressions_str;
    std::deque<klee::ref<klee::Expr>> expressions;

    call_path_t *call_path = load_call_path(file, expressions_str, expressions);
    call_paths.push_back(call_path);
  }

  std::cerr << "Building the BDD...\n";
  BDD::BDD bdd(call_paths);
  std::cerr << "Done!\n";

  AST ast;

  build_ast(ast, bdd, Target);

  if (Out.size()) {
    auto file = std::ofstream(Out);
    assert(file.is_open());
    ast.print(file);
  } else {
    ast.print(std::cout);
  }

  if (XML.size()) {
    auto file = std::ofstream(XML);
    assert(file.is_open());
    ast.print_xml(file);
  }

  for (auto call_path : call_paths) {
    delete call_path;
  }

  return 0;
}
