#include "call-paths-to-bdd.h"

namespace BDD {

constexpr char BDD::INIT_CONTEXT_MARKER[];

std::vector<std::string> call_paths_t::skip_functions {
  "loop_invariant_consume",
  "loop_invariant_produce",
  "packet_receive",
  "packet_state_total_length",
  "packet_free",
  "packet_send"
};

std::vector<std::string> BDD::skip_conditions_with_symbol {
  "received_a_packet",
  "loop_termination"
};

std::string BDD::get_fname(const Node* node) {
  assert(node->get_type() == Node::NodeType::CALL);
  const Call* call = static_cast<const Call*>(node);
  return call->get_call().function_name;
}

bool call_paths_t::is_skip_function(const std::string& fname) {
  auto found_it = std::find(call_paths_t::skip_functions.begin(), call_paths_t::skip_functions.end(), fname);
  return found_it != call_paths_t::skip_functions.end();
}

bool BDD::is_skip_function(const Node* node) {
  auto fname = BDD::get_fname(node);
  return call_paths_t::is_skip_function(fname);
}

bool BDD::is_skip_condition(const Node* node) {
  assert(node->get_type() == Node::NodeType::BRANCH);
  const Branch* branch = static_cast<const Branch*>(node);
  auto cond = branch->get_condition();

  RetrieveSymbols retriever;
  retriever.visit(cond);

  auto symbols = retriever.get_retrieved_strings();
  for (const auto& symbol : symbols) {
    auto found_it = std::find(BDD::skip_conditions_with_symbol.begin(),
                              BDD::skip_conditions_with_symbol.end(), symbol);
    if (found_it != BDD::skip_conditions_with_symbol.end()) {
      return true;
    }
  }

  return false;
}

bool solver_toolbox_t::is_expr_always_true(klee::ref<klee::Expr> expr) const {
  klee::ConstraintManager no_constraints;
  return is_expr_always_true(no_constraints, expr);
}

bool solver_toolbox_t::is_expr_always_true(klee::ConstraintManager constraints, klee::ref<klee::Expr> expr) const {
  klee::Query sat_query(constraints, expr);

  bool result;
  bool success = solver->mustBeTrue(sat_query, result);
  assert(success);

  return result;
}

bool solver_toolbox_t::is_expr_always_true(klee::ConstraintManager constraints,
                                           klee::ref<klee::Expr> expr,
                                           ReplaceSymbols& symbol_replacer) const {
    klee::ConstraintManager replaced_constraints;

    for (auto constr : constraints) {
      replaced_constraints.addConstraint(symbol_replacer.visit(constr));
    }

    return is_expr_always_true(replaced_constraints, expr);
  }

bool solver_toolbox_t::is_expr_always_false(klee::ref<klee::Expr> expr) const {
  klee::ConstraintManager no_constraints;
  return is_expr_always_false(no_constraints, expr);
}

bool solver_toolbox_t::is_expr_always_false(klee::ConstraintManager constraints,
                                            klee::ref<klee::Expr> expr) const {
  klee::Query sat_query(constraints, expr);

  bool result;
  bool success = solver->mustBeFalse(sat_query, result);
  assert(success);

  return result;
}

bool solver_toolbox_t::is_expr_always_false(klee::ConstraintManager constraints,
                                            klee::ref<klee::Expr> expr,
                                            ReplaceSymbols& symbol_replacer) const {
    klee::ConstraintManager replaced_constraints;

    for (auto constr : constraints) {
      replaced_constraints.addConstraint(symbol_replacer.visit(constr));
    }

    return is_expr_always_false(replaced_constraints, expr);
  }

bool solver_toolbox_t::are_exprs_always_equal(klee::ref<klee::Expr> expr1, klee::ref<klee::Expr> expr2) const {
  if (expr1.isNull() != expr2.isNull()) {
    return false;
  }

  if (expr1.isNull()) {
    return true;
  }

  RetrieveSymbols symbol_retriever;
  symbol_retriever.visit(expr1);
  std::vector<klee::ref<klee::ReadExpr>> symbols = symbol_retriever.get_retrieved();

  ReplaceSymbols symbol_replacer(symbols);
  klee::ref<klee::Expr> replaced = symbol_replacer.visit(expr2);

  return is_expr_always_true(exprBuilder->Eq(expr1, replaced));
}

uint64_t solver_toolbox_t::value_from_expr(klee::ref<klee::Expr> expr) const {
  klee::ConstraintManager no_constraints;
  klee::Query sat_query(no_constraints, expr);

  klee::ref<klee::ConstantExpr> value_expr;
  bool success = solver->getValue(sat_query, value_expr);

  assert(success);
  return value_expr->getZExtValue();
}

void CallPathsGroup::group_call_paths() {
  assert(call_paths.size());

  for (const auto& cp : call_paths.cp) {
    on_true.clear();
    on_false.clear();

    if (cp->calls.size() == 0) {
      continue;
    }

    call_t call = cp->calls[0];

    for (unsigned int icp = 0; icp < call_paths.size(); icp++) {
      auto pair = call_paths.get(icp);

      if (pair.first->calls.size() && are_calls_equal(pair.first->calls[0], call)) {
        on_true.push_back(pair);
        continue;
      }

      on_false.push_back(pair);
    }

    // all calls are equal, no need do discriminate
    if (on_false.size() == 0) {
      return;
    }

    discriminating_constraint = find_discriminating_constraint();

    if (!discriminating_constraint.isNull()) {
      return;
    }
  }

  // no more calls
  if (on_true.size() == 0 && on_false.size() == 0) {
    on_true = call_paths;
    return;
  }

  assert(false && "Could not group call paths");
}

bool CallPathsGroup::are_calls_equal(call_t c1, call_t c2) {
  if (c1.function_name != c2.function_name) {
    return false;
  }

  for (auto arg_name_value_pair : c1.args) {
    auto arg_name = arg_name_value_pair.first;

    // exception: we don't care about 'p' differences
    if (arg_name == "p" || arg_name == "src_devices") {
      continue;
    }

    auto c1_arg = c1.args[arg_name];
    auto c2_arg = c2.args[arg_name];

    if (!c1_arg.out.isNull()) {
      continue;
    }

    // comparison between modifications to the received packet
    if (c1.function_name == "packet_return_chunk" && arg_name == "the_chunk" &&
        !solver_toolbox.are_exprs_always_equal(c1_arg.in, c2_arg.in)) {
      return false;
    }

    if (!solver_toolbox.are_exprs_always_equal(c1_arg.expr, c2_arg.expr)) {
      return false;
    }
  }

  return true;
}

klee::ref<klee::Expr> CallPathsGroup::find_discriminating_constraint() {
  assert(on_true.size());

  auto possible_discriminating_constraints = get_possible_discriminating_constraints();

  for (auto constraint : possible_discriminating_constraints) {
    if (check_discriminating_constraint(constraint)) {
      return constraint;
    }
  }

  return klee::ref<klee::Expr>();
}

std::vector<klee::ref<klee::Expr>> CallPathsGroup::get_possible_discriminating_constraints() const {
  std::vector<klee::ref<klee::Expr>> possible_discriminating_constraints;
  assert(on_true.size());

  for (auto constraint : on_true.cp[0]->constraints) {
    if (satisfies_constraint(on_true.cp, constraint)) {
      possible_discriminating_constraints.push_back(constraint);
    }
  }

  return possible_discriminating_constraints;
}

bool CallPathsGroup::satisfies_constraint(std::vector<call_path_t*> call_paths,
                                          klee::ref<klee::Expr> constraint) const {
  for (const auto& call_path : call_paths) {
    if (!satisfies_constraint(call_path, constraint)) {
      return false;
    }
  }
  return true;
}

bool CallPathsGroup::satisfies_constraint(call_path_t* call_path, klee::ref<klee::Expr> constraint) const {
  RetrieveSymbols symbol_retriever;
  symbol_retriever.visit(constraint);
  std::vector<klee::ref<klee::ReadExpr>> symbols = symbol_retriever.get_retrieved();

  ReplaceSymbols symbol_replacer(symbols);
  auto not_constraint = solver_toolbox.exprBuilder->Not(constraint);

  return solver_toolbox.is_expr_always_false(call_path->constraints, not_constraint, symbol_replacer);
}

bool CallPathsGroup::satisfies_not_constraint(std::vector<call_path_t*> call_paths,
                                              klee::ref<klee::Expr> constraint) const {
  for (const auto& call_path : call_paths) {
    if (!satisfies_not_constraint(call_path, constraint)) {
      return false;
    }
  }
  return true;
}

bool CallPathsGroup::satisfies_not_constraint(call_path_t* call_path, klee::ref<klee::Expr> constraint) const {
  RetrieveSymbols symbol_retriever;
  symbol_retriever.visit(constraint);
  std::vector<klee::ref<klee::ReadExpr>> symbols = symbol_retriever.get_retrieved();

  ReplaceSymbols symbol_replacer(symbols);
  auto not_constraint = solver_toolbox.exprBuilder->Not(constraint);

  return solver_toolbox.is_expr_always_true(call_path->constraints, not_constraint, symbol_replacer);
}

bool CallPathsGroup::check_discriminating_constraint(klee::ref<klee::Expr> constraint) {
  assert(on_true.size());
  assert(on_false.size());

  call_paths_t _on_true = on_true;
  call_paths_t _on_false;

  for (unsigned int i = 0; i < on_false.size(); i++) {
    auto pair = on_false.get(i);
    auto call_path = pair.first;

    if (satisfies_constraint(call_path, constraint)) {
      _on_true.push_back(pair);
    } else {
      _on_false.push_back(pair);
    }
  }

  if (_on_false.size() && satisfies_not_constraint(_on_false.cp, constraint)) {
    on_true  = _on_true;
    on_false = _on_false;
    return true;
  }

  return false;
}

call_t BDD::get_successful_call(std::vector<call_path_t*> call_paths) const {
  assert(call_paths.size());

  for (const auto& cp : call_paths) {
    assert(cp->calls.size());
    call_t call = cp->calls[0];

    if (call.ret.isNull()) {
      return call;
    }

    auto zero = solver_toolbox.exprBuilder->Constant(0, call.ret->getWidth());
    auto eq_zero = solver_toolbox.exprBuilder->Eq(call.ret, zero);
    auto is_ret_success = solver_toolbox.is_expr_always_false(eq_zero);

    if (is_ret_success) {
      return call;
    }
  }

  // no function with successful return
  return call_paths[0]->calls[0];
}

Node* BDD::populate(call_paths_t call_paths) {
  Node* local_root = nullptr;
  Node* local_leaf = nullptr;

  ReturnRaw* return_raw = new ReturnRaw(get_and_inc_id(), call_paths);

  while (call_paths.cp.size()) {
    CallPathsGroup group(call_paths, solver_toolbox);

    auto on_true  = group.get_on_true();
    auto on_false = group.get_on_false();

    if (on_true.cp.size() == call_paths.cp.size()) {
      assert(on_false.cp.size() == 0);

      if (on_true.cp[0]->calls.size() == 0) {
        break;
      }

      Call* node = new Call(get_and_inc_id(), get_successful_call(on_true.cp), on_true.cp);

      // root node
      if (local_root == nullptr) {
        local_root = node;
        local_leaf = node;
      } else {
        local_leaf->add_next(node);
        node->add_prev(local_leaf);
        local_leaf = node;
      }

      for (auto& cp : call_paths.cp) {
        assert(cp->calls.size());
        cp->calls.erase(cp->calls.begin());
      }
    } else {
      auto discriminating_constraint = group.get_discriminating_constraint();

      Branch* node = new Branch(get_and_inc_id(), discriminating_constraint, call_paths.cp);

      Node* on_true_root  = populate(on_true);
      Node* on_false_root = populate(on_false);

      node->add_on_true(on_true_root);
      node->add_on_false(on_false_root);

      if (local_root == nullptr) {
        return node;
      }

      local_leaf->add_next(node);
      node->add_prev(local_leaf);

      return local_root;
    }
  }

  if (local_root == nullptr) {
    local_root = return_raw;
  } else {
    local_leaf->add_next(return_raw);
    return_raw->add_prev(local_leaf);
  }

  return local_root;
}

Node* BDD::populate_init(const Node* root) {
  Node* local_root = nullptr;
  Node* local_leaf = nullptr;
  Node* new_node;

  while (root != nullptr) {
    new_node = nullptr;

    switch (root->get_type()) {
    case Node::NodeType::CALL: {
      if (get_fname(root) == BDD::INIT_CONTEXT_MARKER) {
        root = nullptr;
        break;
      }

      if (!is_skip_function(root)) {
        new_node = root->clone();
        new_node->replace_next(nullptr);
        new_node->replace_prev(nullptr);
      }

      root = root->get_next();
      break;
    };
    case Node::NodeType::BRANCH: {
      const Branch* root_branch = static_cast<const Branch*>(root);

      Node* on_true_node  = populate_init(root_branch->get_on_true());
      Node* on_false_node = populate_init(root_branch->get_on_false());

      Branch* branch = static_cast<Branch*>(root->clone());

      branch->replace_on_true(on_true_node);
      branch->replace_on_false(on_false_node);

      new_node = branch;
      root = nullptr;

      break;
    };
    case Node::NodeType::RETURN_RAW: {
      const ReturnRaw* root_return_raw = static_cast<const ReturnRaw*>(root);
      new_node = new ReturnInit(get_and_inc_id(), root_return_raw);

      root = nullptr;
      break;
    };
    default: {
      assert(false && "Should not encounter return nodes here");
    };
    }

    if (new_node && local_leaf == nullptr) {
      local_root = new_node;
      local_leaf = local_root;
    } else if (new_node) {
      local_leaf->replace_next(new_node);
      new_node->replace_prev(local_leaf);
      local_leaf = new_node;
    }
  }

  if (local_root == nullptr) {
    local_root = new ReturnInit(get_and_inc_id());
  }

  return local_root;
}

Node* BDD::populate_process(const Node* root, bool store) {
  Node* local_root = nullptr;
  Node* local_leaf = nullptr;
  Node* new_node;

  while (root != nullptr) {
    new_node = nullptr;

    switch (root->get_type()) {
    case Node::NodeType::CALL: {
      if (get_fname(root) == BDD::INIT_CONTEXT_MARKER) {
        store = true;
        root = root->get_next();
        break;
      }

      if (store && !is_skip_function(root)) {
        new_node = root->clone();
        new_node->replace_next(nullptr);
        new_node->replace_prev(nullptr);
      }

      root = root->get_next();
      break;
    };
    case Node::NodeType::BRANCH: {
      const Branch* root_branch = static_cast<const Branch*>(root);
      assert(root_branch->get_on_true());
      assert(root_branch->get_on_false());

      Node* on_true_node  = populate_process(root_branch->get_on_true(), store);
      Node* on_false_node = populate_process(root_branch->get_on_false(), store);

      assert(on_true_node);
      assert(on_false_node);

      auto skip = is_skip_condition(root);
      auto equal = false;

      if (on_true_node->get_type() == Node::NodeType::RETURN_PROCESS &&
          on_false_node->get_type() == Node::NodeType::RETURN_PROCESS) {

        ReturnProcess* on_true_ret_process  = static_cast<ReturnProcess*>(on_true_node);
        ReturnProcess* on_false_ret_process = static_cast<ReturnProcess*>(on_false_node);

        equal |= (on_true_ret_process->get_return_operation() == on_false_ret_process->get_return_operation() &&
                  on_true_ret_process->get_return_value() == on_false_ret_process->get_return_value());
      }

      if (store && equal) {
        new_node = on_true_node;
      }

      else if (store && !skip) {
        Branch* branch = static_cast<Branch*>(root->clone());

        branch->replace_on_true(on_true_node);
        branch->replace_on_false(on_false_node);

        new_node = branch;
      }

      else {
        auto on_true_empty = on_true_node->get_type() == Node::NodeType::RETURN_INIT ||
                             on_true_node->get_type() == Node::NodeType::RETURN_PROCESS;

        auto on_false_empty = on_false_node->get_type() == Node::NodeType::RETURN_INIT ||
                              on_false_node->get_type() == Node::NodeType::RETURN_PROCESS;

        if (on_true_node->get_type() == Node::NodeType::RETURN_PROCESS) {
          ReturnProcess* on_true_return_process = static_cast<ReturnProcess*>(on_true_node);
          on_true_empty |= (on_true_return_process->get_return_operation() == ReturnProcess::Operation::ERR);
        }

        if (on_false_node->get_type() == Node::NodeType::RETURN_PROCESS) {
          ReturnProcess* on_false_return_process = static_cast<ReturnProcess*>(on_false_node);
          on_false_empty |= (on_false_return_process->get_return_operation() == ReturnProcess::Operation::ERR);
        }

        assert(on_true_empty || on_false_empty);
        new_node = on_false_empty ? on_true_node : on_false_node;
      }

      root = nullptr;
      break;
    };
    case Node::NodeType::RETURN_RAW: {
      const ReturnRaw* root_return_raw = static_cast<const ReturnRaw*>(root);
      new_node = new ReturnProcess(get_and_inc_id(), root_return_raw);

      root = nullptr;
      break;
    };
    default: {
      assert(false && "Should not encounter return nodes here");
    };
    }

    if (new_node && local_leaf == nullptr) {
      local_root = new_node;
      local_leaf = new_node;
    } else if (new_node) {
      local_leaf->replace_next(new_node);
      new_node->replace_prev(local_leaf);
      local_leaf = new_node;
    }
  }

  assert(local_root);
  return local_root;
}

void BDD::dump() const {
  std::cerr << "\n================== INIT ==================\n";
  dump(0, nf_init.get());

  std::cerr << "\n================== PROCESS ==================\n";
  dump(0, nf_process.get());
}

void BDD::dump(int lvl, const Node* node) const {
  std::string sep = std::string(lvl*2, ' ');

  if (node) {
    std::cerr << "\n";
    for (auto filename : node->get_call_paths_filenames()) {
      std::cerr << sep << "[" << filename << "]" << "\n";
    }
  }

  while (node) {
    node->dump_compact(lvl);

    if (node->get_type() == Node::NodeType::BRANCH) {
      const Branch* branch_node = static_cast<const Branch*>(node);
      dump(lvl+1, branch_node->get_on_true());
      dump(lvl+1, branch_node->get_on_false());
      return;
    }

    node = node->get_next();
  }
}
}
