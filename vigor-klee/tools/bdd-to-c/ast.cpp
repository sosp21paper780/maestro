#include "ast.h"
#include "printer.h"

constexpr char AST::CHUNK_LAYER_2[];
constexpr char AST::CHUNK_LAYER_3[];
constexpr char AST::CHUNK_LAYER_4[];

Variable_ptr AST::generate_new_symbol(klee::ref<klee::Expr> expr) {
  Type_ptr type = type_from_size(expr->getWidth());

  RetrieveSymbols retriever;
  retriever.visit(expr);
  auto symbols = retriever.get_retrieved_strings();
  assert(symbols.size() == 1);

  std::string symbol = from_cp_symbol(symbols[0]);

  auto state_partial_name_finder = [&](Variable_ptr v) -> bool {
    std::string local_symbol = v->get_symbol();
    return local_symbol.find(symbol) != std::string::npos;
  };

  auto local_partial_name_finder = [&](local_variable_t v) -> bool {
    std::string local_symbol = v.first->get_symbol();
    return local_symbol.find(symbol) != std::string::npos;
  };

  auto state_it = std::find_if(state.begin(), state.end(), state_partial_name_finder);
  assert(state_it == state.end());

  for (auto i = local_variables.rbegin(); i != local_variables.rend(); i++) {
    auto stack = *i;
    auto local_it = std::find_if(stack.begin(), stack.end(), local_partial_name_finder);
    assert(local_it == stack.end());
  }

  return Variable::build(symbol, type);
}

Variable_ptr AST::generate_new_symbol(std::string symbol, Type_ptr type,
                                      unsigned int ptr_lvl, unsigned int counter_begins) {

  symbol = from_cp_symbol(symbol);

  auto state_partial_name_finder = [&](Variable_ptr v) -> bool {
    std::string local_symbol = v->get_symbol();
    return local_symbol.find(symbol) != std::string::npos;
  };

  auto local_partial_name_finder = [&](local_variable_t v) -> bool {
    std::string local_symbol = v.first->get_symbol();
    return local_symbol.find(symbol) != std::string::npos;
  };

  auto state_it = std::find_if(state.begin(), state.end(), state_partial_name_finder);

  unsigned int counter = 0;
  unsigned int last_id = 0;

  while (state_it != state.end()) {
    Variable_ptr var = *state_it;
    std::string saved_symbol = var->get_symbol();

    auto delim = saved_symbol.find(symbol);
    assert(delim != std::string::npos);

    std::string suffix = saved_symbol.substr(delim + symbol.size());
    if (suffix.size() > 1 && isdigit(suffix[1])) {
      assert(suffix[0] == '_');
      suffix = suffix.substr(1);
      unsigned int id = std::stoi(suffix, nullptr);
      if (last_id < id) {
        last_id = id;
      }
    }

    counter++;
    state_it = std::find_if(++state_it, state.end(), state_partial_name_finder);
  }

  for (auto i = local_variables.rbegin(); i != local_variables.rend(); i++) {
    auto stack = *i;
    auto local_it = std::find_if(stack.begin(), stack.end(), local_partial_name_finder);

    while (local_it != stack.end()) {
      Variable_ptr var = local_it->first;
      std::string saved_symbol = var->get_symbol();

      auto delim = saved_symbol.find(symbol);
      assert(delim != std::string::npos);

      std::string suffix = saved_symbol.substr(delim + symbol.size());
      if (suffix.size() > 1 && isdigit(suffix[1])) {
        assert(suffix[0] == '_');
        suffix = suffix.substr(1);
        unsigned int id = std::stoi(suffix, nullptr);
        if (last_id < id) {
          last_id = id;
        }
      }

      counter++;
      local_it = std::find_if(++local_it, stack.end(), local_partial_name_finder);
    }
  }

  std::string new_symbol = symbol;

  if (counter == 0 && counter_begins > 0) {
    new_symbol += "_" + std::to_string(counter_begins);
  }

  else if (counter > 0) {
    new_symbol += "_" + std::to_string(last_id + 1);
  }

  while (ptr_lvl != 0) {
    type = Pointer::build(type);
    ptr_lvl--;
  }

  return Variable::build(new_symbol, type);
}

Variable_ptr AST::generate_new_symbol(const std::string& symbol, Type_ptr type) {
  return generate_new_symbol(symbol, type, 0, 0);
}

Variable_ptr AST::get_from_state(const std::string& symbol) {
  auto translated = from_cp_symbol(symbol);

  auto finder = [&](Variable_ptr v) -> bool {
    return translated == v->get_symbol();
  };

  auto it = std::find_if(state.begin(), state.end(), finder);

  if (it == state.end()) {
    return nullptr;
  }

  return *it;
}

std::string AST::from_cp_symbol(std::string name) {
  if (callpath_var_translation.find(name) == callpath_var_translation.end()) {
    return name;
  }

  return callpath_var_translation[name];
}

AST::chunk_t AST::get_chunk_from_local(unsigned int idx) {
  chunk_t result;

  result.var = nullptr;
  result.start_index = 0;

  auto finder = [&](local_variable_t v) -> bool {
    Variable_ptr var = v.first;
    klee::ref<klee::Expr> expr = v.second;

    std::string symbol = var->get_symbol();

    if (symbol != CHUNK_LAYER_2 &&
        symbol != CHUNK_LAYER_3 &&
        symbol != CHUNK_LAYER_4) {
      return false;
    }

    if (expr->getKind() != klee::Expr::Kind::Concat) {
      return false;
    }

    auto start_idx = get_first_concat_idx(solver, expr);
    auto end_idx = get_last_concat_idx(solver, expr);

    return start_idx <= idx && idx <= end_idx;
  };

  for (auto i = local_variables.rbegin(); i != local_variables.rend(); i++) {
    auto stack = *i;
    auto it = std::find_if(stack.begin(), stack.end(), finder);
    if (it != stack.end()) {
      result.var = it->first;
      result.start_index = get_first_concat_idx(solver, it->second);
      break;
    }
  }

  return result;
}

Variable_ptr AST::get_from_local(const std::string& symbol, bool partial) {
  auto translated = from_cp_symbol(symbol);

  auto finder = [&](local_variable_t v) -> bool {
    if (!partial) {
      return v.first->get_symbol() == translated;
    } else {
      std::string local_symbol = v.first->get_symbol();
      return local_symbol.find(translated) != std::string::npos;
    }
  };

  for (auto i = local_variables.rbegin(); i != local_variables.rend(); i++) {
    auto stack = *i;

    auto it = std::find_if(stack.begin(), stack.end(), finder);
    if (it != stack.end()) {
      return it->first;
    }
  }

  return nullptr;
}

klee::ref<klee::Expr> AST::get_expr_from_local_by_addr(unsigned int addr) {
  klee::ref<klee::Expr> found;

  assert(addr != 0);
  auto addr_finder = [&](local_variable_t v) -> bool {
    unsigned int local_addr = v.first->get_addr();
    return local_addr == addr;
  };

  for (auto i = local_variables.rbegin(); i != local_variables.rend(); i++) {
    auto stack = *i;
    auto it = std::find_if(stack.begin(), stack.end(), addr_finder);
    if (it != stack.end()) {
      found = it->second;
      break;
    }
  }

  return found;
}

Variable_ptr AST::get_from_local_by_addr(const std::string& symbol, unsigned int addr) {
  assert(addr != 0);
  auto translated = from_cp_symbol(symbol);

  auto partial_name_finder = [&](local_variable_t v) -> bool {
    std::string local_symbol = v.first->get_symbol();
    return local_symbol.find(translated) != std::string::npos;
  };

  auto addr_finder = [&](local_variable_t v) -> bool {
    unsigned int local_addr = v.first->get_addr();
    return local_addr == addr;
  };

  for (auto i = local_variables.rbegin(); i != local_variables.rend(); i++) {
    auto stack = *i;
    auto it = std::find_if(stack.begin(), stack.end(), addr_finder);
    if (it != stack.end()) {
      return it->first;
    }
  }

  // allocating)
  for (auto i = local_variables.rbegin(); i != local_variables.rend(); i++) {
    auto stack = *i;
    auto it = std::find_if(stack.begin(), stack.end(), partial_name_finder);

    if (it == stack.end()) {
      continue;
    }

    Variable_ptr var = it->first;

    if (var->get_addr() != 0) {
      continue;
    }

    var->set_addr(addr);
    return var;
  }

  assert(false && "All pointers are allocated, or symbol not found");
  Variable_ptr ptr;
  return ptr;
}

Variable_ptr AST::get_from_state(unsigned int addr) {
  assert(addr != 0);

  auto addr_finder = [&](Variable_ptr v) -> bool {
    return v->get_addr() == addr;
  };

  auto addr_finder_it = std::find_if(state.begin(), state.end(), addr_finder);
  if (addr_finder_it != state.end()) {
    return *addr_finder_it;
  }

  dump_stack();
  std::cerr << "Address requested: " << addr << "\n";
  assert(false && "No variable allocated in this address");
}

Expr_ptr AST::get_from_local(klee::ref<klee::Expr> expr) {
  assert(!expr.isNull());

  auto find_matching_offset = [](klee::ref<klee::Expr> saved,
                                 klee::ref<klee::Expr> wanted,
                                 const BDD::solver_toolbox_t& solver) -> int {
    auto saved_sz = saved->getWidth();
    auto wanted_sz = wanted->getWidth();

    if (wanted_sz > saved_sz) {
      return -1;
    }

    for (unsigned int offset = 0; offset <= saved_sz - wanted_sz; offset += 8) {
      auto saved_chunk = solver.exprBuilder->Extract(saved, offset, wanted_sz);

      if (solver.are_exprs_always_equal(saved_chunk, wanted)) {
        return offset;
      }
    }

    return -1;
  };

  auto finder = [&](local_variable_t v) -> bool {
    if (v.second.isNull()) {
      return false;
    }

    return find_matching_offset(v.second, expr, solver) >= 0;
  };

  for (auto i = local_variables.rbegin(); i != local_variables.rend(); i++) {
    auto stack = *i;

    auto it = std::find_if(stack.begin(), stack.end(), finder);
    if (it != stack.end()) {
      auto offset = find_matching_offset(it->second, expr, solver);
      assert(offset % 8 == 0 && "Found the local variable, but offset is not multiple of byte");

      if (offset == 0 && it->second->getWidth() == expr->getWidth()) {
        return it->first;
      }

      Constant_ptr idx = Constant::build(PrimitiveType::PrimitiveKind::UINT64_T, offset / 8);
      Read_ptr extracted = Read::build(it->first, type_from_size(expr->getWidth()), idx);

      return extracted;
    }
  }

  return nullptr;
}

void AST::associate_expr_to_local(const std::string& symbol, klee::ref<klee::Expr> expr) {
  auto translated = from_cp_symbol(symbol);

  auto name_finder = [&](local_variable_t v) -> bool {
    return v.first->get_symbol() == translated;
  };

  for (auto i = local_variables.rbegin(); i != local_variables.rend(); i++) {
    auto stack = *i;

    auto name_it = std::find_if(stack.begin(), stack.end(), name_finder);
    if (name_it != stack.end()) {
      auto association = std::make_pair(name_it->first, expr);
      std::replace_if(stack.begin(), stack.end(), name_finder, association);
      return;
    }
  }

  assert(false && "Variable not found");
}

void AST::push_to_state(Variable_ptr var) {
  assert(get_from_state(var->get_symbol()) == nullptr);
  state.push_back(var);
}

void AST::push_to_local(Variable_ptr var) {
  assert(get_from_local(var->get_symbol()) == nullptr);
  assert(local_variables.size() > 0);
  local_variables.back().push_back(std::make_pair(var, nullptr));
}

void AST::push_to_local(Variable_ptr var, klee::ref<klee::Expr> expr) {
  assert(get_from_local(var->get_symbol()) == nullptr);
  assert(local_variables.size() > 0);
  local_variables.back().push_back(std::make_pair(var, expr));
}

Node_ptr AST::init_state_node_from_call(call_t call, TargetOption target) {
  auto fname = call.function_name;
  std::vector<ExpressionType_ptr> args;

  PrimitiveType_ptr ret_type;
  std::string ret_symbol;

  if (fname == "map_allocate") {
    Expr_ptr map_out_expr = transpile(this, call.args["map_out"].out);
    assert(map_out_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t map_addr = (static_cast<Constant*>(map_out_expr.get()))->get_value();

    assert(call.args["keq"].fn_ptr_name.first);
    assert(call.args["khash"].fn_ptr_name.first);
    Type_ptr void_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID);

    Expr_ptr keq = Variable::build(call.args["keq"].fn_ptr_name.second, void_type);
    assert(keq);
    Expr_ptr khash = Variable::build(call.args["khash"].fn_ptr_name.second, void_type);
    assert(khash);
    Expr_ptr capacity = transpile(this, call.args["capacity"].expr);
    assert(capacity);

    Type_ptr map_type = Struct::build(translate_struct("Map", target));
    Variable_ptr new_map = generate_new_symbol("map", map_type, 1, 0);
    new_map->set_addr(map_addr);

    push_to_state(new_map);

    args = std::vector<ExpressionType_ptr>{ keq, khash, capacity, AddressOf::build(new_map) };

    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);
    ret_symbol = "map_allocation_succeeded";
  }

  else if (fname == "vector_allocate") {
    Expr_ptr vector_out_expr = transpile(this, call.args["vector_out"].out);
    assert(vector_out_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t vector_addr = (static_cast<Constant*>(vector_out_expr.get()))->get_value();

    assert(call.args["init_elem"].fn_ptr_name.first);
    Type_ptr void_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID);

    Expr_ptr elem_size = transpile(this, call.args["elem_size"].expr);
    assert(elem_size);
    Expr_ptr capacity = transpile(this, call.args["capacity"].expr);
    assert(capacity);
    Expr_ptr init_elem = Variable::build(call.args["init_elem"].fn_ptr_name.second, void_type);
    assert(init_elem);

    Type_ptr vector_type = Struct::build(translate_struct("Vector", target));
    Variable_ptr new_vector = generate_new_symbol("vector", vector_type, 1, 0);
    new_vector->set_addr(vector_addr);

    push_to_state(new_vector);

    args = std::vector<ExpressionType_ptr>{ elem_size, capacity, init_elem, AddressOf::build(new_vector) };

    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);
    ret_symbol = "vector_alloc_success";
  }

  else if (fname == "dchain_allocate") {
    Expr_ptr chain_out_expr = transpile(this, call.args["chain_out"].out);
    assert(chain_out_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t dchain_addr = (static_cast<Constant*>(chain_out_expr.get()))->get_value();

    Expr_ptr index_range = transpile(this, call.args["index_range"].expr);
    assert(index_range);

    Type_ptr dchain_type = Struct::build(translate_struct("DoubleChain", target));
    Variable_ptr new_dchain = generate_new_symbol("dchain", dchain_type, 1, 0);
    new_dchain->set_addr(dchain_addr);

    push_to_state(new_dchain);

    args = std::vector<ExpressionType_ptr>{ index_range, AddressOf::build(new_dchain) };

    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);
    ret_symbol = "is_dchain_allocated";
  }

  else if (fname == "cht_fill_cht") {
    Expr_ptr vector_expr = transpile(this, call.args["cht"].expr);
    assert(vector_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t vector_addr = (static_cast<Constant*>(vector_expr.get()))->get_value();

    Expr_ptr vector = get_from_state(vector_addr);
    Expr_ptr cht_height = transpile(this, call.args["cht_height"].expr);
    assert(cht_height);
    Expr_ptr backend_capacity = transpile(this, call.args["backend_capacity"].expr);
    assert(backend_capacity);

    args = std::vector<ExpressionType_ptr>{ vector, cht_height, backend_capacity };

    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);
    ret_symbol = "cht_fill_cht_successful";
  }

  else {
    std::cerr << call.function_name << "\n";

    for (const auto& arg : call.args) {
      std::cerr << arg.first << " : "
                << expr_to_string(arg.second.expr) << "\n";
      if (!arg.second.in.isNull()) {
        std::cerr << "  in:  " << expr_to_string(arg.second.in) << "\n";
      }
      if (!arg.second.out.isNull()) {
        std::cerr << "  out: " << expr_to_string(arg.second.out) << "\n";
      }
    }

    for (const auto& ev : call.extra_vars) {
      std::cerr << ev.first << " : "
                << expr_to_string(ev.second.first) << " | "
                << expr_to_string(ev.second.second) << "\n";
    }

    std::cerr << expr_to_string(call.ret) << "\n";

    assert(false && "Not implemented");
  }

  fname = translate_fname(fname, target);
  assert(args.size() == call.args.size());

  FunctionCall_ptr fcall = FunctionCall::build(fname, args, ret_type);

  if (ret_type->get_primitive_kind() != PrimitiveType::PrimitiveKind::VOID) {
    assert(ret_symbol.size());

    Variable_ptr ret_var = generate_new_symbol(ret_symbol, ret_type);
    ret_var->set_wrap(false);
    push_to_local(ret_var);

    VariableDecl_ptr ret = VariableDecl::build(ret_var);
    Assignment_ptr assignment = Assignment::build(ret, fcall);
    assignment->set_terminate_line(true);

    return assignment;
  }

  return fcall;
}

Node_ptr AST::process_state_node_from_call(call_t call, TargetOption target) {
  auto fname = call.function_name;

  std::vector<Expr_ptr> exprs;
  std::vector<ExpressionType_ptr> args;

  Type_ptr ret_type;
  std::string ret_symbol;
  klee::ref<klee::Expr> ret_expr;
  std::pair<bool, uint64_t> ret_addr;

  int counter_begins = 0;
  bool ignore = false;

  bool check_write_attempt = false;
  bool write_attempt = false;

  if (fname == "current_time") {
    associate_expr_to_local("now", call.ret);
    ignore = true;
  }

  else if (fname == "packet_borrow_next_chunk") {
    // rename fname
    fname = "nf_borrow_next_chunk";

    Expr_ptr chunk_expr = transpile(this, call.args["chunk"].out);
    assert(chunk_expr->get_kind() == Node::NodeKind::CONSTANT);
    ret_addr = std::pair<bool, uint64_t>(true, static_cast<Constant*>(chunk_expr.get())->get_value());

    Variable_ptr p = get_from_local("p");
    assert(p);
    Expr_ptr pkt_len = transpile(this, call.args["length"].expr);

    switch (layer.back()) {
    case 2: {
      Array_ptr _uint8_t_6 = Array::build(PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT8_T), 6);

      std::vector<Variable_ptr> ether_addr_fields{
        Variable::build("addr_bytes", _uint8_t_6)
      };

      Struct_ptr ether_addr = Struct::build("ether_addr", ether_addr_fields);

      std::vector<Variable_ptr> ether_hdr_fields {
        Variable::build("d_addr", ether_addr),
        Variable::build("s_addr", ether_addr),
        Variable::build("ether_type", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T))
      };

      Struct_ptr ether_hdr = Struct::build("rte_ether_hdr", ether_hdr_fields);

      ret_type = Pointer::build(ether_hdr);
      ret_symbol = CHUNK_LAYER_2;

      layer.back()++;
      break;
    }
    case 3: {
      std::vector<Variable_ptr> ipv4_hdr_fields {
        Variable::build("version_ihl", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT8_T)),
        Variable::build("type_of_service", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT8_T)),
        Variable::build("total_length", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T)),
        Variable::build("packet_id", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T)),
        Variable::build("fragment_offset", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T)),
        Variable::build("time_to_live", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT8_T)),
        Variable::build("next_proto_id", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT8_T)),
        Variable::build("hdr_checksum", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T)),
        Variable::build("src_addr", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT32_T)),
        Variable::build("dst_addr", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT32_T))
      };

      Struct_ptr ipv4_hdr = Struct::build("rte_ipv4_hdr", ipv4_hdr_fields);

      ret_type = Pointer::build(ipv4_hdr);
      ret_symbol = CHUNK_LAYER_3;

      layer.back()++;
      break;
    }
    case 4: {
      if (pkt_len->get_kind() != Node::NodeKind::CONSTANT) {
        ret_type = Pointer::build(PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT8_T));
        ret_symbol = "ip_options";
        break;
      }

      std::vector<Variable_ptr> tcpudp_hdr_fields {
        Variable::build("src_port", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T)),
        Variable::build("dst_port", PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T))
      };

      Struct_ptr tcpudp_hdr = Struct::build("tcpudp_hdr", tcpudp_hdr_fields);

      ret_type = Pointer::build(tcpudp_hdr);
      ret_symbol = CHUNK_LAYER_4;

      layer.back()++;
      break;
    }
    default: {
      assert(false && "Missing layers implementation");
    }
    }

    ret_expr = call.extra_vars["the_chunk"].second;
    args = std::vector<ExpressionType_ptr>{ p, pkt_len };
  }

  else if (fname == "packet_get_unread_length") {
    Variable_ptr p = get_from_local("p");
    assert(p);

    args = std::vector<ExpressionType_ptr>{ p };
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T);
    ret_symbol = "unread_len";
    ret_expr = call.ret;
  }

  else if (fname == "expire_items_single_map") {
    check_write_attempt = true;

    Expr_ptr chain_expr = transpile(this, call.args["chain"].expr);
    assert(chain_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t chain_addr = (static_cast<Constant*>(chain_expr.get()))->get_value();

    Expr_ptr vector_expr = transpile(this, call.args["vector"].expr);
    assert(vector_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t vector_addr = (static_cast<Constant*>(vector_expr.get()))->get_value();

    Expr_ptr map_expr = transpile(this, call.args["map"].expr);
    assert(map_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t map_addr = (static_cast<Constant*>(map_expr.get()))->get_value();

    Variable_ptr chain = get_from_state(chain_addr);
    Variable_ptr vector = get_from_state(vector_addr);
    Variable_ptr map = get_from_state(map_addr);
    Expr_ptr now = transpile(this, call.args["time"].expr);
    assert(now);

    args = std::vector<ExpressionType_ptr>{ chain, vector, map, now };
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);
    ret_symbol = "unmber_of_freed_flows";
    ret_expr = call.ret;
  }

  else if (fname == "map_get") {
    Expr_ptr map_expr = transpile(this, call.args["map"].expr);
    assert(map_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t map_addr = (static_cast<Constant*>(map_expr.get()))->get_value();

    Type_ptr key_type = type_from_klee_expr(call.args["key"].in, true);
    Variable_ptr key = generate_new_symbol("map_key", key_type);
    push_to_local(key);

    VariableDecl_ptr key_decl = VariableDecl::build(key);
    exprs.push_back(key_decl);

    auto statements = build_and_fill_byte_array(this, key, call.args["key"].in);
    assert(statements.size());
    exprs.insert(exprs.end(), statements.begin(), statements.end());

    Expr_ptr map = get_from_state(map_addr);

    Type_ptr value_out_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);
    Variable_ptr value_out = generate_new_symbol("value_out", value_out_type);

    assert(!call.args["value_out"].out.isNull());
    push_to_local(value_out, call.args["value_out"].out);

    VariableDecl_ptr value_out_decl = VariableDecl::build(value_out);
    exprs.push_back(value_out_decl);

    args = std::vector<ExpressionType_ptr>{ map, AddressOf::build(key), AddressOf::build(value_out) };
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);
    ret_symbol = "map_has_this_key";
    ret_expr = call.ret;
  }

  else if (fname == "dchain_allocate_new_index") {
    check_write_attempt = true;
    
    Expr_ptr chain_expr = transpile(this, call.args["chain"].expr);
    assert(chain_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t chain_addr = (static_cast<Constant*>(chain_expr.get()))->get_value();

    Expr_ptr chain = get_from_state(chain_addr);
    assert(chain);

    Variable_ptr index_out = generate_new_symbol(call.args["index_out"].out);
    assert(index_out);
    push_to_local(index_out, call.args["index_out"].out);

    Expr_ptr now = transpile(this, call.args["time"].expr);
    assert(now);

    VariableDecl_ptr index_out_decl = VariableDecl::build(index_out);
    exprs.push_back(index_out_decl);

    std::string suffix;

    if (index_out->get_symbol().find_last_of("_") != std::string::npos) {
      std::string counter = index_out->get_symbol().substr(index_out->get_symbol().find_last_of("_") + 1);
      suffix = "_" + counter;
    }

    args = std::vector<ExpressionType_ptr>{ chain, AddressOf::build(index_out), now };
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);
    ret_symbol = "out_of_space" + suffix;
    ret_expr = call.ret;
    counter_begins = -1;
  }

  else if (fname == "vector_borrow") {
    assert(!call.args["val_out"].out.isNull());

    Expr_ptr vector_expr = transpile(this, call.args["vector"].expr);
    assert(vector_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t vector_addr = (static_cast<Constant*>(vector_expr.get()))->get_value();

    Expr_ptr val_out_expr = transpile(this, call.args["val_out"].out);
    assert(val_out_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t val_out_addr = (static_cast<Constant*>(val_out_expr.get()))->get_value();

    Expr_ptr vector = get_from_state(vector_addr);
    Expr_ptr index = transpile(this, call.args["index"].expr);
    assert(index);

    Type_ptr val_out_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT8_T);
    Variable_ptr val_out = generate_new_symbol("val_out", val_out_type, 1, 0);
    val_out->set_addr(val_out_addr);

    assert(!call.extra_vars["borrowed_cell"].second.isNull());
    push_to_local(val_out, call.extra_vars["borrowed_cell"].second);

    VariableDecl_ptr val_out_decl = VariableDecl::build(val_out);
    Expr_ptr zero = Constant::build(PrimitiveType::PrimitiveKind::UINT32_T, 0);
    exprs.push_back(Assignment::build(val_out_decl, zero));

    Type_ptr val_out_type_arg = Pointer::build(Pointer::build(PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID)));
    Expr_ptr val_out_arg = AddressOf::build(val_out);
    Cast_ptr val_out_cast = Cast::build(val_out_arg, val_out_type_arg);

    args = std::vector<ExpressionType_ptr>{ vector, index, val_out_cast };
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID);
  }

  else if (fname == "map_put") {
    check_write_attempt = true;

    Expr_ptr map_expr = transpile(this, call.args["map"].expr);
    assert(map_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t map_addr = (static_cast<Constant*>(map_expr.get()))->get_value();

    Expr_ptr map = get_from_state(map_addr);
    
    Type_ptr key_type = type_from_klee_expr(call.args["key"].in, true);
    Variable_ptr key = generate_new_symbol("map_key", key_type);
    push_to_local(key);

    VariableDecl_ptr key_decl = VariableDecl::build(key);
    exprs.push_back(key_decl);

    auto statements = build_and_fill_byte_array(this, key, call.args["key"].in);
    assert(statements.size());
    exprs.insert(exprs.end(), statements.begin(), statements.end());

    Expr_ptr value = transpile(this, call.args["value"].expr);
    assert(value);

    args = std::vector<ExpressionType_ptr>{ map, AddressOf::build(key), value };
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID);
  }

  else if (fname == "vector_return") {
    Expr_ptr vector_expr = transpile(this, call.args["vector"].expr);
    assert(vector_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t vector_addr = (static_cast<Constant*>(vector_expr.get()))->get_value();

    Expr_ptr value_expr = transpile(this, call.args["value"].expr);
    assert(value_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t value_addr = (static_cast<Constant*>(value_expr.get()))->get_value();

    Expr_ptr vector = get_from_state(vector_addr);
    Expr_ptr index = transpile(this, call.args["index"].expr);
    assert(index);
    Expr_ptr value = get_from_local_by_addr("val_out", value_addr);
    assert(value);
    auto before_value = get_expr_from_local_by_addr(value_addr);

    auto changes = apply_changes(this, value, before_value, call.args["value"].in);

    write_attempt = changes.size();
    exprs.insert(exprs.end(), changes.begin(), changes.end());

    args = std::vector<ExpressionType_ptr>{ vector, index, value };
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID);
  }

  else if (fname == "dchain_rejuvenate_index") {
    Expr_ptr chain_expr = transpile(this, call.args["chain"].expr);
    assert(chain_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t chain_addr = (static_cast<Constant*>(chain_expr.get()))->get_value();

    Expr_ptr chain = get_from_state(chain_addr);
    assert(chain);
    Expr_ptr index = transpile(this, call.args["index"].expr);
    assert(index);
    Expr_ptr now = transpile(this, call.args["time"].expr);
    assert(now);

    args = std::vector<ExpressionType_ptr>{ chain, index, now };

    // actually this is an int, but we never use it in any call path...
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID);
  }

  else if (fname == "packet_return_chunk") {
    ignore = true;

    Expr_ptr chunk_expr = transpile(this, call.args["the_chunk"].expr);
    assert(chunk_expr->get_kind() == Node::NodeKind::CONSTANT);

    uint64_t chunk_addr = (static_cast<Constant*>(chunk_expr.get()))->get_value();

    klee::ref<klee::Expr> prev_chunk = get_expr_from_local_by_addr(chunk_addr);
    assert(!prev_chunk.isNull());

    auto eq = solver.are_exprs_always_equal(prev_chunk, call.args["the_chunk"].in);

    // changes to the chunk
    if (!eq) {
      std::vector<Expr_ptr> changes = apply_changes_to_match(this, prev_chunk, call.args["the_chunk"].in);
      exprs.insert(exprs.end(), changes.begin(), changes.end());
    }
  }

  else if (fname == "rte_ether_addr_hash") {
    assert(solver.are_exprs_always_equal(call.args["obj"].in, call.args["obj"].out));
    Expr_ptr obj = transpile(this, call.args["obj"].in);
    assert(obj);

    args = std::vector<ExpressionType_ptr>{ AddressOf::build(obj) };
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);
    ret_symbol = "hash";
    ret_expr = call.ret;
  }

  else if (fname == "dchain_is_index_allocated") {
    Expr_ptr chain_expr = transpile(this, call.args["chain"].expr);
    assert(chain_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t chain_addr = (static_cast<Constant*>(chain_expr.get()))->get_value();

    Expr_ptr chain = get_from_state(chain_addr);
    assert(chain);
    Expr_ptr index = transpile(this, call.args["index"].expr);
    assert(index);

    args = std::vector<ExpressionType_ptr>{ chain, index };

    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT32_T);
    ret_symbol = "is_index_allocated";
    ret_expr = call.ret;
  }

  else if (fname == "LoadBalancedFlow_hash") {
    Expr_ptr obj = transpile(this, call.args["obj"].in);
    assert(obj);

    args = std::vector<ExpressionType_ptr>{ obj };

    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT32_T);
    ret_symbol = "load_balanced_flow_hash";
    ret_expr = call.ret;
  }

  else if (fname == "cht_find_preferred_available_backend") {
    Expr_ptr hash = transpile(this, call.args["hash"].expr);
    assert(hash);

    Expr_ptr cht_expr = transpile(this, call.args["cht"].expr);
    assert(cht_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t cht_addr = (static_cast<Constant*>(cht_expr.get()))->get_value();

    Expr_ptr cht = get_from_state(cht_addr);
    assert(cht);

    Expr_ptr active_backends_expr = transpile(this, call.args["active_backends"].expr);
    assert(active_backends_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t active_backends_addr = (static_cast<Constant*>(active_backends_expr.get()))->get_value();

    Expr_ptr active_backends = get_from_state(active_backends_addr);
    assert(active_backends);

    Expr_ptr cht_height = transpile(this, call.args["cht_height"].expr);
    assert(cht_height);

    Expr_ptr backend_capacity = transpile(this, call.args["backend_capacity"].expr);
    assert(backend_capacity);

    Variable_ptr chosen_backend = generate_new_symbol(call.args["chosen_backend"].out);

    Expr_ptr chosen_backend_expr = transpile(this, call.args["chosen_backend"].expr);
    assert(chosen_backend_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t chosen_backend_addr = (static_cast<Constant*>(chosen_backend_expr.get()))->get_value();
    chosen_backend->set_addr(chosen_backend_addr);
    push_to_local(chosen_backend, call.args["chosen_backend"].out);

    VariableDecl_ptr chosen_backend_decl = VariableDecl::build(chosen_backend);
    Expr_ptr zero = Constant::build(PrimitiveType::PrimitiveKind::UINT32_T, 0);
    exprs.push_back(Assignment::build(chosen_backend_decl, zero));

    args = std::vector<ExpressionType_ptr>{ hash, cht, active_backends, cht_height, backend_capacity, AddressOf::build(chosen_backend) };

    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT32_T);
    ret_symbol = "prefered_backend_found";
    ret_expr = call.ret;
  }

  else if (fname == "nf_set_rte_ipv4_udptcp_checksum") {
    Expr_ptr ip_header_expr = transpile(this, call.args["ip_header"].expr);
    assert(ip_header_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t ip_header_addr = (static_cast<Constant*>(ip_header_expr.get()))->get_value();

    Expr_ptr l4_header_expr = transpile(this, call.args["l4_header"].expr);
    assert(l4_header_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t l4_header_addr = (static_cast<Constant*>(l4_header_expr.get()))->get_value();

    Expr_ptr ip_header = get_from_local_by_addr("rte_ipv4_hdr", ip_header_addr);
    assert(ip_header);
    Expr_ptr l4_header = get_from_local_by_addr("tcpudp_hdr", l4_header_addr);
    assert(l4_header);
    Expr_ptr packet = get_from_local("p");
    assert(packet);

    fname = "rte_ipv4_udptcp_cksum";
    args = std::vector<ExpressionType_ptr>{ ip_header, l4_header };
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);
    ret_symbol = "checksum";
  }

  else if (fname == "map_erase") {
    check_write_attempt = true;

    Expr_ptr map_expr = transpile(this, call.args["map"].expr);
    assert(map_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t map_addr = (static_cast<Constant*>(map_expr.get()))->get_value();

    Expr_ptr map = get_from_state(map_addr);
    
    Type_ptr key_type = type_from_klee_expr(call.args["key"].in, true);
    Variable_ptr key = generate_new_symbol("map_key", key_type);
    push_to_local(key);

    VariableDecl_ptr key_decl = VariableDecl::build(key);
    exprs.push_back(key_decl);

    auto statements = build_and_fill_byte_array(this, key, call.args["key"].in);
    assert(statements.size());
    exprs.insert(exprs.end(), statements.begin(), statements.end());

    Expr_ptr trash = transpile(this, call.args["trash"].expr);
    assert(trash);

    Type_ptr trash_type_arg = Pointer::build(Pointer::build(PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID)));
    Expr_ptr trash_arg = AddressOf::build(trash);
    Cast_ptr trash_cast = Cast::build(trash_arg, trash_type_arg);

    args = std::vector<ExpressionType_ptr>{ map, AddressOf::build(key), trash_cast };
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID);
  }

  else if (fname == "dchain_free_index") {
    check_write_attempt = true;

    Expr_ptr chain_expr = transpile(this, call.args["chain"].expr);
    assert(chain_expr->get_kind() == Node::NodeKind::CONSTANT);
    uint64_t chain_addr = (static_cast<Constant*>(chain_expr.get()))->get_value();

    Expr_ptr chain = get_from_state(chain_addr);
    assert(chain);
    Expr_ptr index = transpile(this, call.args["index"].expr);
    assert(index);

    args = std::vector<ExpressionType_ptr>{ chain, index };

    // actually this is an int, but we never use it in any call path...
    ret_type = PrimitiveType::build(PrimitiveType::PrimitiveKind::VOID);
  }

  else {
    std::cerr << call.function_name << "\n";

    for (const auto& arg : call.args) {
      std::cerr << arg.first << " : "
                << expr_to_string(arg.second.expr) << "\n";
      if (!arg.second.in.isNull()) {
        std::cerr << "  in:  " << expr_to_string(arg.second.in) << "\n";
      }
      if (!arg.second.out.isNull()) {
        std::cerr << "  out: " << expr_to_string(arg.second.out) << "\n";
      }
    }

    for (const auto& ev : call.extra_vars) {
      std::cerr << ev.first << " : "
                << expr_to_string(ev.second.first) << " | "
                << expr_to_string(ev.second.second) << "\n";
    }

    std::cerr << expr_to_string(call.ret) << "\n";

    assert(false && "Not implemented");
  }

  fname = translate_fname(fname, target);

  if (!ignore) {
    assert(call.function_name != fname || args.size() == call.args.size());
    FunctionCall_ptr fcall = FunctionCall::build(fname, args, ret_type);

    bool is_void = false;

    if (ret_type->get_type_kind() == Type::TypeKind::PRIMITIVE) {
      PrimitiveType* primitive = static_cast<PrimitiveType*>(ret_type.get());
      is_void = primitive->get_primitive_kind() == PrimitiveType::PrimitiveKind::VOID;
    }

    if (!is_void) {
      assert(ret_symbol.size());

      Variable_ptr ret_var;

      if (counter_begins >= 0) {
        ret_var = generate_new_symbol(ret_symbol, ret_type, 0, counter_begins);
      } else {
        ret_var = Variable::build(ret_symbol, ret_type);
      }

      if (!ret_expr.isNull()) {
        push_to_local(ret_var, ret_expr);
      } else {
        push_to_local(ret_var);
      }

      if (ret_addr.first) {
        ret_var->set_addr(ret_addr.second);
      }

      VariableDecl_ptr ret = VariableDecl::build(ret_var);
      Assignment_ptr assignment = Assignment::build(ret, fcall);

      exprs.push_back(assignment);
    }

    else {
      exprs.push_back(fcall);
    }
  }

  for (auto expr : exprs) {
    expr->set_terminate_line(true);
    expr->set_wrap(false);
  }

  if (exprs.size() == 0) {
    return nullptr;
  }

  std::vector<Node_ptr> nodes;

  if (target == LOCKS && write_attempt) {
    nodes.push_back(AST::write_attempt());
  }

  nodes.insert(nodes.end(), exprs.begin(), exprs.end());

  if (target == LOCKS && check_write_attempt) {
    nodes.push_back(AST::check_write_attempt());
  }

  return Block::build(nodes, false);
}

void AST::push() {
  local_variables.emplace_back();
  layer.push_back(layer.back());
}

void AST::pop() {
  assert(local_variables.size() > 0);
  local_variables.pop_back();

  assert(layer.size() > 1);
  layer.pop_back();
}

Node_ptr AST::node_from_call(call_t call, TargetOption target) {
  switch (context) {
  case INIT: return init_state_node_from_call(call, target);
  case PROCESS: return process_state_node_from_call(call, target);
  case DONE: assert(false);
  }

  return nullptr;
}

void AST::context_switch(Context ctx) {
  context = ctx;

  switch (context) {
  case INIT:
    push();
    break;

  case PROCESS: {
    pop();
    push();

    std::vector<VariableDecl_ptr> args {
      VariableDecl::build(from_cp_symbol("src_devices"), PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T)),
      VariableDecl::build(from_cp_symbol("p"), Pointer::build(PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT8_T))),
      VariableDecl::build(from_cp_symbol("pkt_len"), PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T)),
      VariableDecl::build(from_cp_symbol("now"), PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT64_T))
    };

    for (const auto& arg : args) {
      push_to_local(Variable::build(arg->get_symbol(), arg->get_type()));
    }

    break;
  }

  case DONE:
    pop();
    break;
  }

}

void AST::commit(Node_ptr body) {
  Block_ptr _body = Block::build(body);

  switch (context) {
  case INIT: {
    std::vector<FunctionArgDecl_ptr> _args;
    Type_ptr _return = PrimitiveType::build(PrimitiveType::PrimitiveKind::BOOL);

    nf_init = Function::build("nf_init", _args, _body, _return);

    context_switch(PROCESS);
    break;
  }

  case PROCESS: {
    std::vector<FunctionArgDecl_ptr> _args{
      FunctionArgDecl::build(from_cp_symbol("src_devices"), PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T)),
      FunctionArgDecl::build(from_cp_symbol("p"), Pointer::build(PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT8_T))),
      FunctionArgDecl::build(from_cp_symbol("pkt_len"), PrimitiveType::build(PrimitiveType::PrimitiveKind::UINT16_T)),
      FunctionArgDecl::build(from_cp_symbol("now"), PrimitiveType::build(PrimitiveType::PrimitiveKind::INT64_T)),
    };

    Type_ptr _return = PrimitiveType::build(PrimitiveType::PrimitiveKind::INT);

    nf_process = Function::build("nf_process", _args, _body, _return);

    context_switch(DONE);
    break;
  }

  case DONE:
    assert(false);
  }
}
