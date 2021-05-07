/* -*- mode: c++; c-basic-offset: 2; -*- */

//===-- ktest-dehavoc.cpp ---------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Support/MemoryBuffer.h"
#include "klee/ExprBuilder.h"
#include "klee/perf-contracts.h"
#include <klee/Constraints.h>
#include <klee/Solver.h>

#include <dlfcn.h>
#include <expr/Parser.h>
#include <fstream>
#include <iostream>
#include <vector>

#include "load-call-paths.h"

#define DEBUG

call_path_t *load_call_path(std::string file_name,
                            std::vector<std::string> expressions_str,
                            std::deque<klee::ref<klee::Expr> > &expressions) {
  std::ifstream call_path_file(file_name);
  assert(call_path_file.is_open() && "Unable to open call path file.");

  call_path_t *call_path = new call_path_t;
  call_path->file_name = file_name;

  enum {
    STATE_INIT,
    STATE_KQUERY,
    STATE_CALLS,
    STATE_CALLS_MULTILINE,
    STATE_DONE
  } state = STATE_INIT;

  std::string kQuery;
  std::vector<klee::ref<klee::Expr> > exprs;
  std::set<std::string> declared_arrays;

  int parenthesis_level = 0;

  std::string current_extra_var;
  std::string current_arg;
  std::string current_arg_name;

  std::string current_expr_str;
  std::vector<std::string> current_exprs_str;

  while (!call_path_file.eof()) {
    std::string line;
    std::getline(call_path_file, line);

    switch (state) {
    case STATE_INIT: {
      if (line == ";;-- kQuery --") {
        state = STATE_KQUERY;
      }
    } break;

    case STATE_KQUERY: {
      if (line == ";;-- Calls --") {
        if (kQuery.substr(kQuery.length() - 2) == "])") {
          kQuery = kQuery.substr(0, kQuery.length() - 2) + "\n";

          for (auto eit : expressions_str) {
            kQuery += "\n         " + eit;
          }
          kQuery += "])";
        } else if (kQuery.substr(kQuery.length() - 6) == "false)") {
          kQuery = kQuery.substr(0, kQuery.length() - 1) + " [\n";

          for (auto eit : expressions_str) {
            kQuery += "\n         " + eit;
          }
          kQuery += "])";
        }

        llvm::MemoryBuffer *MB = llvm::MemoryBuffer::getMemBuffer(kQuery);
        klee::ExprBuilder *Builder = klee::createDefaultExprBuilder();
        klee::expr::Parser *P =
            klee::expr::Parser::Create("", MB, Builder, false);
        while (klee::expr::Decl *D = P->ParseTopLevelDecl()) {
          assert(!P->GetNumErrors() &&
                 "Error parsing kquery in call path file.");
          if (klee::expr::ArrayDecl *AD = dyn_cast<klee::expr::ArrayDecl>(D)) {
            call_path->arrays[AD->Root->name] = AD->Root;
          } else if (klee::expr::QueryCommand *QC =
                         dyn_cast<klee::expr::QueryCommand>(D)) {
            call_path->constraints = klee::ConstraintManager(QC->Constraints);
            exprs = QC->Values;
            break;
          }
        }

        state = STATE_CALLS;
      } else {
        kQuery += "\n" + line;

        if (line.substr(0, sizeof("array ") - 1) == "array ") {
          std::string array_name = line.substr(sizeof("array "));
          size_t delim = array_name.find("[");
          assert(delim != std::string::npos);
          array_name = array_name.substr(0, delim);
          declared_arrays.insert(array_name);
        }
      }
      break;

    case STATE_CALLS:
      if (line == ";;-- Constraints --") {
        for (size_t i = 0; i < expressions_str.size(); i++) {
          assert(!exprs.empty() && "Too few expressions in kQuery.");
          expressions.push_back(exprs.front());
          exprs.erase(exprs.begin());
        }

        assert(exprs.empty() && "Too many expressions in kQuery.");

        state = STATE_DONE;
      } else {
        size_t delim = line.find(":");
        assert(delim != std::string::npos);
        std::string preamble = line.substr(0, delim);
        line = line.substr(delim + 1);

        current_extra_var.clear();
        current_exprs_str.clear();

        if (preamble == "extra") {
          while (line[0] == ' ') {
            line = line.substr(1);
          }

          delim = line.find("&");
          assert(delim != std::string::npos);
          current_extra_var = line.substr(0, delim);
          line = line.substr(delim + 1);

          delim = line.find("[");
          assert(delim != std::string::npos);
          line = line.substr(delim + 1);
        } else {
          call_path->calls.emplace_back();

          delim = line.find("(");
          assert(delim != std::string::npos);
          call_path->calls.back().function_name = line.substr(0, delim);
        }

        for (char c : line) {
          current_expr_str += c;
          if (c == '(') {
            if (parenthesis_level == 0) {
              current_expr_str = "(";
            }
            parenthesis_level++;
          } else if (c == ')') {
            parenthesis_level--;
            assert(parenthesis_level >= 0);

            if (parenthesis_level == 0) {
              current_exprs_str.push_back(current_expr_str);
            }
          }
        }

        if (current_exprs_str.size() && parenthesis_level == 0) {
          auto last_store = current_exprs_str.back();
          if (line.size() < last_store.size())
            last_store = last_store.substr(last_store.size() - line.size());
          auto remainder_delim = line.find(last_store);
          auto remainder = line.substr(remainder_delim+last_store.size());
          auto ret_symbol = std::string("-> ");
          auto ret_delim = remainder.find(ret_symbol);
          if (ret_delim != std::string::npos && remainder.substr(ret_symbol.size()+1) != "[]") {
            auto ret = remainder.substr(ret_symbol.size()+1);
            current_exprs_str.push_back(ret);
          }
        }

        if (parenthesis_level > 0) {
          state = STATE_CALLS_MULTILINE;
        } else {
          if (!current_extra_var.empty()) {
            assert(current_exprs_str.size() == 2 &&
                   "Too many expression in extra variable.");
            if (current_exprs_str[0] != "(...)") {
              assert(exprs.size() >= 1 && "Not enough expression in kQuery.");
              call_path->calls.back().extra_vars[current_extra_var].first =
                  exprs[0];
              exprs.erase(exprs.begin());
              current_exprs_str.erase(current_exprs_str.begin(), current_exprs_str.begin() + 2);
            }
            if (current_exprs_str[1] != "(...)") {
              assert(exprs.size() >= 1 && "Not enough expression in kQuery.");
              call_path->calls.back().extra_vars[current_extra_var].second =
                  exprs[0];
              exprs.erase(exprs.begin());
              current_exprs_str.erase(current_exprs_str.begin(), current_exprs_str.begin() + 2);
            }
          } else {
            bool parsed_last_arg = false;
            while (!parsed_last_arg) {
              if (current_exprs_str[0] == "()")
                break;
              delim = current_exprs_str[0].find(",");
              if (delim == std::string::npos) {
                delim = current_exprs_str[0].size() - 1;
                parsed_last_arg = true;
              }
              current_arg = current_exprs_str[0].substr(0, delim);
              if (current_arg[0] == '(')
                current_arg = current_arg.substr(1);
              current_exprs_str[0] = current_exprs_str[0].substr(delim + 1);
              delim = current_arg.find(":");
              assert(delim != std::string::npos);
              current_arg_name = current_arg.substr(0, delim);
              current_arg = current_arg.substr(delim + 1);

              delim = current_arg.find("&");
              if (delim == std::string::npos) {
                assert(exprs.size() >= 1 && "Not enough expression in kQuery.");
                call_path->calls.back().args[current_arg_name].expr = exprs[0];
                exprs.erase(exprs.begin(), exprs.begin() + 1);
              } else {
                call_path->calls.back().args[current_arg_name].expr = exprs[0];
                exprs.erase(exprs.begin(), exprs.begin() + 1);

                if (current_arg.substr(delim + 1) == "[...]") {
                    continue;
                }

                if (current_arg.substr(delim + 1)[0] != '[') {
                  call_path->calls.back().args[current_arg_name].fn_ptr_name =
                      std::make_pair(true, current_arg.substr(delim + 1));
                  continue;
                }

                current_arg = current_arg.substr(delim + 2);

                delim = current_arg.find("]");
                assert(delim != std::string::npos);

                current_arg = current_arg.substr(0, delim);

                delim = current_arg.find("->");
                assert(delim != std::string::npos);

                if (current_arg.substr(0, delim).size()) {
                  assert(exprs.size() >= 1 &&
                         "Not enough expression in kQuery.");
                  call_path->calls.back().args[current_arg_name].in = exprs[0];
                  exprs.erase(exprs.begin(), exprs.begin() + 1);
                }

                if (current_arg.substr(delim + 2).size()) {
                  assert(exprs.size() >= 1 &&
                         "Not enough expression in kQuery.");
                  call_path->calls.back().args[current_arg_name].out = exprs[0];
                  exprs.erase(exprs.begin(), exprs.begin() + 1);
                }
              }
            }
            current_exprs_str.erase(current_exprs_str.begin());
          }


          if (current_exprs_str.size()) {
            call_path->calls.back().ret = exprs[0];
            exprs.erase(exprs.begin());
          }
        }
      }
    } break;

    case STATE_CALLS_MULTILINE: {
      current_expr_str += " ";
      for (char c : line) {
        current_expr_str += c;
        if (c == '(') {
          if (parenthesis_level == 0) {
            current_expr_str = "(";
          }
          parenthesis_level++;
        } else if (c == ')') {
          parenthesis_level--;
          assert(parenthesis_level >= 0);

          if (parenthesis_level == 0) {
            current_exprs_str.push_back(current_expr_str);
          }
        }
      }

      if (current_exprs_str.size() && parenthesis_level == 0) {
        auto last_store = current_exprs_str.back();
        if (line.size() < last_store.size())
          last_store = last_store.substr(last_store.size() - line.size());
        auto remainder_delim = line.find(last_store);
        auto remainder = line.substr(remainder_delim+last_store.size());
        auto ret_symbol = std::string("-> ");
        auto ret_delim = remainder.find(ret_symbol);
        if (ret_delim != std::string::npos && remainder.substr(ret_symbol.size()+1) != "[]") {
          auto ret = remainder.substr(ret_symbol.size()+1);
          current_exprs_str.push_back(ret);
        }
      }

      if (parenthesis_level == 0) {
        if (!current_extra_var.empty()) {
          assert(current_exprs_str.size() == 2 &&
                 "Too many expression in extra variable.");
          if (current_exprs_str[0] != "(...)") {
            assert(exprs.size() >= 1 && "Not enough expression in kQuery.");
            call_path->calls.back().extra_vars[current_extra_var].first =
                exprs[0];
            exprs.erase(exprs.begin());
            current_exprs_str.erase(current_exprs_str.begin(), current_exprs_str.begin() + 2);
          }
          if (current_exprs_str[1] != "(...)") {
            assert(exprs.size() >= 1 && "Not enough expression in kQuery.");
            call_path->calls.back().extra_vars[current_extra_var].second =
                exprs[0];
            exprs.erase(exprs.begin());
            current_exprs_str.erase(current_exprs_str.begin(), current_exprs_str.begin() + 2);
          }
        } else {
          bool parsed_last_arg = false;
          size_t delim;

          while (!parsed_last_arg) {
            if (current_exprs_str[0] == "()")
              break;
            delim = current_exprs_str[0].find(",");
            if (delim == std::string::npos) {
              delim = current_exprs_str[0].size() - 1;
              parsed_last_arg = true;
            }
            current_arg = current_exprs_str[0].substr(0, delim);
            if (current_arg[0] == '(')
              current_arg = current_arg.substr(1);
            current_exprs_str[0] = current_exprs_str[0].substr(delim + 1);
            delim = current_arg.find(":");
            assert(delim != std::string::npos);
            current_arg_name = current_arg.substr(0, delim);
            current_arg = current_arg.substr(delim + 1);

            delim = current_arg.find("&");
            if (delim == std::string::npos) {
              assert(exprs.size() >= 1 && "Not enough expression in kQuery.");
              call_path->calls.back().args[current_arg_name].expr = exprs[0];
              exprs.erase(exprs.begin(), exprs.begin() + 1);
            } else {
              call_path->calls.back().args[current_arg_name].expr = exprs[0];
              exprs.erase(exprs.begin(), exprs.begin() + 1);

              if (current_arg.substr(delim + 1) == "[...]") {
                  continue;
              }

              if (current_arg.substr(delim + 1)[0] != '[') {
                call_path->calls.back().args[current_arg_name].fn_ptr_name =
                    std::make_pair(true, current_arg.substr(delim + 1));
                continue;
              }

              current_arg = current_arg.substr(delim + 2);

              delim = current_arg.find("]");
              assert(delim != std::string::npos);

              current_arg = current_arg.substr(0, delim);

              delim = current_arg.find("->");
              assert(delim != std::string::npos);

              if (current_arg.substr(0, delim).size()) {
                assert(exprs.size() >= 1 && "Not enough expression in kQuery.");
                call_path->calls.back().args[current_arg_name].in = exprs[0];
                exprs.erase(exprs.begin(), exprs.begin() + 1);
              }

              if (current_arg.substr(delim + 2).size()) {
                assert(exprs.size() >= 1 && "Not enough expression in kQuery.");
                call_path->calls.back().args[current_arg_name].out = exprs[0];
                exprs.erase(exprs.begin(), exprs.begin() + 1);
              }
            }
          }

          current_exprs_str.erase(current_exprs_str.begin());
        }


        if (current_exprs_str.size()) {
          call_path->calls.back().ret = exprs[0];
          exprs.erase(exprs.begin());
        }

        state = STATE_CALLS;
      }

      continue;
    } break;

    case STATE_DONE: {
      continue;
    } break;

    default: {
      assert(false && "Invalid call path file.");
    } break;
    }
  }

  return call_path;
}

