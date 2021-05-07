#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(bdd-to-c
  bdd-to-c.cpp
  nodes.cpp
  ast.cpp
  klee_transpiler.cpp
  ../load-call-paths/load-call-paths.cpp
  ../call-paths-to-bdd/call-paths-to-bdd.cpp
  ../printer/printer.cpp
)

set(KLEE_LIBS
  kleaverExpr
  kleeCore
)

target_include_directories(bdd-to-c PRIVATE ../load-call-paths ../call-paths-to-bdd ../printer)
target_link_libraries(bdd-to-c ${KLEE_LIBS})

install(TARGETS bdd-to-c RUNTIME DESTINATION bin)
