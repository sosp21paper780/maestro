#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(call-paths-to-bdd
  call-paths-to-bdd.cpp
  main.cpp
  ../load-call-paths/load-call-paths.cpp
  ../printer/printer.cpp
)

set(KLEE_LIBS
  kleaverExpr
  kleeCore
)

target_include_directories(call-paths-to-bdd PRIVATE ../load-call-paths ../printer)
target_link_libraries(call-paths-to-bdd ${KLEE_LIBS})

install(TARGETS call-paths-to-bdd RUNTIME DESTINATION bin)
