#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(printer
  printer.cpp
  main.cpp
)

set(KLEE_LIBS
  kleaverExpr
  kleeCore
)

target_link_libraries(printer ${KLEE_LIBS})

install(TARGETS printer RUNTIME DESTINATION bin)
