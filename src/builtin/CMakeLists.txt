# This directory contains Lean builtin libraries and Lua scripts
# needed to run Lean. The builtin Lean libraries are compiled
# using ${LEAN_BINARY_DIR}/shell/lean
# The library builtin is not a real library.
# It is just a hack to force CMake to consider our custom targets
add_library(builtin builtin.cpp)

# We copy files to the shell directory, to make sure we can test lean
# without installing it.
set(SHELL_DIR ${LEAN_BINARY_DIR}/shell)

file(GLOB LEANLIB "*.lean")
FOREACH(FILE ${LEANLIB})
  get_filename_component(BASENAME ${FILE} NAME_WE)
  set(FNAME "${BASENAME}.olean")
  add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${FNAME}
    COMMAND ${SHELL_DIR}/lean -o ${CMAKE_CURRENT_BINARY_DIR}/${FNAME} ${FILE}
    COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_BINARY_DIR}/${FNAME} ${SHELL_DIR}/${FNAME}
    DEPENDS ${FILE} ${SHELL_DIR}/lean)
  add_custom_target(${FNAME}_builtin DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${FNAME})
  add_dependencies(builtin ${FNAME}_builtin)
  install(FILES ${CMAKE_CURRENT_BINARY_DIR}/${FNAME} DESTINATION library)
ENDFOREACH(FILE)

file(GLOB LEANLIB "*.lua")
FOREACH(FILE ${LEANLIB})
  get_filename_component(FNAME ${FILE} NAME)
  add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${FNAME}
    COMMAND ${CMAKE_COMMAND} -E copy ${FILE} ${CMAKE_CURRENT_BINARY_DIR}/${FNAME}
    COMMAND ${CMAKE_COMMAND} -E copy ${FILE} ${SHELL_DIR}/${FNAME}
    DEPENDS ${FILE})
  add_custom_target("${FNAME}_builtin" DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${FNAME})
  add_dependencies(builtin "${FNAME}_builtin")
  install(FILES ${CMAKE_CURRENT_BINARY_DIR}/${FNAME} DESTINATION library)
ENDFOREACH(FILE)
