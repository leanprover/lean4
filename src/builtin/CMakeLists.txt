add_library(builtin builtin.cpp)

file(GLOB LEANLIB "${LEAN_SOURCE_DIR}/builtin/*.lean")
FOREACH(FILE ${LEANLIB})
  get_filename_component(BASENAME ${FILE} NAME_WE)
  set(FNAME "${BASENAME}.olean")
  add_custom_command(OUTPUT ${LEAN_BINARY_DIR}/builtin/${FNAME}
    COMMAND ${LEAN_BINARY_DIR}/shell/lean -o ${LEAN_BINARY_DIR}/builtin/${FNAME} ${FILE}
    COMMAND ${CMAKE_COMMAND} -E copy ${LEAN_BINARY_DIR}/builtin/${FNAME} ${LEAN_BINARY_DIR}/shell/${FNAME}
    DEPENDS ${FILE} ${LEAN_BINARY_DIR}/shell/lean)
  add_custom_target(${FNAME}_builtin DEPENDS ${LEAN_BINARY_DIR}/builtin/${FNAME})
  add_dependencies(builtin ${FNAME}_builtin)
  install(FILES ${LEAN_BINARY_DIR}/builtin/${FNAME} DESTINATION library)
ENDFOREACH(FILE)

file(GLOB LEANLIB "${LEAN_SOURCE_DIR}/builtin/*.lua")
FOREACH(FILE ${LEANLIB})
  get_filename_component(FNAME ${FILE} NAME)
  add_custom_command(OUTPUT ${LEAN_BINARY_DIR}/builtin/${FNAME}
    COMMAND ${CMAKE_COMMAND} -E copy ${FILE} ${LEAN_BINARY_DIR}/builtin/${FNAME}
    COMMAND ${CMAKE_COMMAND} -E copy ${FILE} ${LEAN_BINARY_DIR}/shell/${FNAME}
    DEPENDS ${FILE})
  add_custom_target("${FNAME}_builtin" DEPENDS ${LEAN_BINARY_DIR}/builtin/${FNAME})
  add_dependencies(builtin "${FNAME}_builtin")
  install(FILES ${LEAN_BINARY_DIR}/builtin/${FNAME} DESTINATION library)
ENDFOREACH(FILE)
