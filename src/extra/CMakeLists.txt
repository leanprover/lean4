add_library(extra extra.cpp)

file(GLOB LEANLIB "${LEAN_SOURCE_DIR}/extra/*.lean")
FOREACH(FILE ${LEANLIB})
  get_filename_component(BASENAME ${FILE} NAME_WE)
  set(FNAME "${BASENAME}.olean")
  add_custom_command(OUTPUT ${LEAN_BINARY_DIR}/extra/${FNAME}
    COMMAND ${LEAN_BINARY_DIR}/shell/lean -o ${LEAN_BINARY_DIR}/extra/${FNAME} ${FILE}
    COMMAND ${CMAKE_COMMAND} -E copy ${LEAN_BINARY_DIR}/extra/${FNAME} ${LEAN_BINARY_DIR}/shell/${FNAME}
    DEPENDS ${FILE} ${LEAN_BINARY_DIR}/shell/lean)
  add_custom_target(${FNAME}_extra DEPENDS ${LEAN_BINARY_DIR}/extra/${FNAME})
  add_dependencies(extra ${FNAME}_extra)
  install(FILES ${LEAN_BINARY_DIR}/extra/${FNAME} DESTINATION library)
ENDFOREACH(FILE)

file(GLOB LEANLIB "${LEAN_SOURCE_DIR}/extra/*.lua")
FOREACH(FILE ${LEANLIB})
  get_filename_component(FNAME ${FILE} NAME)
  add_custom_command(OUTPUT ${LEAN_BINARY_DIR}/extra/${FNAME}
    COMMAND ${CMAKE_COMMAND} -E copy ${FILE} ${LEAN_BINARY_DIR}/extra/${FNAME}
    COMMAND ${CMAKE_COMMAND} -E copy ${FILE} ${LEAN_BINARY_DIR}/shell/${FNAME}
    DEPENDS ${FILE})
  add_custom_target("${FNAME}_extra" DEPENDS ${LEAN_BINARY_DIR}/extra/${FNAME})
  add_dependencies(extra "${FNAME}_extra")
  install(FILES ${LEAN_BINARY_DIR}/extra/${FNAME} DESTINATION library)
ENDFOREACH(FILE)
