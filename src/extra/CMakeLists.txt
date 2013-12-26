file(GLOB LEANLIB "${LEAN_SOURCE_DIR}/extra/*.lean")
FOREACH(FILE ${LEANLIB})
   install_files(/library FILES ${FILE})
ENDFOREACH(FILE)

file(GLOB LEANLIB "${LEAN_SOURCE_DIR}/extra/*.lua")
FOREACH(FILE ${LEANLIB})
   install_files(/library FILES ${FILE})
ENDFOREACH(FILE)
