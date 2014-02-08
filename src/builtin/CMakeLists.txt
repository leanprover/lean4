# This directory contains Lean builtin libraries and Lua scripts
# needed to run Lean. The builtin Lean libraries are compiled
# using ${LEAN_BINARY_DIR}/shell/lean
# The library builtin is not a real library.
# It is just a hack to force CMake to consider our custom targets
add_library(builtin builtin.cpp)

# We copy files to the shell directory, to make sure we can test lean
# without installing it.
set(SHELL_DIR ${LEAN_BINARY_DIR}/shell)

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

# The following command invokes the lean binary.
# So, it CANNOT be executed if we are cross-compiling.
function(add_theory_core FILE ARG)
  set(EXTRA_DEPS ${ARGN})
  get_filename_component(BASENAME ${FILE} NAME_WE)
  set(FNAME "${BASENAME}.olean")
  add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${FNAME}
    COMMAND ${SHELL_DIR}/lean.sh ${ARG} -q -o ${CMAKE_CURRENT_BINARY_DIR}/${FNAME} ${CMAKE_CURRENT_SOURCE_DIR}/${FILE}
    COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_BINARY_DIR}/${FNAME} ${SHELL_DIR}/${FNAME}
    COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_BINARY_DIR}/${FNAME} ${CMAKE_CURRENT_SOURCE_DIR}/obj/${FNAME}
    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/${FILE} lean_sh ${EXTRA_DEPS})
  add_custom_target("${BASENAME}_builtin" DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${FNAME} ${EXTRA_DEPS})
  add_dependencies(builtin ${BASENAME}_builtin)
  install(FILES ${CMAKE_CURRENT_BINARY_DIR}/${FNAME} DESTINATION library)
  add_test("${BASENAME}_builtin_test" ${SHELL_DIR}/lean -o ${CMAKE_CURRENT_BINARY_DIR}/${FNAME}_test ${ARG} ${CMAKE_CURRENT_SOURCE_DIR}/${FILE})
endfunction()

# When cross compiling, we cannot execute lean during the build.
# So, we just copy the precompiled .olean files.
function(copy_olean FILE)
  get_filename_component(BASENAME ${FILE} NAME_WE)
  set(FNAME "${BASENAME}.olean")
  add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${FNAME}
    COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_SOURCE_DIR}/obj/${FNAME} ${CMAKE_CURRENT_BINARY_DIR}/${FNAME}
    COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_SOURCE_DIR}/obj/${FNAME} ${SHELL_DIR}/${FNAME}
    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/obj/${FNAME})
  add_custom_target("${BASENAME}_builtin" DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${FNAME})
  add_dependencies(builtin ${BASENAME}_builtin)
  install(FILES ${CMAKE_CURRENT_BINARY_DIR}/${FNAME} DESTINATION library)
endfunction()

function(add_kernel_theory FILE)
  if(CMAKE_CROSSCOMPILING)
    copy_olean(${FILE})
  else()
    add_theory_core(${FILE} "-n" ${ARGN})
  endif()
endfunction()

function(add_theory FILE)
  if(CMAKE_CROSSCOMPILING)
    copy_olean(${FILE})
  else()
    add_theory_core(${FILE} "" ${ARGN})
  endif()
endfunction()

# The following command invokes the lean binary to update .cpp/.h interface files
# associated with a .lean file.
function(update_interface FILE DEST ARG)
  get_filename_component(BASENAME ${FILE} NAME_WE)
  set(CPPFILE "${LEAN_SOURCE_DIR}/${DEST}/${BASENAME}_decls.cpp")
  set(HFILE "${LEAN_SOURCE_DIR}/${DEST}/${BASENAME}_decls.h")
  # We also create a fake .h file, it serves as the output for the following
  # custom command. We don't use CPPFILE and HFILE as the output to avoid
  # a cyclic dependency.
  set(HFILE_fake "${LEAN_BINARY_DIR}/${DEST}/${BASENAME}_fake.h")
  add_custom_command(OUTPUT ${HFILE_fake}
    COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/lean2cpp.sh "${SHELL_DIR}/lean.sh" "${CMAKE_CURRENT_SOURCE_DIR}" "${CMAKE_CURRENT_BINARY_DIR}/${FILE}" "${CPPFILE}" "${ARG}$"
    COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/lean2h.sh   "${SHELL_DIR}/lean.sh" "${CMAKE_CURRENT_SOURCE_DIR}" "${CMAKE_CURRENT_BINARY_DIR}/${FILE}" "${HFILE}"   "${ARG}$"
    COMMAND ${CMAKE_COMMAND} -E copy ${HFILE} ${HFILE_fake}
    DEPENDS ${FILE} lean_sh)
  add_custom_target("${BASENAME}_decls" DEPENDS ${HFILE_fake})
  add_dependencies(builtin ${BASENAME}_decls)
endfunction()

add_kernel_theory("kernel.lean"    ${CMAKE_CURRENT_BINARY_DIR}/macros.lua ${CMAKE_CURRENT_BINARY_DIR}/tactic.lua)
add_kernel_theory("Nat.lean"       ${CMAKE_CURRENT_BINARY_DIR}/kernel.olean)

add_theory("Int.lean"          "${CMAKE_CURRENT_BINARY_DIR}/Nat.olean")
add_theory("Real.lean"         "${CMAKE_CURRENT_BINARY_DIR}/Int.olean")
add_theory("specialfn.lean"    "${CMAKE_CURRENT_BINARY_DIR}/Real.olean")
add_theory("subtype.lean"      "${CMAKE_CURRENT_BINARY_DIR}/Nat.olean")
add_theory("optional.lean"     "${CMAKE_CURRENT_BINARY_DIR}/subtype.olean")
add_theory("sum.lean"          "${CMAKE_CURRENT_BINARY_DIR}/optional.olean")

update_interface("kernel.olean"       "kernel" "-n")
update_interface("Nat.olean"          "library/arith" "-n")
update_interface("Int.olean"          "library/arith" "")
update_interface("Real.olean"         "library/arith" "")
