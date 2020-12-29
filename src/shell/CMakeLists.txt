add_executable(lean lean.cpp)
set_target_properties(lean PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")
target_link_libraries(lean leancpp)

# create import library on Windows to link plugins against
set_target_properties(lean PROPERTIES ENABLE_EXPORTS ON)
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  # https://github.com/msys2/MINGW-packages/issues/5952
  target_link_options(lean PRIVATE "-Wl,--out-implib,${CMAKE_BINARY_DIR}/bin/lean.exe.a")
endif()
install(TARGETS lean DESTINATION bin)

# use executable of current stage for tests
string(REGEX REPLACE "^([a-zA-Z]):" "/\\1" LEAN_BIN "${CMAKE_BINARY_DIR}/bin")

add_test(lean_help1    "${CMAKE_BINARY_DIR}/bin/lean" --help)
add_test(lean_help2    "${CMAKE_BINARY_DIR}/bin/lean" -h)
add_test(lean_version1 "${CMAKE_BINARY_DIR}/bin/lean" --version)
if (NOT ${EMSCRIPTEN})
add_test(lean_version2 "${CMAKE_BINARY_DIR}/bin/lean" --v)
endif()
add_test(lean_ghash1   "${CMAKE_BINARY_DIR}/bin/lean" -g)
add_test(lean_ghash2   "${CMAKE_BINARY_DIR}/bin/lean" --githash)
add_test(lean_unknown_option bash "${LEAN_SOURCE_DIR}/cmake/check_failure.sh" "${CMAKE_BINARY_DIR}/bin/lean" "-z")
add_test(lean_unknown_file1 bash "${LEAN_SOURCE_DIR}/cmake/check_failure.sh" "${CMAKE_BINARY_DIR}/bin/lean" "boofoo.lean")

# LEAN TESTS
file(GLOB LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/*.lean")
FOREACH(T ${LEANTESTS})
  if(NOT T MATCHES "\\.#")
    GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
    add_test(NAME "leantest_${T_NAME}"
             WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
             COMMAND bash -c "PATH=${LEAN_BIN}:$PATH ./test_single.sh ${T_NAME}")
  endif()
ENDFOREACH(T)

# LEAN RUN TESTS
file(GLOB LEANRUNTESTS "${LEAN_SOURCE_DIR}/../tests/lean/run/*.lean")
FOREACH(T ${LEANRUNTESTS})
  if(NOT T MATCHES "\\.#")
    GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
    add_test(NAME "leanruntest_${T_NAME}"
             WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/run"
             COMMAND bash -c "PATH=${LEAN_BIN}:$PATH ./test_single.sh ${T_NAME}")
  endif()
ENDFOREACH(T)

# LEAN COMPILER TESTS
file(GLOB LEANCOMPTESTS "${LEAN_SOURCE_DIR}/../tests/compiler/*.lean")
FOREACH(T ${LEANCOMPTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leancomptest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/compiler"
           COMMAND bash -c "PATH=${LEAN_BIN}:$PATH ./test_single.sh ${T_NAME}")
ENDFOREACH(T)

add_test(NAME leancomptest_foreign
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/compiler/foreign"
         COMMAND bash -c "${LEAN_BIN}/leanmake --always-make && ./build/bin/test")
add_test(NAME leancomptest_doc_example
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../doc/examples/compiler"
         COMMAND bash -c "${LEAN_BIN}/leanmake --always-make bin && ./build/bin/test hello world")

# LEAN INTERPRETER TESTS
file(GLOB LEANINTERPTESTS "${LEAN_SOURCE_DIR}/../tests/compiler/*.lean")
FOREACH(T ${LEANINTERPTESTS})
  if(NOT EXISTS "${T}.no_interpreter")
    GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
    add_test(NAME "leaninterptest_${T_NAME}"
             WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/compiler"
             COMMAND bash -c "PATH=${LEAN_BIN}:$PATH ./test_single_interpret.sh ${T_NAME}")
  endif()
ENDFOREACH(T)

# LEAN BENCHMARK TESTS
# do not test all .lean files in bench/
file(GLOB LEANBENCHTESTS "${LEAN_SOURCE_DIR}/../tests/bench/*.lean.expected.out")
FOREACH(T_OUT ${LEANBENCHTESTS})
  string(REPLACE ".expected.out" "" T ${T_OUT})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanbenchtest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/bench"
           COMMAND bash -c "PATH=${LEAN_BIN}:$PATH ./test_single.sh ${T_NAME}")
ENDFOREACH(T_OUT)

# LEAN PLUGIN TESTS
file(GLOB LEANINTERPTESTS "${LEAN_SOURCE_DIR}/../tests/plugin/*.lean")
FOREACH(T ${LEANINTERPTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanplugintest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/plugin"
           COMMAND bash -c "PATH=${LEAN_BIN}:$PATH ./test_single.sh ${T_NAME}")
ENDFOREACH(T)

# LEAN TESTS using --trust=0
file(GLOB LEANT0TESTS "${LEAN_SOURCE_DIR}/../tests/lean/trust0/*.lean")
FOREACH(T ${LEANT0TESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leant0test_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/trust0"
           COMMAND bash -c "PATH=${LEAN_BIN}:$PATH ./test_single.sh ${T_NAME}")
ENDFOREACH(T)

# LEAN SERVER TESTS
file(GLOB LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/server/*.lean")
FOREACH(T ${LEANTESTS})
  if(NOT T MATCHES "\\.#")
    GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
    add_test(NAME "leanservertest_${T_NAME}"
             WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/server"
             COMMAND bash -c "PATH=${LEAN_BIN}:$PATH ./test_single.sh ${T_NAME}")
  endif()
ENDFOREACH(T)

add_test(NAME leanpkgtest
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/leanpkg/b"
         COMMAND bash -c "PATH=${LEAN_BIN}:$PATH leanpkg build")
