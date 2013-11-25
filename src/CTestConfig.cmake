## This file should be placed in the root directory of your project.
## Then modify the CMakeLists.txt file in the root directory of your
## project to incorporate the testing dashboard.
##
## # The following are required to submit to the CDash dashboard:
##   ENABLE_TESTING()
##   INCLUDE(CTest)

set(CTEST_PROJECT_NAME "Lean")
set(CTEST_NIGHTLY_START_TIME "00:00:00 EST")

# Specify MEMCHECK Option: http://valgrind.org/docs/manual/mc-manual.html
# Note: We use "--trace-children=yes" to valgrind-ise child processes (follow execve)
# Note: We turn off "--show-reachable=yes" option.
#set(MEMORYCHECK_SUPPRESSIONS_FILE ${CMAKE_SOURCE_DIR}/memcheck.supp)
file(TO_CMAKE_PATH "${CMAKE_SOURCE_DIR}/memcheck.supp"  MEMORYCHECK_SUPPRESSIONS_FILE)
set(VALGRIND_COMMAND_OPTIONS "-q --tool=memcheck --leak-check=yes --workaround-gcc296-bugs=yes --num-callers=50 --trace-children=yes --leak-check=full --track-origins=yes --gen-suppressions=all")
set(MEMORYCHECK_COMMAND_OPTIONS "-q --tool=memcheck --leak-check=yes --workaround-gcc296-bugs=yes --num-callers=50 --trace-children=yes --leak-check=full --track-origins=yes --gen-suppressions=all")

set(CTEST_DROP_METHOD "http")
set(CTEST_DROP_SITE "borel.modck.cs.cmu.edu")
set(CTEST_DROP_LOCATION "/CDash/submit.php?project=Lean")
set(CTEST_DROP_SITE_CDASH TRUE)

set(UPDATE_COMMAND "git")
set(COVERAGE_COMMAND "gcov-4.8")
