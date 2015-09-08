add_library(api OBJECT string.cpp exception.cpp name.cpp options.cpp univ.cpp
  expr.cpp decl.cpp env.cpp ios.cpp module.cpp type_checker.cpp inductive.cpp
  parser.cpp)

FILE(GLOB LEAN_API_INCLUDE_FILES lean*.h)
install(FILES ${LEAN_API_INCLUDE_FILES} DESTINATION include)
