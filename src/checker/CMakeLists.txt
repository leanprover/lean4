add_executable(leanchecker checker.cpp text_import.cpp
        $<TARGET_OBJECTS:util> $<TARGET_OBJECTS:sexpr>
        $<TARGET_OBJECTS:kernel> $<TARGET_OBJECTS:inductive> $<TARGET_OBJECTS:quotient>)
install(TARGETS leanchecker DESTINATION bin)
