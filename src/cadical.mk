%.o: src/%.cpp
	ccache clang++ -O3 -DNDEBUG -DNBUILD $(CADICAL_CXXFLAGS) -c $< -o $@

../../cadical$(CMAKE_EXECUTABLE_SUFFIX): $(patsubst src/%.cpp,%.o,$(shell ls src/*.cpp | grep -v mobical))
	ccache clang++ -o $@ $^
