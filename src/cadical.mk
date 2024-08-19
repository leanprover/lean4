CADICAL_CXX ?= c++

%.o: src/%.cpp
	ccache $(CADICAL_CXX) -std=c++11 -O3 -DNDEBUG -DNBUILD $(CXXFLAGS) -c $< -o $@

../../cadical$(CMAKE_EXECUTABLE_SUFFIX): $(patsubst src/%.cpp,%.o,$(shell ls src/*.cpp | grep -v mobical))
	$(CADICAL_CXX) -o $@ $^
