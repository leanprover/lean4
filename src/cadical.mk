CXX ?= c++

%.o: src/%.cpp
	$(CXX) -std=c++11 -O3 -DNDEBUG -DNBUILD $(CXXFLAGS) -c $< -o $@

%.o: src/%.c
	$(CC) -O3 -DNDEBUG -DNBUILD $(CFLAGS) -c $< -o $@

../../cadical$(CMAKE_EXECUTABLE_SUFFIX): $(patsubst src/%.cpp,%.o,$(shell ls src/*.cpp | grep -v mobical)) $(patsubst src/%.c,%.o,$(shell ls src/*.c))
	$(CXX) -o $@ $^
