#include <iostream>
#include "version.h"
#include "parser.h"
using namespace lean;

int main() {
    std::cout << "Lean (version " << LEAN_VERSION_MAJOR << "." << LEAN_VERSION_MINOR << ")\n";
    frontend f;
    return parse_commands(f, std::cin) ? 0 : 1;
}
