#include <iostream>
#include <fstream>
#include "version.h"
#include "parser.h"
using namespace lean;

int main(int argc, char ** argv) {
    std::cout << "Lean (version " << LEAN_VERSION_MAJOR << "." << LEAN_VERSION_MINOR << ")\n";
    frontend f;
    if (argc == 1) {
        return parse_commands(f, std::cin) ? 0 : 1;
    } else {
        bool ok = true;
        for (int i = 1; i < argc; i++) {
            std::ifstream in(argv[i]);
            if (!parse_commands(f, in))
                ok = false;
        }
        return ok ? 0 : 1;
    }
}
