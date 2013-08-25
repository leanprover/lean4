#include <iostream>
#include <fstream>
#include <signal.h>
#include "version.h"
#include "printer.h"
#include "interruptable_ptr.h"
#include "lean_parser.h"
using namespace lean;

static interruptable_ptr<shell> g_lean_shell;

static void on_ctrl_c(int) {
    g_lean_shell.set_interrupt(true);
}

bool lean_shell() {
    std::cout << "Lean (version " << LEAN_VERSION_MAJOR << "." << LEAN_VERSION_MINOR << ")\n";
    std::cout << "Type Ctrl-D to exit or 'Help.' for help."<< std::endl;
    frontend f;
    shell sh(f);
    scoped_set_interruptable_ptr<shell> set(g_lean_shell, &sh);
    signal(SIGINT, on_ctrl_c);
    return sh();
}

int main(int argc, char ** argv) {
    if (argc == 1) {
        return lean_shell() ? 0 : 1;
    } else {
        bool ok = true;
        frontend f;
        for (int i = 1; i < argc; i++) {
            std::ifstream in(argv[i]);
            parser p(f, in);
            if (!p())
                ok = false;
        }
        return ok ? 0 : 1;
    }
}
