/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#include "debug.h"
#include <iostream>
#include <sstream>
#include <set>
#include <string>
#include <memory>

#ifndef _WINDOWS
// Support for pid
#include<unistd.h>
#endif

namespace lean {

static volatile bool                          g_enable_assertions = true;
static std::unique_ptr<std::set<std::string>> g_enabled_debug_tags;

void enable_assertions(bool f) {
    g_enable_assertions = f;
}

bool assertions_enabled() {
    return g_enable_assertions;
}

void notify_assertion_violation(const char * fileName, int line, const char * condition) {
    std::cerr << "LEAN ASSERTION VIOLATION\n";
    std::cerr << "File: " << fileName << "\n";
    std::cerr << "Line: " << line << "\n";
    std::cerr << condition << "\n";
    std::cerr.flush();
}

void enable_debug(char const * tag) {
    if (!g_enabled_debug_tags)
        g_enabled_debug_tags.reset(new std::set<std::string>());
    g_enabled_debug_tags->insert(tag);
}

void disable_debug(char const * tag) {
    if (g_enabled_debug_tags)
        g_enabled_debug_tags->erase(tag);
}

bool is_debug_enabled(const char * tag) {
    return g_enabled_debug_tags && g_enabled_debug_tags->find(tag) != g_enabled_debug_tags->end();
}

void invoke_debugger() {
    int * x = 0;
    for (;;) {
        #ifdef _WINDOWS
        std::cerr << "(C)ontinue, (A)bort, (S)top\n";
        #else
        std::cerr << "(C)ontinue, (A)bort, (S)top, Invoke (G)DB\n";
        #endif
        char result;
        std::cin >> result;
        switch(result) {
        case 'C':
        case 'c':
            return;
        case 'A':
        case 'a':
            exit(1);
        case 'S':
        case 's':
            // force seg fault...
            *x = 0;
            return;
        #ifndef _WINDOWS
        case 'G':
        case 'g': {
            std::cerr << "INVOKING GDB...\n";
            std::ostringstream buffer;
            buffer << "gdb -nw /proc/" << getpid() << "/exe " << getpid();
            if (system(buffer.str().c_str()) == 0) {
                std::cerr << "continuing the execution...\n";
            }
            else {
                std::cerr << "ERROR STARTING GDB...\n";
                // forcing seg fault.
                int * x = 0;
                *x = 0;
            }
            return;
        }
        #endif
        default:
            std::cerr << "INVALID COMMAND\n";
        }
    }
}

}
