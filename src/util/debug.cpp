/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <sstream>
#include <set>
#include <string>
#include <memory>
#include <cstdlib>
#ifndef _WINDOWS
// Support for pid
#include<unistd.h>
#endif
#include "util/debug.h"

namespace lean {
static volatile bool           g_has_violations     = false;
static volatile bool           g_enable_assertions  = true;
static std::set<std::string> * g_enabled_debug_tags = nullptr;

void initialize_debug() {
    // lazy initialization
}

void finalize_debug() {
    delete g_enabled_debug_tags;
}

bool has_violations() {
    return g_has_violations;
}
// LCOV_EXCL_START
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
        g_enabled_debug_tags = new std::set<std::string>();
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
    g_has_violations = true;
    int * x = 0;
    for (;;) {
        if (std::cin.eof())
            exit(1);
        #ifdef _WINDOWS
        std::cerr << "(C)ontinue, (A)bort, (S)top\n";
        #else
        std::cerr << "(C)ontinue, (A)bort, (S)top, Invoke (G)DB\n";
        #endif
        char result;
        std::cin >> result;
        switch (result) {
        case 'C':
        case 'c':
            return;
        case 'A':
        case 'a':
        case EOF:
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
            } else {
                std::cerr << "ERROR STARTING GDB...\n";
                // forcing seg fault.
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
// LCOV_EXCL_STOP
}
