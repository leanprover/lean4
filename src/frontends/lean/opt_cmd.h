/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"

namespace lean {
// We use options to communicate auxiliary commands set by the lean.exe frontend.

options set_show_goal(options const & opts, unsigned line, unsigned col);
bool has_show_goal(options const & opts, unsigned & line, unsigned & col);

options set_show_hole(options const & _opts, unsigned line, unsigned col);
bool has_show_hole(options const & opts, unsigned & line, unsigned & col);

options set_show_info(options const & opts, unsigned line, unsigned col);
bool has_show_info(options const & opts, unsigned & line, unsigned & col);

void print_lean_info_header(std::ostream & out);
void print_lean_info_footer(std::ostream & out);
}
