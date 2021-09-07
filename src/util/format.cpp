/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Soonho Kong
*/
#include <sstream>
#include <string>
#include <cstring>
#include <utility>
#include <vector>
#include <unordered_map>
#include "runtime/interrupt.h"
#include "runtime/sstream.h"
#include "runtime/hash.h"
#include "util/options.h"
#include "util/option_declarations.h"
#include "util/format.h"

#ifndef LEAN_DEFAULT_PP_INDENTATION
#define LEAN_DEFAULT_PP_INDENTATION 2
#endif

#ifndef LEAN_DEFAULT_PP_UNICODE
#define LEAN_DEFAULT_PP_UNICODE true
#endif

#ifndef LEAN_DEFAULT_PP_WIDTH
#define LEAN_DEFAULT_PP_WIDTH 120
#endif

namespace lean {
static name * g_pp_indent  = nullptr;
static name * g_pp_unicode = nullptr;
static name * g_pp_width   = nullptr;

unsigned get_pp_indent(options const & o) {
    return o.get_unsigned(*g_pp_indent, LEAN_DEFAULT_PP_INDENTATION);
}
bool get_pp_unicode(options const & o) {
    return o.get_bool(*g_pp_unicode, LEAN_DEFAULT_PP_UNICODE);
}
unsigned get_pp_width(options const & o) {
    return o.get_unsigned(*g_pp_width, LEAN_DEFAULT_PP_WIDTH);
}

extern "C" object* lean_format_append(object* f1, object* f2);
extern "C" object* lean_format_group(object* f);
extern "C" object* lean_format_pretty(object* f, object* w);

format compose(format const & f1, format const & f2) {
    return format(lean_format_append(f1.to_obj_arg(), f2.to_obj_arg()));
}
format nest(int i, format const & f) {
    return format(mk_cnstr(static_cast<unsigned>(format::format_kind::NEST), mk_nat_obj(static_cast<unsigned>(i)), f.to_obj_arg()));
}

static format * g_line = nullptr;
static format * g_space = nullptr;
format line() { return *g_line; }
format space() { return *g_space; }
format group(format const & f) {
    return format(lean_format_group(f.to_obj_arg()));
}
format bracket(std::string const & l, format const & x, std::string const & r) {
    return group(nest(l.size(), format(l) + x + format(r)));
}
format paren(format const & x) {
    return group(nest(1, format("(") + x + format(")")));
}
format operator+(format const & f1, format const & f2) {
    return compose(f1, f2);
}

std::ostream & format::pretty(std::ostream & out, unsigned w, format const & f) {
    string_ref s(lean_format_pretty(f.to_obj_arg(), mk_nat_obj(w)));
    out << s.data();
    return out;
}

std::ostream & pretty(std::ostream & out, unsigned w, format const & f) {
    return format::pretty(out, w, f);
}

std::ostream & pretty(std::ostream & out, options const & opts, format const & f) {
    return pretty(out, get_pp_width(opts), f);
}

std::ostream & operator<<(std::ostream & out, format const & f) {
    return pretty(out, LEAN_DEFAULT_PP_WIDTH, f);
}

std::ostream & operator<<(std::ostream & out, pair<format const &, options const &> const & p) {
    return pretty(out, p.second, p.first);
}

bool format_pp_eq(format const & f1, format const & f2, options const & o) {
    std::ostringstream out1;
    std::ostringstream out2;
    out1 << mk_pair(f1, o);
    out2 << mk_pair(f2, o);
    return out1.str() == out2.str();
}

format pp(name const & n) {
    return format(n.to_string());
}

void initialize_format() {
    g_pp_indent  = new name{"pp", "indent"};
    mark_persistent(g_pp_indent->raw());
    g_pp_unicode = new name{"pp", "unicode"};
    mark_persistent(g_pp_unicode->raw());
    g_pp_width   = new name{"pp", "width"};
    mark_persistent(g_pp_width->raw());
    g_line  = new format(box(static_cast<unsigned>(format::format_kind::LINE)));
    mark_persistent(g_line->raw());
    g_space = new format(" ");
    mark_persistent(g_space->raw());
}

void finalize_format() {
    delete g_line;
    delete g_space;
    delete g_pp_indent;
    delete g_pp_unicode;
    delete g_pp_width;
}
}
