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
#include "util/escaped.h"
#include "util/sexpr/sexpr.h"
#include "util/sexpr/format.h"
#include "util/sexpr/sexpr_fn.h"
#include "util/options.h"
#include "util/option_declarations.h"

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
format compose(format const & f1, format const & f2) {
    return format(format::sexpr_compose({f1.m_value, f2.m_value}));
}
format nest(int i, format const & f) {
    return format(format::sexpr_nest(i, f.m_value));
}
// Commonly used format objects
format mk_line() {
    return format(format::sexpr_line());
}

static format * g_line = nullptr;
static format * g_space = nullptr;
static sexpr  * g_sexpr_space = nullptr;
format line() { return *g_line; }
format space() { return *g_space; }
// Auxiliary flag used to mark whether flatten
// produce a different sexpr
LEAN_THREAD_VALUE(bool, g_diff_flatten, false);
//
sexpr format::flatten(sexpr const & s) {
    check_system("formatter");
    lean_assert(is_cons(s));
    switch (sexpr_kind(s)) {
    case format_kind::NIL:
        /* flatten NIL = NIL */
        return s;
    case format_kind::NEST:
        /* flatten (NEST i x) = flatten x */
        return flatten(sexpr_nest_s(s));
    case format_kind::COMPOSE:
        /* flatten (s_1 <> ... <> s_n ) = flatten s_1 <> ... <> flatten s_n */
        return sexpr_flat_compose(map(sexpr_compose_list(s),
                                      [](sexpr const & s) {
                                          return flatten(s);
                                      }));
    case format_kind::CHOICE:
        /* flatten (x <|> y) = flatten x */
        g_diff_flatten = true;
        return flatten(sexpr_choice_1(s));
    case format_kind::LINE:
        g_diff_flatten = true;
        return *g_sexpr_space;
    case format_kind::FLAT_COMPOSE:
    case format_kind::TEXT:
        return s;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
format flatten(format const & f){
    return format(format::flatten(f.m_value));
}
format group(format const & f) {
    g_diff_flatten = false;
    format flat_f = flatten(f);
    if (g_diff_flatten) {
        return choice(flat_f, f);
    } else {
        // flat_f and f are essentially the same format object.
        // So, we don't need to create a choice.
        return flat_f;
    }
}
format bracket(std::string const & l, format const & x, std::string const & r) {
    return group(nest(l.size(), format(l) + x + format(r)));
}
format paren(format const & x) {
    return group(nest(1, format("(") + x + format(")")));
}

/**
   \brief Auxiliary exception used to sign that the amount of
   available space was exhausted. It is used in \c space_upto_line_break and
   \c space_upto_line_break_list_exceeded
*/
struct space_exceeded {};

/**
   \brief Return true iff the space upto line break fits in the available space.
*/
bool format::space_upto_line_break_list_exceeded(sexpr const & s, int available, std::vector<pair<sexpr, unsigned>> const & todo) {
    try {
        bool found_newline = false;
        available -= space_upto_line_break(s, available, found_newline);
        auto it    = todo.end();
        auto begin = todo.begin();
        while (it != begin && !found_newline) {
            --it;
            if (available < 0)
                return true;
            available -= space_upto_line_break(it->first, available, found_newline);
        }
        return available < 0;
    } catch (space_exceeded) {
        return true;
    }
}

/**
   \brief Return the space upto line break. If the space exceeds available, then throw an exception.
*/
int format::space_upto_line_break(sexpr const & s, int available, bool & found_newline) {
    // s : format
    lean_assert(!found_newline);

    switch (sexpr_kind(s)) {
    case format_kind::NIL:
    {
        return 0;
    }
    case format_kind::COMPOSE:
    case format_kind::FLAT_COMPOSE:
    {
        sexpr list  = sexpr_compose_list(s);
        int len = 0;
        while (!is_nil(list) && !found_newline) {
            sexpr h = car(list);
            list    = cdr(list);
            len += space_upto_line_break(h, available, found_newline);
            if (len > available)
                throw space_exceeded();
        }
        return len;
    }
    case format_kind::NEST:
    {
        sexpr const & x = sexpr_nest_s(s);
        return space_upto_line_break(x, available, found_newline);
    }
    case format_kind::TEXT: {
        return sexpr_text_length(s);
    }
    case format_kind::LINE:
        found_newline = true;
        return 0;
    case format_kind::CHOICE:
    {
        sexpr const & x = sexpr_choice_2(s);
        return space_upto_line_break(x, available, found_newline);
    }
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

format operator+(format const & f1, format const & f2) {
    return compose(f1, f2);
}

format operator^(format const & f1, format const & f2) {
    return compose(f1, compose(format(" "), f2));
}

std::ostream & format::pretty(std::ostream & out, unsigned w, format const & f) {
    unsigned pos        = 0;
    std::vector<pair<sexpr, unsigned>> todo;
    todo.push_back(std::make_pair(f.m_value, 0));
    while (!todo.empty()) {
        check_system("formatter");
        auto pair       = todo.back();
        sexpr s         = pair.first;
        unsigned indent = pair.second;
        todo.pop_back();

        switch (sexpr_kind(s)) {
        case format_kind::NIL:
            break;
        case format_kind::COMPOSE:
        case format_kind::FLAT_COMPOSE: {
            unsigned old_sz     = todo.size();
            for_each(sexpr_compose_list(s), [&](sexpr const & c) { todo.emplace_back(c, indent); });
            std::reverse(todo.begin() + old_sz, todo.end());
            break;
        }
        case format_kind::NEST:
            todo.emplace_back(sexpr_nest_s(s), indent + sexpr_nest_i(s));
            break;
        case format_kind::LINE:
            pos        = indent;
            out << "\n";
            for (unsigned i = 0; i < indent; i++)
                out << " ";
            break;
        case format_kind::TEXT:
            pos += sexpr_text_length(s);
            if (is_string(cdr(s)))
                out << to_string(cdr(s));
            else
                out << cdr(s);
            break;
        case format_kind::CHOICE: {
            sexpr const & x = sexpr_choice_1(s);
            sexpr const & y = sexpr_choice_2(s);;
            int available   = static_cast<int>(w) - static_cast<int>(pos);
            if (!space_upto_line_break_list_exceeded(x, available, todo))
                todo.emplace_back(x, indent);
            else
                todo.emplace_back(y, indent);
        }
        }
    }
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
    g_pp_unicode = new name{"pp", "unicode"};
    g_pp_width   = new name{"pp", "width"};
    register_unsigned_option(*g_pp_indent, LEAN_DEFAULT_PP_INDENTATION, "(pretty printer) default indentation");
    register_bool_option(*g_pp_unicode, LEAN_DEFAULT_PP_UNICODE, "(pretty printer) use unicode characters");
    register_unsigned_option(*g_pp_width, LEAN_DEFAULT_PP_WIDTH, "(pretty printer) line width");
    g_line = new format(mk_line());
    g_space = new format(" ");
    g_sexpr_space = new sexpr(sexpr(format::format_kind::TEXT), " ");
}

void finalize_format() {
    delete g_sexpr_space;
    delete g_line;
    delete g_space;
    delete g_pp_indent;
    delete g_pp_unicode;
    delete g_pp_width;
}
}
