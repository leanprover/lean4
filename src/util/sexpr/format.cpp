/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Soonho Kong
*/
#include <sstream>
#include <string>
#include <utility>
#include "util/escaped.h"
#include "util/sexpr/sexpr.h"
#include "util/sexpr/format.h"
#include "util/sexpr/sexpr_fn.h"
#include "util/sexpr/options.h"

#ifndef LEAN_DEFAULT_PP_INDENTATION
#define LEAN_DEFAULT_PP_INDENTATION 4
#endif

#ifndef LEAN_DEFAULT_PP_UNICODE
#define LEAN_DEFAULT_PP_UNICODE true
#endif

#ifndef LEAN_DEFAULT_PP_WIDTH
#define LEAN_DEFAULT_PP_WIDTH 120
#endif

#ifndef LEAN_DEFAULT_PP_COLORS
#define LEAN_DEFAULT_PP_COLORS true
#endif

#ifndef LEAN_KEYWORD_HIGHLIGHT_COLOR
#define LEAN_KEYWORD_HIGHLIGHT_COLOR format::ORANGE
#endif

#ifndef LEAN_BUILTIN_HIGHLIGHT_COLOR
#define LEAN_BUILTIN_HIGHLIGHT_COLOR format::CYAN
#endif

#ifndef LEAN_COMMAND_HIGHLIGHT_COLOR
#define LEAN_COMMAND_HIGHLIGHT_COLOR format::BLUE
#endif

namespace lean {
static name g_pp_indent{"pp", "indent"};
static name g_pp_unicode{"pp", "unicode"};
static name g_pp_colors{"pp", "colors"};
static name g_pp_width{"pp", "width"};

RegisterUnsignedOption(g_pp_indent, LEAN_DEFAULT_PP_INDENTATION, "(pretty printer) default indentation");
RegisterBoolOption(g_pp_unicode, LEAN_DEFAULT_PP_UNICODE, "(pretty printer) use unicode characters");
RegisterBoolOption(g_pp_colors, LEAN_DEFAULT_PP_COLORS, "(pretty printer) use colors");
RegisterUnsignedOption(g_pp_width, LEAN_DEFAULT_PP_WIDTH, "(pretty printer) line width");

unsigned get_pp_indent(options const & o) {
    return o.get_unsigned(g_pp_indent, LEAN_DEFAULT_PP_INDENTATION);
}

bool get_pp_unicode(options const & o) {
    return o.get_bool(g_pp_unicode, LEAN_DEFAULT_PP_UNICODE);
}

bool get_pp_colors(options const & o) {
    return o.get_bool(g_pp_colors, LEAN_DEFAULT_PP_COLORS);
}

unsigned get_pp_width(options const & o) {
    return o.get_unsigned(g_pp_width, LEAN_DEFAULT_PP_WIDTH);
}

std::ostream & layout(std::ostream & out, bool colors, sexpr const & s) {
    lean_assert(!is_nil(s));
    switch (format::sexpr_kind(s)) {
    case format::format_kind::NEST:
    case format::format_kind::CHOICE:
    case format::format_kind::COMPOSE:
    case format::format_kind::FLAT_COMPOSE:
        lean_unreachable(); // LCOV_EXCL_LINE

    case format::format_kind::NIL:
        out << "";
        break;

    case format::format_kind::LINE:
        out << std::endl;
        break;

    case format::format_kind::TEXT:
    {
        sexpr const & v = cdr(s);
        if (is_string(v)) {
            out << to_string(v);
        } else {
            out << v;
        }
        break;
    }

    case format::format_kind::COLOR_BEGIN:
        if (colors) {
            format::format_color c = static_cast<format::format_color>(to_int(cdr(s)));
            out << "\e[" << (31 + c % 7) << "m";
        }
        break;
    case format::format_kind::COLOR_END:
        if (colors) {
            out << "\e[0m";
        }
        break;
    }
    return out;
}

std::ostream & layout_list(std::ostream & out, bool colors, sexpr const & s) {
    for_each(s, [&](sexpr const & s) {
            layout(out, colors, s);
        });
    return out;
}

format compose(format const & f1, format const & f2) {
    return format(format::sexpr_compose({f1.m_value, f2.m_value}));
}
format nest(int i, format const & f) {
    return format(format::sexpr_nest(i, f.m_value));
}
format highlight(format const & f, format::format_color const c) {
    return format(format::sexpr_highlight(f.m_value, c));
}
format highlight_keyword(format const & f) {
    return highlight(f, LEAN_KEYWORD_HIGHLIGHT_COLOR);
}
format highlight_builtin(format const & f) {
    return highlight(f, LEAN_BUILTIN_HIGHLIGHT_COLOR);
}
format highlight_command(format const & f) {
    return highlight(f, LEAN_COMMAND_HIGHLIGHT_COLOR);
}
// Commonly used format objects
format mk_line() {
    return format(format::sexpr_line());
}
static format g_line(mk_line());
static format g_space(" ");
static format g_lp("(");
static format g_rp(")");
static format g_lsb("[");
static format g_rsb("]");
static format g_lcurly("{");
static format g_rcurly("}");
static format g_comma(",");
static format g_colon(":");
static format g_dot(".");
format const & line() { return g_line; }
format const & space() { return g_space; }
format const & lp() { return g_lp; }
format const & rp() { return g_rp; }
format const & lsb() { return g_lsb; }
format const & rsb() { return g_rsb; }
format const & lcurly() { return g_lcurly; }
format const & rcurly() { return g_rcurly; }
format const & comma() { return g_comma; }
format const & colon() { return g_colon; }
format const & dot() { return g_dot; }
// Auxiliary flag used to mark whether flatten
// produce a different sexpr
static bool thread_local g_diff_flatten = false;
//
sexpr format::flatten(sexpr const & s) {
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
        return sexpr_text(sexpr(" "));
    case format_kind::FLAT_COMPOSE:
    case format_kind::TEXT:
    case format_kind::COLOR_BEGIN:
    case format_kind::COLOR_END:
        return s;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
format format::flatten(format const & f){
    return format(flatten(f.m_value));
}
format group(format const & f) {
    g_diff_flatten = false;
    format flat_f = format::flatten(f);
    if (g_diff_flatten) {
        return choice(flat_f, f);
    } else {
        // flat_f and f are essentially the same format object.
        // So, we don't need to create a choice.
        return flat_f;
    }
}
format above(format const & f1, format const & f2) {
    return format{f1, line(), f2};
}
format bracket(std::string const & l, format const & x, std::string const & r) {
    return group(nest(l.size(), format{format(l), x, format(r)}));
}
format paren(format const & x) {
    return group(nest(1, format{lp(), x, rp()}));
}

// wrap = <+/>
// wrap x y = x <> (text " " :<|> line) <> y
format wrap(format const & f1, format const & f2) {
    return format{f1,
                  choice(format(" "), line()),
                  f2};
}

/**
   \brief Auxiliary exception used to sign that the amount of
   available space was exhausted. It is used in \c space_upto_line_break and
   \c space_upto_line_break_list_exceeded
*/
struct space_exceeded {};

// Return true iff the space upto line break fits in the available space.
bool format::space_upto_line_break_list_exceeded(sexpr const & r, int available) {
    // r : list of (int * format)
    try {
        lean_assert(is_list(r));
        sexpr list = r;
        bool found_newline = false;
        while (!is_nil(list) && !found_newline) {
            if (available < 0)
                return true;
            sexpr const & h = cdr(car(list));
            available -= space_upto_line_break(h, available, found_newline);
            list = cdr(list);
        }
        return available < 0;
    } catch (space_exceeded) {
        return true;
    }
    return false;
}

/**
   \brief Return the space upto line break. If the space exceeds available, then throw an exception.
*/
int format::space_upto_line_break(sexpr const & s, int available, bool & found_newline) {
    // s : format
    lean_assert(!found_newline);
    lean_assert(sexpr_kind(s) <= format_kind::COLOR_END);

    switch (sexpr_kind(s)) {
    case format_kind::NIL:
    case format_kind::COLOR_BEGIN:
    case format_kind::COLOR_END:
    {
        return 0;
    }
    case format_kind::COMPOSE:
    case format_kind::FLAT_COMPOSE:
    {
        sexpr list  = sexpr_compose_list(s);
        int len = 0;
        while (!is_nil(list) && !found_newline) {
            sexpr const & h = car(list);
            list = cdr(list);
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

sexpr format::be(unsigned w, unsigned k, sexpr const & s) {
    /* s = (i, v) :: z, where h has the type int x format */
    /* ret = list of format */

    if (is_nil(s)) {
        return sexpr{};
    }

    sexpr const & h = car(s);
    sexpr const & z = cdr(s);
    int i = to_int(car(h));
    sexpr const & v = cdr(h);

    switch (sexpr_kind(v)) {
    case format_kind::NIL:
        return be(w, k, z);
    case format_kind::COLOR_BEGIN:
    case format_kind::COLOR_END:
        return sexpr(v, be(w, k, z));
    case format_kind::COMPOSE:
    case format_kind::FLAT_COMPOSE:
    {
        sexpr const & list  = sexpr_compose_list(v);
        sexpr const & list_ = foldr(list, z, [i](sexpr const & s, sexpr const & res) {
                return sexpr(sexpr(i, s), res);
            });
        return be(w, k, list_);
    }
    case format_kind::NEST:
    {
        int j = sexpr_nest_i(v);
        sexpr const & x = sexpr_nest_s(v);
        return be(w, k, sexpr(sexpr(i + j, x), z));
    }
    case format_kind::TEXT:
        return sexpr(v, be(w, k + sexpr_text_length(v), z));
    case format_kind::LINE:
        return sexpr(v, sexpr(sexpr_text(std::string(i, ' ')), be(w, i, z)));
    case format_kind::CHOICE:
    {
        sexpr const & x = sexpr_choice_1(v);
        sexpr const & y = sexpr_choice_2(v);;
        int available = static_cast<int>(w) - static_cast<int>(k);
        if (!space_upto_line_break_list_exceeded(sexpr(sexpr(i, x), z), available)) {
            sexpr const & s1 = be(w, k, sexpr(sexpr(i, x), z));
            return s1;
        } else {
            sexpr const & s2 = be(w, k, sexpr(sexpr(i, y), z));
            return s2;
        }
    }
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

sexpr format::best(unsigned w, unsigned k, sexpr const & s) {
    return be(w, k, sexpr{sexpr(0, s)});
}

format operator+(format const & f1, format const & f2) {
    return format{f1, f2};
}

format operator^(format const & f1, format const & f2) {
    return format {f1, format(" "), f2};
}

std::ostream & pretty(std::ostream & out, unsigned w, bool colors, format const & f) {
    sexpr const & b = format::best(w, 0, f.m_value);
    return layout_list(out, colors, b);
}

std::ostream & pretty(std::ostream & out, unsigned w, format const & f) {
    return pretty(out, w, LEAN_DEFAULT_PP_COLORS, f);
}

std::ostream & pretty(std::ostream & out, options const & opts, format const & f) {
    return pretty(out, get_pp_width(opts), get_pp_colors(opts), f);
}

std::ostream & operator<<(std::ostream & out, format const & f) {
    return pretty(out, LEAN_DEFAULT_PP_WIDTH, LEAN_DEFAULT_PP_COLORS, f);
}

std::ostream & operator<<(std::ostream & out, std::pair<format const &, options const &> const & p) {
    return pretty(out, p.second, p.first);
}

format pp(name const & n) {
    return format(n.to_string());
}

struct sexpr_pp_fn {
    format apply(sexpr const & s) {
        switch (s.kind()) {
        case sexpr_kind::NIL:         return format("nil");
        case sexpr_kind::STRING: {
            std::ostringstream ss;
            ss << "\"" << escaped(to_string(s).c_str()) << "\"";
            return format(ss.str());
        }
        case sexpr_kind::BOOL:        return format(to_bool(s) ? "true" : "false");
        case sexpr_kind::INT:         return format(to_int(s));
        case sexpr_kind::DOUBLE:      return format(to_double(s));
        case sexpr_kind::NAME:        return pp(to_name(s));
        case sexpr_kind::MPZ:         return format(to_mpz(s));
        case sexpr_kind::MPQ:         return format(to_mpq(s));
        case sexpr_kind::CONS: {
            sexpr const * curr = &s;
            format r;
            while (true) {
                r += apply(head(*curr));
                curr = &tail(*curr);
                if (is_nil(*curr)) {
                    return paren(r);
                } else if (!is_cons(*curr)) {
                    return group(nest(1, format{lp(), r, space(), dot(), line(), apply(*curr), rp()}));
                } else {
                    r += line();
                }
            }
        }}
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    format operator()(sexpr const & s) {
        return apply(s);
    }
};

format pp(sexpr const & s) {
    return sexpr_pp_fn()(s);
}
}
