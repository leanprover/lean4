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
#include "util/sstream.h"
#include "util/escaped.h"
#include "util/interrupt.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpq.h"
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
#define LEAN_DEFAULT_PP_COLORS false
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
static bool LEAN_THREAD_LOCAL g_diff_flatten = false;
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

/**
   \brief Return true iff the space upto line break fits in the available space.
*/
bool format::space_upto_line_break_list_exceeded(sexpr const & s, int available, std::vector<std::pair<sexpr, unsigned>> const & todo) {
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

format operator+(format const & f1, format const & f2) {
    return format{f1, f2};
}

format operator^(format const & f1, format const & f2) {
    return format {f1, format(" "), f2};
}

std::ostream & format::pretty(std::ostream & out, unsigned w, bool colors, format const & f) {
    unsigned pos        = 0;
    std::vector<std::pair<sexpr, unsigned>> todo;
    todo.push_back(std::make_pair(f.m_value, 0));
    while (!todo.empty()) {
        auto pair       = todo.back();
        sexpr s         = pair.first;
        unsigned indent = pair.second;
        todo.pop_back();

        switch (sexpr_kind(s)) {
        case format_kind::NIL:
            break;
        case format_kind::COLOR_BEGIN:
            if (colors) {
                format::format_color c = static_cast<format::format_color>(to_int(cdr(s)));
                out << "\e[" << (31 + c % 7) << "m";
            }
            break;
        case format_kind::COLOR_END:
            if (colors) {
                out << "\e[0m";
            }
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

std::ostream & pretty(std::ostream & out, unsigned w, bool colors, format const & f) {
    return format::pretty(out, w, colors, f);
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
        case sexpr_kind::Nil:         return format("nil");
        case sexpr_kind::String: {
            std::ostringstream ss;
            ss << "\"" << escaped(to_string(s).c_str()) << "\"";
            return format(ss.str());
        }
        case sexpr_kind::Bool:        return format(to_bool(s) ? "true" : "false");
        case sexpr_kind::Int:         return format(to_int(s));
        case sexpr_kind::Double:      return format(to_double(s));
        case sexpr_kind::Name:        return pp(to_name(s));
        case sexpr_kind::MPZ:         return format(to_mpz(s));
        case sexpr_kind::MPQ:         return format(to_mpq(s));
        case sexpr_kind::Cons: {
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

DECL_UDATA(format)

format to_format_elem(lua_State * L, int idx) {
    if (is_format(L, idx))
        return to_format(L, idx);
    else if (lua_isnumber(L, idx))
        return format(static_cast<int>(lua_tonumber(L, idx)));
    else if (is_name(L, idx))
        return format(to_name(L, idx));
    else if (is_mpz(L, idx))
        return format(to_mpz(L, idx));
    else if (is_mpq(L, idx))
        return format(to_mpq(L, idx));
    else
        return format(lua_tostring(L, idx));
}

static int format_tostring(lua_State * L) {
    std::ostringstream out;
    out << mk_pair(to_format(L, 1), get_global_options(L));
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int format_concat(lua_State * L) {
    return push_format(L, compose(to_format_elem(L, 1), to_format_elem(L, 2)));
}

static int mk_format(lua_State * L) {
    format r;
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        r = format();
    } else {
        int i = nargs;
        r = to_format_elem(L, i);
        i--;
        for (; i >= 1; i--) {
            r = compose(to_format_elem(L, i), r);
        }
    }
    return push_format(L, r);
}

static int format_nest(lua_State * L) {
    return push_format(L, nest(luaL_checkinteger(L, 2), to_format(L, 1)));
}

static int format_group(lua_State * L) {
    return push_format(L, group(to_format(L, 1)));
}

static int format_highlight(lua_State * L) {
    char const * color_str = luaL_checkstring(L, 2);
    format::format_color color;
    if (strcmp(color_str, "red") == 0) {
        color = format::RED;
    } else if (strcmp(color_str, "green") == 0) {
        color = format::GREEN;
    } else if (strcmp(color_str, "orange") == 0) {
        color = format::ORANGE;
    } else if (strcmp(color_str, "blue") == 0) {
        color = format::BLUE;
    } else if (strcmp(color_str, "cyan") == 0) {
        color = format::CYAN;
    } else if (strcmp(color_str, "grey") == 0) {
        color = format::GREY;
    } else {
        throw exception(sstream() << "unknown color '" << color_str << "'");
    }
    return push_format(L, highlight(to_format(L, 1), color));
}

static int format_line(lua_State * L) { return push_format(L, line()); }
static int format_space(lua_State * L) { return push_format(L, space()); }

static const struct luaL_Reg format_m[] = {
    {"__gc",            format_gc}, // never throws
    {"__tostring",      safe_function<format_tostring>},
    {"__concat",        safe_function<format_concat>},
    {"nest",            safe_function<format_nest>},
    {"group",           safe_function<format_group>},
    {"highlight",       safe_function<format_highlight>},
    {0, 0}
};

static void format_migrate(lua_State * src, int i, lua_State * tgt) {
    push_format(tgt, to_format(src, i));
}

void open_format(lua_State * L) {
    luaL_newmetatable(L, format_mt);
    set_migrate_fn_field(L, -1, format_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, format_m, 0);

    SET_GLOBAL_FUN(mk_format,    "format");
    SET_GLOBAL_FUN(format_line,  "line");
    SET_GLOBAL_FUN(format_space, "space");
    SET_GLOBAL_FUN(format_pred,  "is_format");
}
}
