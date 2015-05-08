/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "library/choice.h"
#include "library/kernel_bindings.h"
#include "library/kernel_serializer.h"

namespace lean {
static name * g_choice_name = nullptr;
static std::string * g_choice_opcode = nullptr;

[[ noreturn ]] static void throw_ex() { throw exception("unexpected occurrence of 'choice' expression"); }

// We encode a 'choice' expression using a macro.
// This is a trick to avoid creating a new kind of expression.
// 'Choice' expressions are temporary objects used by the elaborator,
// and have no semantic significance.
class choice_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_choice_name; }
    // Choice expressions must be replaced with metavariables before invoking the type checker.
    // Choice expressions cannot be exported. They are transient/auxiliary objects.
    virtual pair<expr, constraint_seq> check_type(expr const &, extension_context &, bool) const { throw_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_ex(); }
    virtual void write(serializer & s) const {
        // we should be able to write choice expressions because of notation declarations
        s.write_string(*g_choice_opcode);
    }
};

static macro_definition * g_choice = nullptr;
expr mk_choice(unsigned num_es, expr const * es) {
    lean_assert(num_es > 0);
    if (num_es == 1)
        return es[0];
    else
        return mk_macro(*g_choice, num_es, es);
}

void initialize_choice() {
    g_choice_name   = new name("choice");
    g_choice_opcode = new std::string("Choice");
    g_choice        = new macro_definition(new choice_macro_cell());
    register_macro_deserializer(*g_choice_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    return mk_choice(num, args);
                                });
}

void finalize_choice() {
    delete g_choice;
    delete g_choice_opcode;
    delete g_choice_name;
}

bool is_choice(expr const & e) {
    return is_macro(e) && macro_def(e) == *g_choice;
}

unsigned get_num_choices(expr const & e) {
    lean_assert(is_choice(e));
    return macro_num_args(e);
}

expr const & get_choice(expr const & e, unsigned i) {
    lean_assert(is_choice(e));
    return macro_arg(e, i);
}

static int mk_choice(lua_State * L) {
    check_atleast_num_args(L, 1);
    int nargs = lua_gettop(L);
    buffer<expr> args;
    for (int i = 1; i <= nargs; i++)
        args.push_back(to_expr(L, i));
    return push_expr(L, mk_choice(args.size(), args.data()));
}

static int is_choice(lua_State * L) {
    return push_boolean(L, is_choice(to_expr(L, 1)));
}
static void check_choice(lua_State * L, int idx) {
    if (!is_choice(to_expr(L, idx)))
        throw exception(sstream() << "arg #" << idx << " is not a choice-expression");
}
static int get_num_choices(lua_State * L) {
    check_choice(L, 1);
    return push_integer(L, get_num_choices(to_expr(L, 1)));
}
static int get_choice(lua_State * L) {
    check_choice(L, 1);
    expr const & c = to_expr(L, 1);
    int i = lua_tointeger(L, 2);
    if (i < 0 || static_cast<unsigned>(i) >= get_num_choices(c))
        throw exception("arg #2 is an invalid choice index");
    return push_expr(L, get_choice(c, i));
}

void open_choice(lua_State * L) {
    SET_GLOBAL_FUN(mk_choice,       "mk_choice");
    SET_GLOBAL_FUN(is_choice,       "is_choice");
    SET_GLOBAL_FUN(get_num_choices, "get_num_choices");
    SET_GLOBAL_FUN(get_choice,      "get_choice");
}
}
