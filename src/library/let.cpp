/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/expr.h"
#include "library/kernel_serializer.h"

namespace lean {
static name g_let("let");
std::string const & get_let_opcode() {
    static std::string g_let_opcode("Let");
    return g_let_opcode;
}

class let_macro_definition_cell : public macro_definition_cell {
    name m_var_name;
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 2)
            throw exception("invalid let expression");
    }
public:
    let_macro_definition_cell(name const & n):m_var_name(n) {}
    name const & get_var_name() const { return m_var_name; }
    virtual name get_name() const { return g_let; }
    virtual expr get_type(expr const & m, expr const * arg_types, extension_context &) const {
        check_macro(m);
        return arg_types[1];
    }
    virtual optional<expr> expand(expr const & m, extension_context &) const {
        check_macro(m);
        return some_expr(macro_arg(m, 1));
    }
    virtual void write(serializer & s) const {
        s.write_string(get_let_opcode());
        s << m_var_name;
    }
};

expr mk_let(name const & n, expr const & v, expr const & b) {
    auto d = macro_definition(new let_macro_definition_cell(n));
    expr args[2] = {v, b};
    return mk_macro(d, 2, args);
}

bool is_let(expr const & e) {
    return is_macro(e) && dynamic_cast<let_macro_definition_cell const *>(macro_def(e).raw()) != nullptr;
}

name const & get_let_var_name(expr const & e) {
    lean_assert(is_let(e));
    return static_cast<let_macro_definition_cell const *>(macro_def(e).raw())->get_var_name();
}

expr const & get_let_value(expr const & e) {
    lean_assert(is_let(e));
    return macro_arg(e, 0);
}

expr const & get_let_body(expr const & e) {
    lean_assert(is_let(e));
    return macro_arg(e, 1);
}

static register_macro_deserializer_fn
let_des_fn(get_let_opcode(),
               [](deserializer & d, unsigned num, expr const * args) {
                   if (num != 2)
                       throw corrupted_stream_exception();
                   name n;
                   d >> n;
                   return mk_let(n, args[0], args[1]);
           });
}
