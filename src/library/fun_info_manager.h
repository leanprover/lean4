/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/expr_lt.h"
#include "library/type_context.h"

namespace lean {
class fun_info_manager {
public:
    class arg_info {
        unsigned       m_implicit:1;
        unsigned       m_inst_implicit:1;
        unsigned       m_prop:1;
        unsigned       m_subsingleton:1;
        list<unsigned> m_deps; // previous arguments it depends on
    public:
        arg_info(bool imp, bool inst_imp, bool prop, bool sub, list<unsigned> const & deps):
            m_implicit(imp), m_inst_implicit(inst_imp), m_prop(prop), m_subsingleton(sub), m_deps(deps) {}
        list<unsigned> const & get_dependencies() const { return m_deps; }
        bool is_prop() const { return m_prop; }
        bool is_implicit() const { return m_implicit; }
        bool is_inst_implicit() const { return m_inst_implicit; }
        bool is_subsingleton() const { return m_subsingleton; }
    };

    class fun_info {
        unsigned       m_arity;
        list<arg_info> m_args_info;
    public:
        fun_info():m_arity(0) {}
        fun_info(unsigned arity, list<arg_info> const & info):m_arity(arity), m_args_info(info) {}
        unsigned get_arity() const { return m_arity; }
        list<arg_info> const & get_args_info() const { return m_args_info; }
    };
private:
    type_context &                         m_ctx;
    rb_map<expr, fun_info, expr_quick_cmp> m_fun_info;

public:
    fun_info_manager(type_context & ctx);
    fun_info get(expr const & e);
};
}
