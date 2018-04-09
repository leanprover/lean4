/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/replace_fn.h"
#include "library/sorry.h"
#include "library/equations_compiler/util.h"
#include "library/compiler/util.h"
#include "library/compiler/procedure.h"
#include "library/compiler/compiler_step_visitor.h"

namespace lean {
class extract_values_fn : public compiler_step_visitor {
    name                  m_prefix;
    expr_map<expr>        m_cache;
    unsigned              m_idx{1};
    buffer<procedure>     m_new_procs;
    expr                  m_root;
    optional<pos_info>    m_pos;

    expr mk_aux_decl(expr const & e) {
        auto it = m_cache.find(e);
        if (it != m_cache.end())
            return it->second;
        name aux = mk_compiler_unused_name(env(), m_prefix, "_val", m_idx);
        m_new_procs.push_back(procedure(aux, m_pos, e));
        expr r   = mk_constant(aux);
        m_cache.insert(mk_pair(e, r));
        return r;
    }

    bool should_extract(expr const & e) {
        if (is_sorry(get_app_fn(e))) {
            // Never extract sorry.
            return false;
        }
        /* TODO(Leo): should we allow users to mark extra types for extract_values?
           Extracting everything is bad since caching may prevent destructive updates (e.g., arrays). */
        return is_nat_int_char_string_name_value(ctx(), e);
    }

    virtual expr visit_app(expr const & e) override {
        if (!has_local(e) && !is_eqp(e, m_root) && should_extract(e))
            return mk_aux_decl(e);
        else
            return compiler_step_visitor::visit_app(e);
    }

    virtual expr visit_macro(expr const & e) override {
        if (!has_local(e) && !is_eqp(e, m_root) && macro_num_args(e) > 0 && !is_sorry(e))
            return mk_aux_decl(e);
        else
            return compiler_step_visitor::visit_macro(e);
    }
public:
    extract_values_fn(environment const & env, abstract_context_cache & cache, name const & prefix):
        compiler_step_visitor(env, cache), m_prefix(prefix) {}

    void operator()(procedure p) {
        m_root   = p.m_code;
        m_pos    = p.m_pos;
        p.m_code = visit(p.m_code);
        m_new_procs.push_back(p);
    }

    buffer<procedure> const & get_procedures() const {
        return m_new_procs;
    }
};

void extract_values(environment const & env, abstract_context_cache & cache, name const & prefix, buffer<procedure> & procs) {
    extract_values_fn fn(env, cache, prefix);
    for (procedure const & p : procs)
        fn(p);
    procs.clear();
    procs.append(fn.get_procedures());
}
}
