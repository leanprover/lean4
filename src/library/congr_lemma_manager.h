/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/app_builder.h"
#include "library/fun_info_manager.h"

namespace lean {
enum class congr_arg_kind { Fixed, Eq, Cast };

class congr_lemma {
    expr                 m_type;
    expr                 m_proof;
    list<congr_arg_kind> m_arg_kinds;
public:
    congr_lemma(expr const & type, expr const & proof, list<congr_arg_kind> const & ks):
        m_type(type), m_proof(proof), m_arg_kinds(ks) {}
    expr const & get_type() const { return m_type; }
    expr const & get_proof() const { return m_proof; }
    list<congr_arg_kind> const & get_arg_kinds() const { return m_arg_kinds; }
};

class congr_lemma_manager {
    struct imp;
    std::unique_ptr<imp> m_ptr;
public:
    /** \brief When ignore_inst_implicit is set to true, then
        for type class instance implicit arguments that are *not* subsingletons,
        the mananger will create congruence lemmas where these arguments remain fixed.
        This is the behavior we want most of the time. For example, when creating a
        congruence for
             add : Pi {A : Type} [s : has_add A], A -> A -> A
        we want the argumet s to remain fixed. */
    congr_lemma_manager(app_builder & b, fun_info_manager & fm, bool ignore_inst_implicit = true);
    ~congr_lemma_manager();
    typedef congr_lemma result;

    optional<result> mk_congr_simp(expr const & fn);
    optional<result> mk_congr_simp(expr const & fn, unsigned nargs);
};
}
