/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Object to simulate delayed justification creation. */
class delayed_justification {
    optional<justification>        m_jst;
    std::function<justification()> m_mk;
public:
    template<typename Mk> delayed_justification(Mk && mk):m_mk(mk) {}
    justification get() { if (!m_jst) { m_jst = m_mk(); } return *m_jst; }
};

/** \brief Auxiliary exception used to sign that constraints cannot be created when \c m_cnstrs_enabled flag is false. */
struct add_cnstr_exception {};

class converter {
public:
    /** \brief Abstract context that must be provided to a converter object. */
    class context {
    public:
        virtual name mk_fresh_name() = 0;
        virtual expr infer_type(expr const & e) = 0;
        virtual void add_cnstr(constraint const & c) = 0;
    };

    virtual ~converter() {}

    virtual expr whnf(expr const & e, context & c) = 0;
    virtual bool is_def_eq(expr const & t, expr const & s, context & c, delayed_justification & j) = 0;
    bool is_def_eq(expr const & t, expr const & s, context & c);
};

std::unique_ptr<converter> mk_dummy_converter();
std::unique_ptr<converter> mk_default_converter(environment const & env,
                                                optional<module_idx> mod_idx = optional<module_idx>(),
                                                bool memoize = true,
                                                name_set const & extra_opaque = name_set());
}
