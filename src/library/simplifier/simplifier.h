/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "util/lua.h"
#include "kernel/environment.h"
#include "library/expr_pair.h"
#include "library/simplifier/rewrite_rule_set.h"

namespace lean {
class simplifier_monitor;

/** \brief Simplifier object cell. */
class simplifier_cell {
    friend class simplifier;
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    simplifier_cell(ro_environment const & env, options const & o, unsigned num_rs, rewrite_rule_set const * rs,
                    std::shared_ptr<simplifier_monitor> const & monitor);

    expr_pair operator()(expr const & e, context const & ctx);
    void clear();

    unsigned get_depth() const;
    context const & get_context() const;
    ro_environment const & get_environment() const;
    options const & get_options() const;
};

/** \brief Reference to simplifier object */
class simplifier {
    friend class ro_simplifier;
    std::shared_ptr<simplifier_cell> m_ptr;
public:
    simplifier(ro_environment const & env, options const & o, unsigned num_rs, rewrite_rule_set const * rs,
               std::shared_ptr<simplifier_monitor> const & monitor);
    simplifier_cell * operator->() const { return m_ptr.get(); }
    simplifier_cell & operator*() const { return *(m_ptr.get()); }
    expr_pair operator()(expr const & e, context const & ctx) { return (*m_ptr)(e, ctx); }
};

/** \brief Read only reference to simplifier object */
class ro_simplifier {
    std::shared_ptr<simplifier_cell const> m_ptr;
public:
    typedef std::weak_ptr<simplifier_cell const> weak_ref;
    ro_simplifier(simplifier const & s);
    ro_simplifier(weak_ref const & s);
    explicit operator weak_ref() const { return weak_ref(m_ptr); }
    weak_ref to_weak_ref() const { return weak_ref(m_ptr); }
    simplifier_cell const * operator->() const { return m_ptr.get(); }
    simplifier_cell const & operator*() const { return *(m_ptr.get()); }
};

/**
   \brief Abstract class that specifies the interface for monitoring
   the behavior of the simplifier.
*/
class simplifier_monitor {
public:
    virtual ~simplifier_monitor() {}
    /**
       \brief This method is invoked to sign that the simplifier is starting to process the expression \c e.
    */
    virtual void pre_eh(ro_simplifier const & s, expr const & e) = 0;

    /**
       \brief This method is invoked to sign that \c e has be rewritten into \c new_e with proof \c pr.
       The proof is none if proof generation is disabled or if \c e and \c new_e are definitionally equal.
    */
    virtual void step_eh(ro_simplifier const & s, expr const & e, expr const & new_e, optional<expr> const & pr) = 0;
    /**
       \brief This method is invoked to sign that \c e has be rewritten into \c new_e using the conditional equation \c ceq.
    */
    virtual void rewrite_eh(ro_simplifier const & s, expr const & e, expr const & new_e, expr const & ceq, name const & ceq_id) = 0;

    enum class failure_kind { Unsupported, TypeMismatch, AssumptionNotProved, MissingArgument, PermutationGe, AbstractionBody };

    /**
       \brief This method is invoked when the simplifier fails to rewrite an application \c e.
       \c i is the argument where the simplifier gave up, and \c k is the reason for failure.
       Two possible values are: Unsupported or TypeMismatch (may happen when simplifying terms that use dependent types).
    */
    virtual void failed_app_eh(ro_simplifier const & s, expr const & e, unsigned i, failure_kind k) = 0;

    /**
       \brief This method is invoked when the simplifier fails to apply a conditional equation \c ceq to \c e.
       The \c ceq may have several arguments, the value \c i is the argument where the simplifier gave up, and \c k is the reason for failure.
       The possible failure values are: AssumptionNotProved (failed to synthesize a proof for an assumption required by \c ceq),
       MissingArgument (failed to infer one of the arguments needed by the conditional equation), PermutationGe
       (the conditional equation is a permutation, and the result is not smaller in the term ordering, \c i is irrelevant in this case).
    */
    virtual void failed_rewrite_eh(ro_simplifier const & s, expr const & e, expr const & ceq, name const & ceq_id, unsigned i, failure_kind k) = 0;

    /**
       \brief This method is invoked when the simplifier fails to simplify an abstraction (Pi or Lambda).
       The possible failure values are: Unsupported, TypeMismatch, and AbstractionBody (failed to rewrite the body of the abstraction,
       this may happen when we are using dependent types).
    */
    virtual void failed_abstraction_eh(ro_simplifier const & s, expr const & e, failure_kind k) = 0;
};

expr_pair simplify(expr const & e, ro_environment const & env, context const & ctx, options const & pts,
                   unsigned num_rs, rewrite_rule_set const * rs,
                   std::shared_ptr<simplifier_monitor> const & monitor = std::shared_ptr<simplifier_monitor>());
expr_pair simplify(expr const & e, ro_environment const & env, context const & ctx, options const & opts,
                   unsigned num_ns, name const * ns,
                   std::shared_ptr<simplifier_monitor> const & monitor = std::shared_ptr<simplifier_monitor>());
void open_simplifier(lua_State * L);
}
