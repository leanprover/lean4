/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "util/lua.h"
#include "util/optional.h"
#include "util/buffer.h"
#include "util/name_map.h"
#include "kernel/expr.h"
#include "kernel/environment.h"

namespace lean {
/** \brief Create a universe level metavariable that can be used as a placeholder in #hop_match.

    \remark The index \c i is encoded in the hierarchical name, and can be quickly accessed.
    In hop_match the substitution is also efficiently represented as an array (aka buffer).
*/
level mk_idx_meta_univ(unsigned i);

/** \brief Context for match_plugins. */
class match_context {
public:
    /** \brief Create a fresh name. */
    virtual name mk_name() = 0;
    /** \brief Given a variable \c x, return its assignment (if available) */
    virtual optional<expr> get_subst(expr const & x) const = 0;
    /** \brief Given a universe level meta-variable \c x (created using #mk_idx_meta_univ), return its assignment (if available) */
    virtual optional<level> get_subst(level const & x) const = 0;
    /** \brief Assign the variable \c x to \c e
        \pre \c x is not assigned
    */
    virtual void assign(expr const & x, expr const & e) = 0;
    /** \brief Assign the variable \c x to \c l
        \pre \c x is not assigned, \c x was created using #mk_idx_meta_univ.
    */
    virtual void assign(level const & x, level const & l) = 0;
    virtual bool match(expr const & p, expr const & t) = 0;
};

/** \brief Callback for extending the higher-order pattern matching procedure.
    It is invoked before the matcher fails.

    plugin(p, t, s) must return true iff for updated substitution s', s'(p) is definitionally equal to t.
*/
typedef std::function<bool(expr const &, expr const &, match_context &)> match_plugin; // NOLINT

/** \brief Create a match_plugin that puts terms in weak-head-normal-form before failing */
match_plugin mk_whnf_match_plugin(std::shared_ptr<type_checker> tc);
match_plugin mk_whnf_match_plugin(type_checker & tc);

/**
   \brief Matching for higher-order patterns. Return true iff \c t matches the higher-order pattern \c p.
   The substitution is stored in \c subst. Note that, this procedure treats free-variables as placholders
   instead of meta-variables.

   \c subst is an assignment for the free variables occurring in \c p.

   \pre \c t must not contain free variables. If it does, they must be replaced with local constants
   before invoking this functions.

   \c p is a higher-order pattern when in all applications in \c p
      1- A free variable is not the function OR
      2- A free variable is the function, but all other arguments are distinct local constants.

   \pre \c subst must be big enough to store all free variables occurring in subst

   If prefix is provided, then it is used for creating unique names.

   If name_subst is different from nullptr, then the procedure stores in name_subst
   a mapping for binder names. It maps the binder names used in the pattern \c p into
   the binder names used in \c t.

   If the plugin is provided, then it is invoked before a failure.

   If \c assigned is provided, then it is set to true if \c esubst or \c lsubst is updated.
*/
bool match(expr const & p, expr const & t, buffer<optional<expr>> & esubst, buffer<optional<level>> & lsubst,
           name const * prefix = nullptr, name_map<name> * name_subst = nullptr, match_plugin const * plugin = nullptr,
           bool * assigned = nullptr);
void open_match(lua_State * L);
void initialize_match();
void finalize_match();
}
