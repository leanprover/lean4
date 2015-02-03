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
/** \brief Create a universe level metavariable that can be used as a placeholder in #match.

    \remark The index \c i is encoded in the hierarchical name, and can be quickly accessed.
    In the match procedure the substitution is also efficiently represented as an array (aka buffer).
*/
level mk_idx_meta_univ(unsigned i);

/** \brief Create a special metavariable that can be used as a placeholder in #match.

    \remark The index \c i is encoded in the hierarchical name, and can be quickly accessed.
    In the match procedure the substitution is also efficiently represented as an array (aka buffer).
*/
expr mk_idx_meta(unsigned i, expr const & type);

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
   The substitution is stored in \c subst. Note that, this procedure treats "special" meta-variables
   (created using #mk_idx_meta_univ and #mk_idx_meta) as placeholders. The substitution of these
   metavariable can be quickly accessed using an index stored in them. The parameters
   \c esubst and \c lsubst store the substitutions for them. There are just buffers.

   \pre \p and \c t must not contain free variables. Thus, free-variables must be replaced with local constants
   before invoking this function.

   Other (non special) meta-variables are treated as opaque constants.

   \c p is a higher-order pattern when in all applications in \c p
      1- A special meta-variable is not the function OR
      2- A special meta-variable is the function, but all other arguments are distinct local constants.

   \pre \c esubst and \c lsubst must be big enough to store the substitution.
   That is, their size should be > than the index of any special metavariable occuring in p.

   If prefix is provided, then it is used for creating unique names.

   If name_subst is different from nullptr, then the procedure stores in name_subst
   a mapping for binder names. It maps the binder names used in the pattern \c p into
   the binder names used in \c t.

   If the plugin is provided, then it is invoked before a failure.

   If \c assigned is provided, then it is set to true if \c esubst or \c lsubst is updated.
*/
bool match(expr const & p, expr const & t, buffer<optional<level>> & lsubst, buffer<optional<expr>> & esubst,
           name const * prefix = nullptr, name_map<name> * name_subst = nullptr, match_plugin const * plugin = nullptr,
           bool * assigned = nullptr);
bool match(expr const & p, expr const & t,
           unsigned lsubst_sz, optional<level> * lsubst,
           unsigned esubst_sz, optional<expr> * esubst,
           name const * prefix = nullptr, name_map<name> * name_subst = nullptr,
           match_plugin const * plugin = nullptr, bool * assigned = nullptr);

void open_match(lua_State * L);
void initialize_match();
void finalize_match();
}
