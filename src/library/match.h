/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "util/lua.h"
#include "util/optional.h"
#include "util/lbool.h"
#include "util/buffer.h"
#include "util/name_map.h"
#include "kernel/expr.h"
#include "kernel/environment.h"
#include "library/idx_metavar.h"

namespace lean {
/** \brief Context for match_plugins. */
class match_context {
public:
    /** \brief Create a fresh name. */
    virtual name mk_name() = 0;
    /** \brief Given a variable \c x, return its assignment (if available) */
    virtual optional<expr> get_subst(expr const & x) const = 0;
    /** \brief Given a universe level meta-variable \c x (created using #mk_idx_metauniv),
        return its assignment (if available) */
    virtual optional<level> get_subst(level const & x) const = 0;
    /** \brief Assign the variable \c x to \c e
        \pre \c x is not assigned
    */
    virtual void assign(expr const & x, expr const & e) = 0;
    /** \brief Assign the variable \c x to \c l
        \pre \c x is not assigned, \c x was created using #mk_idx_metauniv.
    */
    virtual void assign(level const & x, level const & l) = 0;
    virtual bool match(expr const & p, expr const & t) = 0;
};

/** \brief Callback for extending the higher-order pattern matching procedure.
    It is invoked before the matcher fails.

    plugin(p, t, s) must return true iff for updated substitution s', s'(p) is definitionally equal to t.
*/
class match_plugin {
public:
    virtual ~match_plugin() {}
    /** \brief The following method is invoked before the matcher tries to process
        \c p and \c t. The method is only invoked when \c p and \c t have the same kind,
        \c p is not a special metavariable created using \c mk_idx_metavar, and
        \c p and \c t are not structurally identical.

        The result should be:
        - l_false : did not match
        - l_true  : matched
        - l_undef : did not handled (i.e., default matcher should be used)
    */
    virtual lbool pre(expr const & /*p*/, expr const & /*t*/, match_context & /*ctx*/) const { return l_undef; }

    /** \brief The following method is invoked when matcher doesn't have anything else to do.
        This method is usually used to invoke expensive procedures such as the normalizer.
        It should return true it the plugin did manage to match p and t.
    */
    virtual bool on_failure(expr const & p, expr const & t, match_context & ctx) const = 0;
};

/** \brief Simple plugin that just puts terms in whnf and tries again */
class whnf_match_plugin : public match_plugin {
    type_checker & m_tc;
public:
    whnf_match_plugin(type_checker & tc):m_tc(tc) {}
    virtual bool on_failure(expr const & p, expr const & t, match_context & ctx) const;
};

/**
   \brief Matching for higher-order patterns. Return true iff \c t matches the higher-order pattern \c p.
   The substitution is stored in \c subst. Note that, this procedure treats "special" meta-variables
   (created using #mk_idx_metauniv and #mk_idx_metavar) as placeholders. The substitution of these
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
