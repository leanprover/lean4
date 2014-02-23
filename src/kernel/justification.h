/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/debug.h"
#include "util/rc.h"
#include "util/buffer.h"
#include "util/sexpr/format.h"
#include "kernel/expr.h"
#include "kernel/formatter.h"
#include "kernel/pos_info_provider.h"

namespace lean {
class substitution;
struct justification_cell;

/**
   \brief When a set of constraints cannot be solved, we must print some "error" message to the user.
   The pp_jst_fn is a generic funciton that produces these messages. We can associate these functions
   to justification objects.
*/
typedef std::function<format(formatter const &, options const &, pos_info_provider const *, substitution const &)> pp_jst_fn;

/**
    \brief Objects used to justify unification (and level) constraints and metavariable assignments.

    There are 4 basic kinds of justification:
    - None:       the null justification.
    - Asserted:   a justification produced by the type checker.
    - Assumption: for case-splits inside the elaborator and other constraint solvers.
    - Composite:  the combination of two other justification objects.

    A composite justification is used, for example, to justify a constraint produced by
    replacing a metavariable ?M by its assignment in a constraint C.
*/
class justification {
    justification_cell * m_ptr;
    justification(justification_cell * ptr);
public:
    justification();
    justification(justification const & s);
    justification(justification && s);
    ~justification();

    friend void swap(justification & a, justification & b) { std::swap(a.m_ptr, b.m_ptr); }

    bool is_none() const;
    bool is_asserted() const;
    bool is_assumption() const;
    bool is_composite() const;

    justification_cell * raw() const { return m_ptr; }

    justification & operator=(justification const & s);
    justification & operator=(justification && s);
    /**
       \brief Convert this justification into a format object. This method is usually used to report
       "error" messages to users.
    */
    format pp(formatter const & fmt, options const & opts, pos_info_provider const * p, substitution const & s);
    /**
       \brief Return an expression associated with the justification object.
    */
    optional<expr> get_main_expr() const;

    friend justification mk_composite(justification const & j1, justification const & j2, pp_jst_fn const & fn, optional<expr> const & s);
    friend justification mk_composite1(justification const & j1, justification const & j2);
    friend justification mk_assumption_justification(unsigned idx, pp_jst_fn const & fn, optional<expr> const & s);
    friend justification mk_assumption_justification(unsigned idx);
    friend justification mk_justification(pp_jst_fn const & fn, optional<expr> const & s);
};

/**
   \brief Simplifer version of pp_jst_fn
*/
typedef std::function<format(formatter const &, options const &, substitution const &)> pp_jst_sfn;

/** \brief Return a format object containing position information for the given expression (if available) */
format to_pos(optional<expr> const & e, pos_info_provider const * p);

/**
   \brief Combine the two given justifications into a new justification object, and use
   the given function to convert the justification into a format object.
*/
justification mk_composite(justification const & j1, justification const & j2, pp_jst_fn const & fn, optional<expr> const & s);
/**
   \brief Similar to \c mk_composite, but uses \c j1.pp to convert the
   resulting justification into a format object.
*/
justification mk_composite1(justification const & j1, justification const & j2);
/**
   \brief Alias for \c mk_composite1
*/
justification mk_substitution_justification(justification const & j1, justification const & j2);
/**
   \brief Create a "case-split" justification with the given \c idx.
*/
justification mk_assumption_justification(unsigned idx, pp_jst_fn const & fn, optional<expr> const & s);
/**
   \brief Similar to the previous function, but fn just returns the format object "assumption idx", and s is the none.
*/
justification mk_assumption_justification(unsigned idx);
/**
   \brief Create a justification for constraints produced by the type checker.
*/
justification mk_justification(pp_jst_fn const & fn, optional<expr> const & s);
/**
   \brief Create a justification for constraints produced by the type checker.
   It is similar to the previous function, but the position of \c s will be automatically included.
*/
justification mk_justification(pp_jst_sfn const & fn, optional<expr> const & s);

/**
   \brief Return the first child of a composite justification.
   \pre j.is_composite()
*/
justification const & composite_child1(justification const & j);
/**
   \brief Return the second child of a composite justification.
   \pre j.is_composite()
*/
justification const & composite_child2(justification const & j);
/**
   \brief Return the index of an assumption justification.
   \pre j.is_assumption()
*/
unsigned assumption_idx(justification const & j);

/** \brief Return true iff \c j depends on the assumption with index \c i. */
bool depends_on(justification const & j, unsigned i);

/** \brief Printer for debugging purposes */
std::ostream & operator<<(std::ostream & out, justification const & j);
}
