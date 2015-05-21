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
typedef std::function<format(formatter const &, pos_info_provider const *, substitution const &, bool)> pp_jst_fn;

class justification_set;

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
    format pp_core(formatter const & fmt, pos_info_provider const * p, substitution const & s,
                   justification_set & visited, bool is_main) const;
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
    bool is_wrapper() const;

    justification_cell * raw() const { return m_ptr; }

    justification & operator=(justification const & s);
    justification & operator=(justification && s);
    /**
       \brief Convert this justification into a format object. This method is usually used to report
       "error" messages to users.
    */
    format pp(formatter const & fmt, pos_info_provider const * p, substitution const & s) const;
    /**
       \brief Return an expression associated with the justification object.
    */
    optional<expr> get_main_expr() const;

    friend justification mk_composite(justification const & j1, justification const & j2, optional<expr> const & s, pp_jst_fn const & fn);
    friend justification mk_composite1(justification const & j1, justification const & j2);
    friend justification mk_wrapper(justification const & j, optional<expr> const & s, pp_jst_fn const & fn);
    friend justification mk_assumption_justification(unsigned idx, optional<expr> const & s, pp_jst_fn const & fn);
    friend justification mk_assumption_justification(unsigned idx);
    friend justification mk_justification(optional<expr> const & s, pp_jst_fn const & fn);

    friend bool is_eqp(justification const & j1, justification const & j2) { return j1.raw() == j2.raw(); }
};

/**
   \brief Simpler version of pp_jst_fn
*/
typedef std::function<format(formatter const &, substitution const &)> pp_jst_sfn;

/** \brief Return a format object containing position information for the given expression (if available) */
format to_pos(optional<expr> const & e, pos_info_provider const * p);
format pp_previous_error_header(formatter const &, pos_info_provider const * pos_prov, optional<expr> const & ref, bool is_main);

/** \brief Provide a custom pretty printer for \c j */
justification mk_wrapper(justification const & j, optional<expr> const & s, pp_jst_fn const & fn);
/**
   \brief Combine the two given justifications into a new justification object, and use
   the given function to convert the justification into a format object.
*/
justification mk_composite(justification const & j1, justification const & j2, optional<expr> const & s, pp_jst_fn const & fn);
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
justification mk_assumption_justification(unsigned idx, optional<expr> const & s, pp_jst_fn const & fn);
/**
   \brief Similar to the previous function, but fn just returns the format object "assumption idx", and s is the none.
*/
justification mk_assumption_justification(unsigned idx);
/**
   \brief Create a justification for constraints produced by the type checker.
*/
justification mk_justification(optional<expr> const & s, pp_jst_fn const & fn);
justification mk_justification(char const * msg, optional<expr> const & s = none_expr());
/**
   \brief Create a justification for constraints produced by the type checker.
   It is similar to the previous function, but the position of \c s will be automatically included.
*/
justification mk_justification(optional<expr> const & s, pp_jst_sfn const & fn);
inline justification mk_justification(expr const & s, pp_jst_sfn const & fn) {
    return mk_justification(some_expr(s), fn);
}

/**
   \brief Return the child of a wrapper justification.
   \pre j.is_composite()
*/
justification const & wrapper_child(justification const & j);
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

/** \brief Object to simulate delayed justification creation. */
class delayed_justification {
public:
    virtual ~delayed_justification() {}
    virtual justification get() = 0;
};

class no_delayed_justification : public delayed_justification {
public:
    virtual justification get() { return justification(); }
};

class simple_delayed_justification : public delayed_justification {
    optional<justification>        m_jst;
    std::function<justification()> m_mk;
public:
    template<typename Mk> simple_delayed_justification(Mk && mk):m_mk(mk) {}
    virtual justification get() { if (!m_jst) { m_jst = m_mk(); } return *m_jst; }
};

class as_delayed_justification : public delayed_justification {
    justification m_jst;
public:
    as_delayed_justification(justification const & j):m_jst(j) {}
    virtual justification get() { return m_jst; }
};
}
