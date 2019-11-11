/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class type_context_old;

/** \brief Function parameter information. */
class param_info {
    unsigned       m_implicit:1;
    unsigned       m_inst_implicit:1;
    unsigned       m_prop:1;
    unsigned       m_has_fwd_deps:1; // true if rest depends on this parameter
    list<unsigned> m_back_deps;      // previous arguments it depends on
public:
    param_info(bool imp, bool inst_imp, bool prop, bool has_fwd_deps, list<unsigned> const & back_deps):
        m_implicit(imp), m_inst_implicit(inst_imp), m_prop(prop),
        m_has_fwd_deps(has_fwd_deps), m_back_deps(back_deps) {}
    list<unsigned> const & get_back_deps() const { return m_back_deps; }
    bool is_implicit() const { return m_implicit; }
    bool is_inst_implicit() const { return m_inst_implicit; }
    bool is_prop() const { return m_prop; }
    bool has_fwd_deps() const { return m_has_fwd_deps; }
    void set_has_fwd_deps() { m_has_fwd_deps = true; }
};

/** \brief Function information produced by get_fun_info procedures. */
class fun_info {
    unsigned         m_arity;
    list<param_info> m_params_info;
    list<unsigned>   m_result_deps; // resulting type dependencies
public:
    fun_info():m_arity(0) {}
    fun_info(unsigned arity, list<param_info> const & info, list<unsigned> const & result_deps):
        m_arity(arity), m_params_info(info), m_result_deps(result_deps) {}
    unsigned get_arity() const { return m_arity; }
    list<param_info> const & get_params_info() const { return m_params_info; }
    list<unsigned> const & get_result_deps() const { return m_result_deps; }
};

fun_info get_fun_info(type_context_old & ctx, expr const & fn);
/** \brief Return information assuming the function has only nargs.
    \pre nargs <= get_fun_info(ctx, fn).get_arity() */
fun_info get_fun_info(type_context_old & ctx, expr const & fn, unsigned nargs);

/** \brief Subsingleton parameter information */
class subsingleton_param_info {
    /* m_specialized is true if the result of fun_info has been specifialized
       using this argument.
       For example, consider the function

             f : Pi (A : Type), A -> A

       Now, suppse we request get_specialize fun_info for the application

             f unit a

       fun_info_manager returns two param_info objects:
       1) m_specialized = true
       2) m_subsingleton = true

       Note that, in general, the second argument of f is not a subsingleton,
       but it is in this particular case/specialization.

       \remark This bit is only set if it is a dependent parameter (i.e., m_is_dep is true).

       Moreover, we only set m_specialized IF another parameter
       becomes a subsingleton or proposition. */
    unsigned short m_specialized;
    unsigned short m_subsingleton;
public:
    subsingleton_param_info(bool spec, bool ss):
        m_specialized(spec), m_subsingleton(ss) {}
    bool specialized() const { return m_specialized; }
    bool is_subsingleton() const { return m_subsingleton; }
    void set_specialized() { m_specialized = true; }
};

typedef subsingleton_param_info ss_param_info;
typedef list<ss_param_info>     ss_param_infos;

list<ss_param_info> get_subsingleton_info(type_context_old & ctx, expr const & fn);
list<ss_param_info> get_subsingleton_info(type_context_old & ctx, expr const & fn, unsigned nargs);
/** \brief Return subsingleton parameter information for the function application.
    This is more precise than \c get_subsingleton_info for dependent functions.

    Example: given (f : Pi (A : Type), A -> A), \c get_specialized_fun_info for

    f unit b

    returns a \c fun_info with two param_info
    1) m_specialized = true
    2) m_subsingleton = true

    The second argument is marked as subsingleton only because the resulting information
    is taking into account the first argument. */
list<ss_param_info> get_specialized_subsingleton_info(type_context_old & ctx, expr const & app);
unsigned get_specialization_prefix_size(type_context_old & ctx, expr const & fn, unsigned nargs);

void initialize_fun_info();
void finalize_fun_info();
}
