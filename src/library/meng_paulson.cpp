/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

This module implements a heuristic for selecting relevant theorems based on
the approach described at

   "Lightweight relevance filtering for machine-generated resolution problems"
   Jia Meng and Larry Paulson
   Journal of Applied Logic 7 2009
*/
#include <math.h>
#include "util/sexpr/option_declarations.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "library/decl_stats.h"
#include "library/private.h"
#include "library/class.h"
#include "library/constants.h"

#ifndef LEAN_DEFAULT_MENG_PAULSON_P
#define LEAN_DEFAULT_MENG_PAULSON_P 0.6
#endif

#ifndef LEAN_DEFAULT_MENG_PAULSON_C
#define LEAN_DEFAULT_MENG_PAULSON_C 2.4
#endif

namespace lean {
static name * g_meng_paulson_p = nullptr;
static name * g_meng_paulson_c = nullptr;

void initialize_meng_paulson() {
    g_meng_paulson_p = new name{"meng_paulson", "p"};
    g_meng_paulson_c = new name{"meng_paulson", "c"};

    register_double_option(*g_meng_paulson_p, LEAN_DEFAULT_MENG_PAULSON_P,
                           "(theorem selection) control parameter for the Meng&Paulson theorem selection heuristic"
                           "(for details see paper \"Lightweight relevance filtering for machine-generated resolution problems)\"");
    register_double_option(*g_meng_paulson_c, LEAN_DEFAULT_MENG_PAULSON_C,
                           "(theorem selection) control parameter for the Meng&Paulson theorem selection heuristic"
                           "(for details see paper \"Lightweight relevance filtering for machine-generated resolution problems)\"");
}

void finalize_meng_paulson() {
    delete g_meng_paulson_p;
    delete g_meng_paulson_c;
}

double get_meng_paulson_p(options const & o) {
    return o.get_double(*g_meng_paulson_p, LEAN_DEFAULT_MENG_PAULSON_P);
}

double get_meng_paulson_c(options const & o) {
    return o.get_double(*g_meng_paulson_c, LEAN_DEFAULT_MENG_PAULSON_C);
}

class relevant_thms_fn {
    environment m_env;
    double      m_p;
    double      m_c;
    name_set    m_relevant;

    double get_weight(name const & n) const {
        double r = get_num_occs(m_env, n);
        return 1.0 + 2.0 / log(r + 1.0);
    }

    bool is_connective(name const & n) const {
        return
            n == get_or_name() ||
            n == get_and_name() ||
            n == get_not_name() ||
            n == get_iff_name() ||
            n == get_not_name() ||
            n == get_ite_name() ||
            n == get_true_name() ||
            n == get_false_name();
    }

    // constants symbols in theorem types that should be ignored
    bool ignore_F(name const & F) const {
        if (is_private(m_env, F))
            return true; // we ignore private decls
        if (is_class_instance_somewhere(m_env, F))
            return true; // ignore if F is a class or class-instance in some namespace
        if (is_connective(F))
            return true;
        return false;
    }

    // Theorems/Axioms that should be ignored
    bool ignore_T(name const & T) const {
        if (is_private(m_env, T))
            return true;
        if (inductive::is_elim_rule(m_env, T))
            return true;
        if (inductive::is_intro_rule(m_env, T))
            return true;
        return false;
    }

    double get_thm_score(name const & n) const {
        name_set s  = get_use_set(m_env, n);
        unsigned IR = 0;
        double M = 0.0;
        s.for_each([&](name const & F) {
                if (ignore_F(F))
                    return;
                if (m_relevant.contains(F)) {
                    M += get_weight(F);
                } else {
                    // std::cout << "IR: " << F << "\n";
                    IR++;
                }
            });
        // std::cout << n << " M: " << M << " IR: " << IR << "\n";
        if (M > 0.0)
            return M / (M + IR);
        else
            return 0.0;
    }
public:
    relevant_thms_fn(environment const & env, double p, double c, name_set const & rel):
        m_env(env), m_p(p), m_c(c), m_relevant(rel) {
        lean_assert(c > 0.0);
    }

    name_set operator()() {
        name_set A;
        // unsigned i = 1;
        while (true) {
            // std::cout << "#" << i << ", p: " << m_p << "\n";
            name_set Rel;
            m_relevant.for_each([&](name const & c) {
                    name_set used_by = get_used_by_set(m_env, c);
                    used_by.for_each([&](name const & T) {
                            declaration const & T_decl = m_env.get(T);
                            if (A.contains(T))
                                return; // T is already in the result set
                            if (!T_decl.is_theorem() && !T_decl.is_axiom())
                                return; // we only care about axioms and theorems
                            if (ignore_T(T))
                                return; // we ignore private decls
                            double M = get_thm_score(T);
                            // std::cout << T << " : " << M << "\n";
                            if (M < m_p)
                                return; // score is to low
                            Rel.insert(T);
                            A.insert(T);
                        });
                });
            if (Rel.empty())
                break;
            // include symbols of new theorems in m_relevant
            Rel.for_each([&](name const & T) {
                    name_set uses = get_use_set(m_env, T);
                    uses.for_each([&](name const & F) {
                            declaration const & F_decl = m_env.get(F);
                            if (F_decl.is_theorem() || F_decl.is_axiom())
                                return; // we ignore theorems occurring in types
                            if (ignore_F(F))
                                return;
                            // if (!m_relevant.contains(F))
                            //    std::cout << "new relevant: " << F << "\n";
                            m_relevant.insert(F);
                        });
                });
            m_p = m_p + (1.0 - m_p) / m_c;
        }
        return A;
    }
};

name_set get_relevant_thms(environment const & env, double p, double c,
                           name_set const & relevant_symbols) {
    return relevant_thms_fn(env, p, c, relevant_symbols)();
}

name_set get_relevant_thms(environment const & env, options const & o, name_set const & relevant_symbols) {
    return relevant_thms_fn(env, get_meng_paulson_p(o), get_meng_paulson_c(o), relevant_symbols)();
}
}
