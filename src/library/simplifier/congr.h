/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "kernel/environment.h"

namespace lean {
/*
  By default, Lean's simplifier will use the standard congruence theorem.
  To simplify (f s), it will simplify f and s, and obtain the new terms
  f' and s', and proofs H_f and H_s
             H_f : f = f'
             H_s : s = s'
  Then, it uses the congr theorem to obtain
             congr H_f H_s : f s = f' s'

  This behavior can be customize by providing specialized congruence rules
  for specific operators.

  For example, kernel.lean contains the theorem:

  theorem or_congrr {a b c d : Bool} (H_ac : ∀ (H_nb : ¬ b), a = c) (H_bd : ∀ (H_nc : ¬ c), b = d) : a ∨ b ↔ c ∨ d

  It tells us that we can simplify a ∨ b, by first simplifying a under the assumption that b is false,
  and then simplifying b under the assumption that the result of a simplification is false.

  We say or_congrr is a congruence theorem. This module is used to identify congruence theorems and
  "compile" them into simple instructions that can be efficiently applied by the simplifier.
*/
class congr_theorem_info {
    friend congr_theorem_info check_congr_theorem(ro_environment const & env, expr const & e);
public:
    /**
       \brief Each argument may or may not be simplified under a new context.
       For example, in or_congrr, b is simplified under a context containing not c.

       This class store this dependency.
    */
    class context {
        friend congr_theorem_info check_congr_theorem(ro_environment const & env, expr const & e);
        /**
            The position of the dependent argument. For or_congrr this field has value 0 for b,
            since b depends on the new value c of a (after simplification).
        */
        unsigned  m_arg;
        /**
            Indicate whether is a positive or negative dependency.
            For or_congrr, this field is false for b, since it depends negatively on c.
        */
        bool      m_pos;
        /**
           Indicate whether the dependecy is before/after simplification.
           For or_congrr, this field is true for b, since it depends on the new value c of a (after simplification).
        */
        bool      m_new;
        context(unsigned arg, bool pos, bool n):m_arg(arg), m_pos(pos), m_new(n) {}
    public:
        unsigned get_arg_pos() const { return m_arg; }
        bool     is_pos_dep()  const { return m_pos; }
        bool     use_new_val() const { return m_new; }
        void display(std::ostream & out) const;
    };

    /**
       \brief This class indicates how to process an argument of the function application.
    */
    class app_arg_info {
        friend congr_theorem_info check_congr_theorem(ro_environment const & env, expr const & e);
        /**
           \brief Position of the argument to be processed.
           For or_congrr, this field is 2 for b.
        */
        unsigned m_arg_pos;
        /**
           \brief The context (if any) is used to simplify the argument
        */
        optional<context> m_context;
        /**
           \brief Position where this argument goes in the proof term.
           For or_congrr, this field is 1 for b.
        */
        unsigned m_proof_arg_pos;
        /**
           \brief Position where the simplified argument goes in the proof term.
           If the argument should not be simplified, then this field is none.

           For or_congrr, this field is 3 for b.
        */
        optional<unsigned> m_proof_new_arg_pos;
        /**
           \brief Position where the proof for new = old goes in the proof term.

           For or_congrr, this field is 5 for b.
        */
        optional<unsigned> m_proof_proof_pos;
        app_arg_info(unsigned arg_pos, unsigned proof_arg_pos):m_arg_pos(arg_pos), m_proof_arg_pos(proof_arg_pos) {}
        app_arg_info(unsigned arg_pos, unsigned proof_arg_pos, unsigned proof_new_arg_pos):
            m_arg_pos(arg_pos), m_proof_arg_pos(proof_arg_pos), m_proof_new_arg_pos(proof_new_arg_pos) {}
    public:
        unsigned get_arg_pos() const { return m_arg_pos; }
        optional<context> const & get_context() const { return m_context; }
        unsigned get_pos_at_proof() const { return m_proof_arg_pos; }
        optional<unsigned> const & get_new_pos_at_proof() const { return m_proof_new_arg_pos; }
        optional<unsigned> const & get_proof_pos_at_proof() const { return m_proof_proof_pos; }
        void display(std::ostream & out) const;
    };

private:
    /**
       Indicate for which function this theorem is a congruence for.
    */
    expr     m_fun;

    /**
        Proof term for the theorem, in most cases is just a constant (e.g., or_congrr) that references a theorem in a Lean environment.
    */
    expr     m_proof;
    /**
        Number of arguments the theorem takes. For example, or_congrr has 6 arguments.
    */
    unsigned m_num_proof_args;
    /**
       \brief Store the sequence the application arguments should be processed.
    */
    std::vector<app_arg_info> m_arg_info;
public:
    expr const & get_fun() const { return m_fun; }
    expr const & get_proof() const { return m_proof; }
    unsigned     get_num_proof_args() const { return m_num_proof_args; }
    std::vector<app_arg_info> const & get_arg_info() const { return m_arg_info; }
    void display(std::ostream & out) const;
};

/**
   \brief Check whether \c e is a congruence theorem in the given environment.
   If it is, then returns a congr_theorem_info object. Otherwise, throws an exception.
*/
congr_theorem_info check_congr_theorem(ro_environment const & env, expr const & e);
}
