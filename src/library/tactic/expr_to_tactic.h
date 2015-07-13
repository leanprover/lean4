/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/pos_info_provider.h"
#include "library/tactic/tactic.h"
#include "library/tactic/elaborate.h"

namespace lean {
/**
   \brief Return true iff the environment \c env contains the following declarations
   in the namespace 'tactic'
       tactic.builtin : tactic
       and_then : tactic -> tactic -> tactic
       or_else  : tactic -> tactic -> tactic
       repeat   : tactic -> tactic
*/
bool has_tactic_decls(environment const & env);

/**
   \brief Creates a tactic by 'executing' \c e. Definitions are unfolded, whnf procedure is invoked,
   and definitions marked as 'tactic.builtin' are handled by the code registered using
   \c register_expr_to_tactic.
*/
tactic expr_to_tactic(environment const & env, elaborate_fn const & fn, expr const & e, pos_info_provider const * p);
// auxiliary procedure used to compile nested tactic in tacticals
tactic expr_to_tactic(type_checker & tc, elaborate_fn const & fn, expr e, pos_info_provider const * p);

name const & get_tactic_name();

unsigned get_unsigned_arg(type_checker & tc, expr const & e, unsigned i);
optional<unsigned> get_optional_unsigned(type_checker & tc, expr const & e);

expr const & get_tactic_expr_type();
expr const & get_tactic_identifier_type();
expr mk_tactic_expr(expr const & e);
bool is_tactic_expr(expr const & e);
expr const & get_tactic_expr_expr(expr const & e);
void check_tactic_expr(expr const & e, char const * msg);
expr const & get_tactic_expr_list_type();
expr const & get_tactic_using_expr_type();

expr mk_expr_list(unsigned num, expr const * args);

name const & tactic_expr_to_id(expr e, char const * error_msg);
void get_tactic_expr_list_elements(expr l, buffer<expr> & r, char const * error_msg);
void get_tactic_id_list_elements(expr l, buffer<name> & r, char const * error_msg);
expr ids_to_tactic_expr(buffer<name> const & ids);

/**
   \brief Create an expression `by t`, where \c t is an expression of type `tactic`.
   This kind of expression only affects the elaborator, the kernel will reject
   any declaration that contains it.

   \post get_by_arg(mk_by(t)) == t
   \post is_by(mk_by(t))
*/
expr mk_by(expr const & t);
/** \brief Return true iff \c t is an expression created using \c mk_by */
bool is_by(expr const & t);
/** \see mk_by */
expr const & get_by_arg(expr const & t);

// Similar to mk_by, but instructs the elaborator to include the whole context
expr mk_by_plus(expr const & t);
bool is_by_plus(expr const & t);
expr const & get_by_plus_arg(expr const & t);

expr const & get_tactic_type();
expr const & get_and_then_tac_fn();
expr const & get_or_else_tac_fn();
expr const & get_id_tac_fn();
expr const & get_repeat_tac_fn();
expr const & get_determ_tac_fn();

/** \brief Exception used to report a problem when an expression is being converted into a tactic. */
class expr_to_tactic_exception : public exception {
    expr m_expr;
public:
    expr_to_tactic_exception(expr const & e, char const * msg):exception(msg), m_expr(e) {}
    expr_to_tactic_exception(expr const & e, sstream const & strm):exception(strm), m_expr(e) {}
    expr const & get_expr() const { return m_expr; }
};

typedef std::function<tactic(type_checker &, elaborate_fn const & fn, expr const &, pos_info_provider const *)>
expr_to_tactic_fn;

/** \brief Register a new "procedural attachment" for expr_to_tactic. */
void register_tac(name const & n, expr_to_tactic_fn const & fn);
// remark: we cannot use "std::function <...> const &" in the following procedures, for some obscure reason it produces
// memory leaks when we compile using clang 3.3
void register_simple_tac(name const & n, std::function<tactic()> f);
void register_bin_tac(name const & n, std::function<tactic(tactic const &, tactic const &)> f);
void register_unary_tac(name const & n, std::function<tactic(tactic const &)> f);
void register_unary_num_tac(name const & n, std::function<tactic(tactic const &, unsigned)> f);
void register_num_tac(name const & n, std::function<tactic(unsigned k)> f);

void initialize_expr_to_tactic();
void finalize_expr_to_tactic();
}
