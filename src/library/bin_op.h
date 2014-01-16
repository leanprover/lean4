/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/kernel.h"

namespace lean {
/**
   \brief Return unit if <tt>num_args == 0</tt>, args[0] if <tt>num_args == 1</tt>, and
   <tt>(op args[0] (op args[1] (op ... )))</tt>
*/
expr mk_bin_rop(expr const & op, expr const & unit, unsigned num_args, expr const * args);
expr mk_bin_rop(expr const & op, expr const & unit, std::initializer_list<expr> const & l);

/**
   \brief Return unit if <tt>num_args == 0</tt>, args[0] if <tt>num_args == 1</tt>, and
   <tt>(op ... (op (op args[0] args[1]) args[2]) ...)</tt>
*/
expr mk_bin_lop(expr const & op, expr const & unit, unsigned num_args, expr const * args);
expr mk_bin_lop(expr const & op, expr const & unit, std::initializer_list<expr> const & l);

inline expr mk_implies(unsigned num_args, expr const * args) { return mk_bin_rop(mk_implies_fn(), False, num_args, args); }
inline expr Implies(std::initializer_list<expr> const & l) { return mk_implies(l.size(), l.begin()); }

inline expr mk_and(unsigned num_args, expr const * args) { return mk_bin_rop(mk_and_fn(), True, num_args, args); }
inline expr And(std::initializer_list<expr> const & l) { return mk_and(l.size(), l.begin()); }

inline expr mk_or(unsigned num_args, expr const * args) { return mk_bin_rop(mk_or_fn(), False, num_args, args); }
inline expr Or(std::initializer_list<expr> const & l) { return mk_or(l.size(), l.begin()); }
}
