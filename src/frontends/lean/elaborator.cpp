/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/name_set.h"
#include "kernel/normalizer.h"
#include "kernel/context.h"
#include "kernel/builtin.h"
#include "kernel/free_vars.h"
#include "kernel/for_each.h"
#include "kernel/replace.h"
#include "kernel/instantiate.h"
#include "kernel/metavar.h"
#include "kernel/printer.h"
#include "library/placeholder.h"
#include "library/reduce.h"
#include "library/update_expr.h"
#include "library/expr_pair.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/elaborator_exception.h"

namespace lean {
static name g_choice_name = name::mk_internal_unique_name();
static expr g_choice = mk_constant(g_choice_name);
static format g_assignment_fmt  = format(":=");
static format g_unification_u_fmt = format("\u2248");
static format g_unification_fmt = format("=?=");

expr mk_choice(unsigned num_fs, expr const * fs) {
    lean_assert(num_fs >= 2);
    return mk_eq(g_choice, mk_app(num_fs, fs));
}

bool is_choice(expr const & e) {
    return is_eq(e) && eq_lhs(e) == g_choice;
}

unsigned get_num_choices(expr const & e) {
    lean_assert(is_choice(e));
    return num_args(eq_rhs(e));
}

expr const & get_choice(expr const & e, unsigned i) {
    lean_assert(is_choice(e));
    return arg(eq_rhs(e), i);
}

elaborator::elaborator(frontend const & ) {}
elaborator::~elaborator() {}
expr elaborator::operator()(expr const & e) { return e; }
expr elaborator::operator()(expr const & e, expr const & /* expected_type */) { return e; }
expr const & elaborator::get_original(expr const & e) const { return e; }
void elaborator::set_interrupt(bool ) {}
void elaborator::clear() {}
environment const & elaborator::get_environment() const {
    static thread_local environment g_env;
    return g_env;
}
void elaborator::display(std::ostream & ) const {}
format elaborator::pp(formatter &, options const &) const { return format(); }
void elaborator::print(imp * ptr) { lean_assert(ptr); }
bool elaborator::has_constraints() const { return false; }
}
