/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "library/tmp_type_context.h"
#include "library/fun_info_manager.h"
#include "library/annotation.h"
#include "library/scoped_ext.h"
#include "library/idx_metavar.h"
#include "library/blast/forward/pattern.h"

namespace lean {
/*
Step 1: Selecting which variables we should track.

Given (H : Pi (a_1 : A_1) ... (a_n : A_n), B) where B is not a Pi,
we use the following procedure to decide which a_i's must be in
patterns used by heuristic instantiation.

- We say an a_i that must occur in a pattern is "trackable".

- Let Trackable be the set of "trackable" a_i's

- for i := 1 to n
  a) If there is j > i, type(a_j) depends on a_i,
     and type(a_i) is not higher-order, then
     a_i is NOT trackable.
     Reason: we can infer a_i from a_j using type inference.

  b) a_i is a proposition -> a_i is NOT trackable.
     Reason: we can leave a_i as hypothesis whenever we instantiate H.

  c) a_i is instance implicit -> a_i is NOT trackable.
     We should use type class resolution to infer a_i.

  d) Otherwise, we add a_i into Trackable

Remark: we say a (multi-)pattern for H is valid iff it contains all
trackable a_i's.

Remark: we say a_i is a "residue" hypothesis iff
a_i is a proposition, is not instance-implicit, and (there is no j > i s.t. a_j is trackable
and type(a_j) depends on a_i, and type(a_i) is not higher-order)

That is, if a_i is a "residue" hypothesis, we cannot inferred it
by using type inference or type class resolution.

Residue hypotheses are the hypotheses for any instance of H produced by
the heuristic instantiation module.

Step 2a: H contains user-provided pattern hints
The user may provide pattern hints by annotating subterms of H using
the notation (:t:).

Example: The term (g x y) is a pattern hint at (H : forall x y, f (:g x y:) = x).

Let S be the set of patterns hints contained in H.
Then, a multi-pattern P is any subset of S s.t.
    a) P contains all trackable a_i's in H
    b) There is no strict subset of P that contains all trackable a_i's in H

If S is not empty, Lean will generate an error if there is no multi-pattern P for S.

The option pattern.max is a threshold on the number of patterns that can be generated.
Lean will generate an error if more than pattern.max can be generated using the
set S.

Step 2b: H does NOT contain user-provided pattern hints.

When pattern hints are not provided, Lean uses a heuristic for selecting patterns.

- Lean will only consider terms that do NOT contain constants marked with the hint attribute
[no_pattern]. In the standard library, we use this attribute to mark constants such as
'and', 'or', 'not', 'iff', 'eq', 'heq', etc.
Whenever blast has builtin support for handling a symbol (e.g., blast has support for logical connectives),
it is better to use it than using heuristic instantiation.

- Lean will look for candidate patterns in B and residue hypotheses.
Actually, it uses the following approach (TODO(Leo): should we provide options to control it?)
   1) Lean tries to find multi-patterns in B (only). If it finds at least one, then it is done, otherwise
   2) Lean tries to find multi-patterns in residue hypotheses only.
      If it finds at leat one, then it is done, otherwise
   3) Lean tries to find multi-patterns using residue hypotheses and B.
      If it can't find at least one, it signs an error.

- So, from now on, we will assume T is the set of terms where we will look for patterns.
We use trackable(p) to denote the set of trackable variables in p.
Lean will try to find "minimal" patterns and rank candidates in the following way
     Given terms p and q where both do not contain [no_pattern] constants, we say
     term p is "better" than q
     IFF
       1) trackable(p) is a strict superset of trackable(q) OR
       2) trackable(p) == trackable(q), but p is as subterm of q.

Given T, we collect a set of candidates C s.t., for each c_1 in C, there is no c_2 in C s.t. c_2 is better than c_1.

If there is c in C s.t. c contains all trackable a_i's, then all such c in C is our set of patterns (done).

To mimize the number of multi-patterns to be considered, we delete from C
any candidate c_1 in C if there is a c_2 in C s.t.
trackable(c_1) == trackable(c_2) and size(c_1) > size(c_2).

We say a subset M of C is a multi-pattern if M contains all trackable variables.
We say a multi-pattern M is minimal if no strict subset of M is a multi-pattern.

If the set of minimal multi-patterns for C is bigger than `pattern.max`, then we generate an error.
That is, the user should provide pattern-hints.
*/
static name * g_pattern_hint = nullptr;

expr mk_pattern_hint(expr const & e) { return mk_annotation(*g_pattern_hint, e); }
bool is_pattern_hint(expr const & e) { return is_annotation(e, *g_pattern_hint); }
expr const & get_pattern_hint_arg(expr const & e) { lean_assert(is_pattern_hint(e)); return get_annotation_arg(e); }
bool has_pattern_hints(expr const & e) {
    return static_cast<bool>(find(e, [](expr const & e, unsigned) { return is_pattern_hint(e); }));
}

static name * g_no_pattern_name = nullptr;
static std::string * g_key      = nullptr;

struct no_pattern_config {
    typedef name_set state;
    typedef name     entry;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        s.insert(e);
    }

    static name const & get_class_name() {
        return *g_no_pattern_name;
    }

    static std::string const & get_serialization_key() {
        return *g_key;
    }

    static void  write_entry(serializer & s, entry const & e) {
        s << e;
    }

    static entry read_entry(deserializer & d) {
        entry e;
        d >> e;
        return e;
    }

    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.hash());
    }
};

template class scoped_ext<no_pattern_config>;
typedef scoped_ext<no_pattern_config> no_pattern_ext;

bool is_no_pattern(environment const & env, name const & n) {
    return no_pattern_ext::get_state(env).contains(n);
}

environment add_no_pattern(environment const & env, name const & n, bool persistent) {
    return no_pattern_ext::add_entry(env, get_dummy_ios(), n, persistent);
}

name_set const & get_no_patterns(environment const & env) {
    return no_pattern_ext::get_state(env);
}

/** pattern_le */
struct pattern_le_fn {
    tmp_type_context & m_ctx;

    bool is_le_app(expr const & e1, expr const & e2) {
        if (is_app(e1) && is_app(e2)) {
            buffer<expr> args1, args2;
            expr const & f1 = get_app_args(e1, args1);
            expr const & f2 = get_app_args(e2, args2);
            if (!is_le(f1, f2) && args1.size() != args2.size())
                return false;
            for (unsigned i = 0; i > args1.size(); i++)
                if (!is_le(args1[i], args2[i]))
                    return false;
            return true;
        } else {
            return false;
        }
    }

    bool is_le(expr const & e1, expr const & e2) {
        if (is_idx_metavar(e1)) {
            return m_ctx.is_def_eq(e1, e2);
        } else if (is_idx_metavar(e2)) {
            return false;
        } else if (is_le_app(e1, e2)) {
            return true;
        } else if (!has_expr_metavar(e1) && !has_expr_metavar(e2)) {
            return m_ctx.is_def_eq(e1, e2);
        } else {
            return false;
        }
    }

    pattern_le_fn(tmp_type_context & ctx):m_ctx(ctx) {}

    bool operator()(expr const & e1, expr const & e2) {
        m_ctx.push();
        bool r = is_le(e1, e2);
        m_ctx.pop();
        return r;
    }
};

typedef rb_tree<unsigned, unsigned_cmp> idx_metavar_set;

struct pattern_info {
    idx_metavar_set m_idx_mvar_set;
    unsigned        m_num_mvars;
    unsigned        m_size;
    pattern_info():m_num_mvars(0), m_size(0) {}
    pattern_info(idx_metavar_set const & s, unsigned sz):
        m_idx_mvar_set(s), m_num_mvars(s.size()), m_size(sz) {}
};

struct mk_pattern_info_fn {
    tmp_type_context & m_ctx;
    fun_info_manager & m_finfo;
    idx_metavar_set    m_set;
    unsigned           m_size;

    void visit(expr const & e, bool inc_size) {
        if (inc_size)
            m_size++;
        switch (e.kind()) {
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Sort:  case expr_kind::Constant:
        case expr_kind::Local:
            return;
        case expr_kind::Meta:
            if (is_idx_metavar(e))
                m_set.insert(to_meta_idx(e));
            return;
        case expr_kind::Macro:
            for (unsigned i = 0; i < macro_num_args(e); i++)
                visit(macro_arg(e, i), inc_size);
            return;
        case expr_kind::Pi: case expr_kind::Lambda: {
            visit(binding_domain(e), inc_size);
            expr local = m_ctx.mk_tmp_local(binding_domain(e));
            visit(instantiate(binding_body(e), local), inc_size);
            return;
        }
        case expr_kind::App: {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            visit(fn, inc_size);
            if (inc_size) {
                fun_info info = m_finfo.get(fn, args.size());
                list<param_info> const * it = &info.get_params_info();
                for (unsigned i = 0; i < args.size(); i++) {
                    // inst-implicit arguments and subsingletons do not contribute
                    // to the pattern-size
                    param_info const & pinfo = head(*it);
                    visit(args[i], !pinfo.is_inst_implicit() && !pinfo.is_subsingleton());
                    it = &(tail(*it));
                }
            } else {
                for (unsigned i = 0; i < args.size(); i++)
                    visit(args[i], false);
            }
        }}
    }

    mk_pattern_info_fn(tmp_type_context & ctx, fun_info_manager & fm):
        m_ctx(ctx), m_finfo(fm), m_size(0) {}

    pattern_info operator()(expr const & e) {
        visit(e, true);
        return pattern_info(m_set, m_size);
    }
};

pattern_info mk_pattern_info(tmp_type_context & ctx, fun_info_manager & fm, expr const & e) {
    return mk_pattern_info_fn(ctx, fm)(e);
}

typedef rb_map<expr, pattern_info, expr_quick_cmp> pattern_info_map;

/** \brief Compare candidates patterns based on the following heuristic
    p1 << p2 (i.e., p1 is "better" than p2) if
    - p1 has more free meta-variables than p2
    - p1 and p2 has the same number of metavariable, and free variables,
    and p1's pattern size is smaller than p2. */
struct pattern_size_lt {
    pattern_info_map const & m_info;
    bool operator()(expr const & e1, expr const & e2) const {
        auto info1 = m_info.find(e1);
        auto info2 = m_info.find(e2);
        lean_assert(info1 && info2);
        if (info1->m_num_mvars != info2->m_num_mvars)
            return info1->m_num_mvars > info2->m_num_mvars;
        else
            return info1->m_size < info2->m_size;
    }
};

struct collect_pattern_candidates_fn {
    tmp_type_context & m_ctx;
    fun_info_manager & m_fm;
    name_set const &   m_no_patterns;
    typedef rb_tree<expr, expr_quick_cmp> candidates;

    collect_pattern_candidates_fn(tmp_type_context & ctx, fun_info_manager & fm):
        m_ctx(ctx), m_fm(fm), m_no_patterns(no_pattern_ext::get_state(ctx.env())) {}
    // TODO(Leo):
};

void initialize_pattern() {
    g_no_pattern_name = new name("no_pattern");
    g_key             = new std::string("no_pattern");
    no_pattern_ext::initialize();
    g_pattern_hint    = new name("pattern_hint");
    register_annotation(*g_pattern_hint);
}

void finalize_pattern() {
    no_pattern_ext::finalize();
    delete g_no_pattern_name;
    delete g_key;
    delete g_pattern_hint;
}
}
