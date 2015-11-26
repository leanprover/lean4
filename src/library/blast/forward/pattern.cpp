/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "library/expr_lt.h"
#include "kernel/find_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/kernel_serializer.h"
#include "library/tmp_type_context.h"
#include "library/annotation.h"
#include "library/occurs.h"
#include "library/scoped_ext.h"
#include "library/idx_metavar.h"
#include "library/blast/options.h"
#include "library/blast/forward/pattern.h"

#ifndef LEAN_DEFAULT_PATTERN_MAX_STEPS
#define LEAN_DEFAULT_PATTERN_MAX_STEPS 1024
#endif

namespace lean {
static name * g_pattern_max_steps  = nullptr;

unsigned get_pattern_max_steps(options const & o) {
    return o.get_unsigned(*g_pattern_max_steps, LEAN_DEFAULT_PATTERN_MAX_STEPS);
}

/*
Step 1: Selecting which variables we should track.

Given (H : Pi (a_1 : A_1) ... (a_n : A_n), B) where B is not a Pi,
we use the following procedure to decide which a_i's must be in
patterns used by heuristic instantiation.

- We say an a_i that must occur in a pattern is "trackable".

- The set of "trackable" a_i's is the least fix point of
  a) If there is j > i, a_j is trackable, type(a_j) depends on a_i,
     and type(a_i) is not higher-order, then
     a_i is NOT trackable.
     Reason: we can infer a_i from a_j using type inference.

  b) a_i is a proposition -> a_i is NOT trackable.
     Reason: we can leave a_i as hypothesis whenever we instantiate H.

  c) a_i is instance implicit -> a_i is NOT trackable.
     We should use type class resolution to infer a_i.

Remark: we say a (multi-)pattern for H is valid iff it contains all
trackable a_i's.

We define the set of "residue" hypotheses a_i as the least fix point of
  a) a_i is a proposition
  b) a_i is not inst_implicit
  c) a_i is not trackable
  d) there is no j > i s.t. a_j is not residue
     and type(a_j) depends on a_i, and type(a_i) is not higher-order

That is, if a_i is a "residue" hypothesis, we cannot infer it
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

The option pattern.max_steps is a threshold on the number of steps performed
Lean will generate an error if more than pattern.max_steps are performed while processing the set S.

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
trackable(c_1) == trackable(c_2) and weight(c_1) > weight(c_2).

We say a subset M of C is a multi-pattern if M contains all trackable variables.
We say a multi-pattern M is minimal if no strict subset of M is a multi-pattern.

If the set of minimal multi-patterns for C is bigger than `pattern.max`, then we generate an error.
That is, the user should provide pattern-hints.
*/
static name * g_pattern_hint = nullptr;

bool is_pattern_hint(expr const & e) { return is_annotation(e, *g_pattern_hint); }
expr const & get_pattern_hint_arg(expr const & e) { lean_assert(is_pattern_hint(e)); return get_annotation_arg(e); }
bool has_pattern_hints(expr const & e) {
    return static_cast<bool>(find(e, [](expr const & e, unsigned) { return is_pattern_hint(e); }));
}
expr mk_pattern_hint(expr const & e) {
    if (has_pattern_hints(e))
        throw exception("invalid pattern hint, nested patterns hints are not allowed");
    return mk_annotation(*g_pattern_hint, e);
}

static name * g_hi_name    = nullptr;
static std::string * g_key = nullptr;

// "Poor man" union type
struct hi_entry {
    optional<name> m_no_pattern;
    hi_lemma       m_lemma;
    hi_entry() {}
    hi_entry(name const & n):m_no_pattern(n) {}
    hi_entry(hi_lemma const & l):m_lemma(l) {}
};

struct hi_state {
    name_set           m_no_patterns;
    name_map<hi_lemma> m_name_to_lemma;
    hi_lemmas          m_lemmas;
};

serializer & operator<<(serializer & s, multi_pattern const & mp) {
    write_list(s, mp);
    return s;
}

deserializer & operator>>(deserializer & d, multi_pattern & mp) {
    mp = read_list<expr>(d);
    return d;
}

static optional<name> get_hi_lemma_name(expr const & H) {
    if (is_lambda(H))
        return get_hi_lemma_name(binding_body(H));
    expr const & f = get_app_fn(H);
    if (is_constant(f))
        return optional<name>(const_name(f));
    else
        return optional<name>();
}

struct hi_config {
    typedef hi_entry entry;
    typedef hi_state state;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        if (e.m_no_pattern) {
            s.m_no_patterns.insert(*e.m_no_pattern);
        } else {
            if (auto n = get_hi_lemma_name(e.m_lemma.m_proof))
                s.m_name_to_lemma.insert(*n, e.m_lemma);
            for (multi_pattern const & mp : e.m_lemma.m_multi_patterns) {
                for (expr const & p : mp) {
                    lean_assert(is_app(p));
                    lean_assert(is_constant(get_app_fn(p)));
                    s.m_lemmas.insert(const_name(get_app_fn(p)), e.m_lemma);
                }
            }
        }
    }

    static name const & get_class_name() {
        return *g_hi_name;
    }

    static std::string const & get_serialization_key() {
        return *g_key;
    }

    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_no_pattern;
        if (!e.m_no_pattern) {
            hi_lemma const & l = e.m_lemma;
            s << l.m_num_uvars << l.m_num_mvars << l.m_priority << l.m_prop << l.m_proof;
            write_list(s, l.m_multi_patterns);
        }
    }

    static entry read_entry(deserializer & d) {
        entry e;
        d >> e.m_no_pattern;
        if (!e.m_no_pattern) {
            hi_lemma & l = e.m_lemma;
            d >> l.m_num_uvars >> l.m_num_mvars >> l.m_priority >> l.m_prop >> l.m_proof;
            l.m_multi_patterns = read_list<multi_pattern>(d);
        }
        return e;
    }

    static optional<unsigned> get_fingerprint(entry const & e) {
        return e.m_no_pattern ? some(e.m_no_pattern->hash()) : some(e.m_lemma.m_prop.hash());
    }
};

template class scoped_ext<hi_config>;
typedef scoped_ext<hi_config> hi_ext;

bool is_no_pattern(environment const & env, name const & n) {
    return hi_ext::get_state(env).m_no_patterns.contains(n);
}

environment add_no_pattern(environment const & env, name const & n, bool persistent) {
    return hi_ext::add_entry(env, get_dummy_ios(), hi_entry(n), persistent);
}

name_set const & get_no_patterns(environment const & env) {
    return hi_ext::get_state(env).m_no_patterns;
}

typedef rb_tree<unsigned, unsigned_cmp> idx_metavar_set;

static bool is_higher_order(tmp_type_context & ctx, expr const & e) {
    return is_pi(ctx.relaxed_whnf(ctx.infer(e)));
}

/** \brief Given type of the form (Pi (a_1 : A_1) ... (a_n : A_n), B) (or reducible to something of this form),
    create n idx_metavars (one for each a_i), store the meta-variables in mvars,
    and store in trackable and residue the subsets of these meta-variables as
    described in the beginning of this file. Then returns B (instantiated with the new meta-variables) */
expr extract_trackable(tmp_type_context & ctx, expr const & type,
                       buffer<expr> & mvars, idx_metavar_set & trackable, idx_metavar_set & residue) {
    // 1. Create mvars and initialize trackable and residue sets
    expr it = type;
    while (true) {
        if (!is_pi(it)) {
            expr new_it = ctx.relaxed_whnf(it);
            if (!is_pi(new_it))
                break; // consumed all arguments
            it = new_it;
        }
        lean_assert(is_pi(it));
        expr new_mvar = ctx.mk_mvar(binding_domain(it));
        lean_assert(is_idx_metavar(new_mvar));
        mvars.push_back(new_mvar);
        bool is_inst_implicit = binding_info(it).is_inst_implicit();
        bool is_prop          = ctx.is_prop(binding_domain(it));
        if (!is_inst_implicit) {
            unsigned midx = to_meta_idx(new_mvar);
            if (is_prop)
                residue.insert(midx);
            else
                trackable.insert(midx);
        }
        it = instantiate(binding_body(it), new_mvar);
    }
    expr     B = it;
    unsigned n = mvars.size();
    // 2. Compute trackable fixpoint
    bool modified;
    do {
        modified = false;
        for (unsigned i = 0; i < n; i++) {
            unsigned midx = to_meta_idx(mvars[i]);
            if (!trackable.contains(midx))
                continue; // variable is not in the trackable set
            // There is no j > i, mvars[j] is trackable, type(mvars[j]) depends on mvars[i],
            // and type(mvars[i]) is not higher-order.
            if (is_higher_order(ctx, mvars[i]))
                continue;
            unsigned j = i+1;
            for (; j < n; j++) {
                if (trackable.contains(to_meta_idx(mvars[j])) &&
                    occurs(mvars[i], ctx.infer(mvars[j]))) {
                    // we can infer mvars[i] using type inference
                    break;
                }
            }
            if (j == n)
                continue;
            trackable.erase(midx);
            modified = true;
        }
    } while (modified);
    // 3. Compute residue fixpoint
    do {
        modified = false;
        for (unsigned i = 0; i < n; i++) {
            unsigned midx = to_meta_idx(mvars[i]);
            if (!residue.contains(midx))
                continue; // variable is not in the residue set
            // There is no j > i s.t. mvars[j] is not residue
            // and type(mvars[j]) depends on mvars[i], and type(mvars[i]) is not higher-order
            if (is_higher_order(ctx, mvars[i]))
                continue;
            unsigned j = i+1;
            for (; j < n; j++) {
                if (!residue.contains(to_meta_idx(mvars[j])) &&
                    occurs(mvars[i], ctx.infer(mvars[j]))) {
                    // we can infer mvars[i] using type inference
                    break;
                }
            }
            if (j == n)
                continue;
            residue.erase(midx);
            modified = true;
        }
    } while (modified);
    return B;
}

struct mk_hi_lemma_fn {
    tmp_type_context & m_ctx;
    name_set const &   m_no_patterns;
    expr               m_H;
    unsigned           m_num_uvars;
    unsigned           m_priority;
    unsigned           m_max_steps;

    buffer<expr>       m_mvars;
    idx_metavar_set    m_trackable;
    idx_metavar_set    m_residue;
    unsigned           m_num_steps;

    mk_hi_lemma_fn(tmp_type_context & ctx, expr const & H,
                   unsigned num_uvars, unsigned prio, unsigned max_steps):
        m_ctx(ctx), m_no_patterns(hi_ext::get_state(ctx.env()).m_no_patterns),
        m_H(H), m_num_uvars(num_uvars), m_priority(prio), m_max_steps(max_steps) {}

    struct candidate {
        expr            m_expr;
        idx_metavar_set m_mvars;
        candidate() {}
        candidate(expr const & e):
            m_expr(e) {
            for_each(e, [&](expr const & e, unsigned) {
                    if (is_idx_metavar(e))
                        m_mvars.insert(to_meta_idx(e));
                    return true;
                });
        }
        candidate(expr const & e, idx_metavar_set const & mvars):m_expr(e), m_mvars(mvars) {}
    };

    struct candidate_lt {
        int operator()(candidate const & c1, candidate const & c2) const { return expr_quick_cmp()(c1.m_expr, c2.m_expr); }
    };

    typedef rb_tree<candidate, candidate_lt> candidate_set;

    void collect_pattern_hints(expr const & e, candidate_set & s) {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_pattern_hint(e)) {
                    s.insert(candidate(get_pattern_hint_arg(e)));
                    return false;
                }
                return true;
            });
    }

    candidate_set collect_pattern_hints(buffer<expr> const & mvars, expr const & B) {
        candidate_set s;
        for (expr const & mvar : mvars)
            collect_pattern_hints(m_ctx.infer(mvar), s);
        collect_pattern_hints(B, s);
        return s;
    }

    candidate_set m_candidates;

    void save_candidates(candidate_set const & s) {
        m_candidates.merge(s);
    }

    candidate_set collect_core(expr const & a) {
        switch (a.kind()) {
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Sort:   case expr_kind::Constant:
        case expr_kind::Meta:   case expr_kind::Local:
        case expr_kind::Lambda: case expr_kind::Pi:
            return candidate_set();
        case expr_kind::Macro:
            for (unsigned i = 0; i < macro_num_args(a); i++) {
                candidate_set s = collect_core(macro_arg(a, i));
                save_candidates(s);
            }
            return candidate_set();
        case expr_kind::App: {
            buffer<expr> args;
            expr const & fn = get_app_args(a, args);
            buffer<candidate_set> arg_candidates;
            bool forbidden = !is_local(fn) && (!is_constant(fn) || m_no_patterns.contains(const_name(fn)));
            if (forbidden) {
                for (expr const & arg : args) {
                    candidate_set s = collect_core(arg);
                    save_candidates(s);
                }
                return candidate_set();
            } else {
                candidate_set ss;
                idx_metavar_set mvars;
                for (expr const & arg : args) {
                    if (is_idx_metavar(arg)) {
                        if (m_trackable.contains(to_meta_idx(arg))) {
                            mvars.insert(to_meta_idx(arg));
                        }
                    } else {
                        candidate_set s = collect_core(arg);
                        s.for_each([&](candidate const & c) {
                                ss.insert(c);
                                mvars.merge(c.m_mvars);
                            });
                    }
                }
                if (ss.find_if([&](candidate const & c) { return mvars == c.m_mvars; })) {
                    return ss;
                } else if (!mvars.empty()) {
                    // a subsumes all children candidates
                    return candidate_set(candidate(a, mvars));
                }
            }
        }}
        lean_unreachable();
    }

    candidate_set collect(expr const & a) {
        m_candidates = candidate_set();
        save_candidates(collect_core(a));
        return m_candidates;
    }

    void mk_multi_patterns_core(unsigned i, buffer<candidate> const & s, buffer<expr> & mp, idx_metavar_set const & mvars, buffer<multi_pattern> & mps) {
        m_num_steps++;
        if (m_num_steps > m_max_steps)
            throw exception(sstream() << "pattern inference failed for [forward] annotation, the maximum number (" << m_max_steps << ") of steps has been reached "
                            "(possible solutions: provide pattern hints using the notation '(: t :)' for marking subterms; increase threshold using option pattern.max_steps)");
        if (i == s.size())
            return;
        candidate const & c = s[i];
        if (!mvars.is_strict_superset(c.m_mvars)) {
            // candidate s[i] contributes with new variables
            unsigned sz = mp.size();
            mp.push_back(c.m_expr);
            idx_metavar_set new_mvars = mvars;
            new_mvars.merge(c.m_mvars);
            if (new_mvars.is_superset(m_trackable)) {
                // found multi-pattern
                mps.push_back(to_list(mp));
            } else {
                // include s[i]
                mk_multi_patterns_core(i+1, s, mp, new_mvars, mps);
            }
            mp.shrink(sz);
        }
        // do not include s[i];
        mk_multi_patterns_core(i+1, s, mp, mvars, mps);
    }

    // If heuristic is true, then
    //   1. Give preference to unary patterns
    //   2. If there are no unary patterns, then
    //      delet any candidate c_1 if there is a c_2 s.t.
    //      trackable(c_1) == trackable(c_2) and weight(c_1) > weight(c_2).
    list<multi_pattern> mk_multi_patterns_using(candidate_set s, bool heuristic) {
        if (heuristic) {
            buffer<multi_pattern> unit_patterns;
            s.for_each([&](candidate const & c) {
                    if (c.m_mvars.is_superset(m_trackable))
                        unit_patterns.push_back(c.m_expr);
                });
            if (!unit_patterns.empty()) {
                return to_list(unit_patterns);
            }
            buffer<candidate> to_delete;
            s.for_each([&](candidate const & c1) {
                    if (s.find_if([&](candidate const & c2) {
                                return
                                    c1.m_mvars == c2.m_mvars &&
                                    get_weight(c1.m_expr) > get_weight(c2.m_expr);
                            })) {
                        to_delete.push_back(c1);
                    }
                });
            for (candidate const & c : to_delete) {
                s.erase(c);
            }
        }
        buffer<candidate> s_buffer;
        s.to_buffer(s_buffer);
        buffer<multi_pattern> mps;
        buffer<expr> mp;
        m_num_steps = 0;
        mk_multi_patterns_core(0, s_buffer, mp, idx_metavar_set(), mps);
        return to_list(mps);
    }

    expr replace_mvars(expr const & e, buffer<expr> const & subst) {
        return replace(e,
                       [&](expr const & e) {
                           if (!has_expr_metavar(e))
                               return some_expr(e);
                           if (is_idx_metavar(e))
                               return some_expr(subst[to_meta_idx(e)]);
                           else
                               return none_expr();
                       });
    }

    // Create proof by pushing all residue hypotheses to the "end".
    // Residue hypotheses are converted into local constants.
    // Remaining metavariables are "renamed" (i.e., renumbered to avoid gaps due to residue hypotheses moved to the end).
    // Trackable set is updated.
    // subst will contain the mvars renaming
    expr mk_proof(buffer<expr> & new_residue, buffer<expr> & subst) {
        unsigned j = 0;
        bool found_residue     = false;
        bool only_tail_residue = true;
        for (unsigned i = 0; i < m_mvars.size(); i++) {
            expr new_type = m_ctx.infer(m_mvars[i]);
            if (i != j)
                new_type = replace_mvars(new_type, subst);
            if (m_residue.contains(to_meta_idx(m_mvars[i]))) {
                found_residue = true;
                expr res      = m_ctx.mk_tmp_local(new_type);
                new_residue.push_back(res);
                subst.push_back(res);
            } else {
                if (found_residue)
                    only_tail_residue = false;
                expr new_mvar;
                if (j == i) {
                    new_mvar = m_mvars[i];
                } else {
                    new_mvar = mk_idx_metavar(j, new_type);
                    if (m_trackable.contains(i)) {
                        m_trackable.erase(i);
                        m_trackable.insert(j);
                    }
                    m_mvars[j] = new_mvar;
                }
                j++;
                subst.push_back(new_mvar);
            }
        }
        m_mvars.shrink(j);
        if (only_tail_residue) {
            return mk_app(m_H, m_mvars);
        } else {
            return Fun(new_residue, mk_app(m_H, subst));
        }
    }

    hi_lemma operator()() {
        expr H_type = m_ctx.infer(m_H);
        expr B      = extract_trackable(m_ctx, H_type, m_mvars, m_trackable, m_residue);
        buffer<expr> subst;
        buffer<expr> residue_locals;
        expr proof  = mk_proof(residue_locals, subst);
        B           = replace_mvars(B, subst);
        candidate_set hints = collect_pattern_hints(m_mvars, B);
        list<multi_pattern> mps;
        if (!hints.empty()) {
            mps = mk_multi_patterns_using(hints, false);
        } else {
            buffer<expr> places;
            candidate_set B_candidates = collect(B);
            if (auto r1 = mk_multi_patterns_using(B_candidates, true)) {
                mps = r1;
            } else {
                candidate_set residue_candidates;
                for (expr const & r : residue_locals) {
                    residue_candidates.merge(collect(m_ctx.infer(r)));
                }
                if (auto r2 = mk_multi_patterns_using(residue_candidates, true)) {
                    mps = r2;
                } else if (!residue_candidates.empty() && !B_candidates.empty()) {
                    candidate_set all_candidates = B_candidates;
                    all_candidates.merge(residue_candidates);
                    mps = mk_multi_patterns_using(all_candidates, true);
                }
            }
        }
        if (!mps) {
            throw exception(sstream() << "pattern inference failed for [forward] annotation, "
                            "(solution: provide pattern hints using the notation '(: t :)' )");
        }
        hi_lemma r;
        r.m_num_uvars      = m_num_uvars;
        r.m_num_mvars      = m_mvars.size();
        r.m_priority       = m_priority;
        r.m_multi_patterns = mps;
        r.m_prop           = m_ctx.infer(proof);
        r.m_proof          = proof;
        return r;
    }
};

hi_lemma mk_hi_lemma_core(tmp_type_context & ctx, expr const & H, unsigned num_uvars,
                          unsigned priority, unsigned max_steps) {
    return mk_hi_lemma_fn(ctx, H, num_uvars, priority, max_steps)();
}

namespace blast {
hi_lemma mk_hi_lemma(tmp_type_context & ctx, expr const & H) {
    unsigned max_steps = get_config().m_pattern_max_steps;
    ctx.clear();
    return mk_hi_lemma_core(ctx, H, 0, LEAN_HI_LEMMA_DEFAULT_PRIORITY, max_steps);
}}

environment add_hi_lemma(environment const & env, options const & o, name const & c, unsigned priority, bool persistent) {
    tmp_type_context ctx(env, get_dummy_ios());
    declaration const & d = env.get(c);
    buffer<level> us;
    unsigned num_us = d.get_num_univ_params();
    for (unsigned i = 0; i < num_us; i++)
        us.push_back(ctx.mk_uvar());
    expr H             = mk_constant(c, to_list(us));
    unsigned max_steps = get_pattern_max_steps(o);
    return hi_ext::add_entry(env, get_dummy_ios(), hi_entry(mk_hi_lemma_core(ctx, H, num_us, priority, max_steps)),
                             persistent);
}

hi_lemma const * get_hi_lemma(environment const & env, name const & c) {
    return hi_ext::get_state(env).m_name_to_lemma.find(c);
}

void initialize_pattern() {
    g_hi_name           = new name("hi");
    g_key               = new std::string("HI");
    hi_ext::initialize();
    g_pattern_hint      = new name("pattern_hint");
    register_annotation(*g_pattern_hint);
    g_pattern_max_steps = new name{"pattern", "max_steps"};
    register_unsigned_option(*g_pattern_max_steps, LEAN_DEFAULT_PATTERN_MAX_STEPS,
                             "(pattern) max number of steps performed by pattern inference procedure, "
                             "we have this threshold because in the worst case this procedure may take "
                             "an exponetial number of steps");
}

void finalize_pattern() {
    hi_ext::finalize();
    delete g_hi_name;
    delete g_key;
    delete g_pattern_hint;
    delete g_pattern_max_steps;
}
}
