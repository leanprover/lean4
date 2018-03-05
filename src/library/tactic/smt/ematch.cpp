/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/interrupt.h"
#include "util/small_object_allocator.h"
#include "library/trace.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/fun_info.h"
#include "library/idx_metavar.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_nat.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/smt/ematch.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/congruence_tactics.h"
#include "library/tactic/smt/hinst_lemmas.h"

namespace lean {
void ematch_state::internalize(type_context_old & ctx, expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:      case expr_kind::Sort:
    case expr_kind::Constant: case expr_kind::Meta:
    case expr_kind::Local:    case expr_kind::Lambda:
    case expr_kind::Let:
        break;
    case expr_kind::Pi:
        if (is_arrow(e) && ctx.is_prop(e)) {
            internalize(ctx, binding_domain(e));
            internalize(ctx, binding_body(e));
        }
        break;
    case expr_kind::Macro:
        for (unsigned i = 0; i < macro_num_args(e); i++)
            internalize(ctx, macro_arg(e, i));
        break;
    case expr_kind::App: {
        buffer<expr> args;
        expr const & f = get_app_args(e, args);
        if ((is_constant(f) && !has_no_inst_pattern_attribute(ctx.env(), const_name(f))) ||
            (is_local(f))) {
            rb_expr_set s;
            if (auto old_s = m_app_map.find(head_index(f)))
                s = *old_s;
            s.insert(e);
            m_app_map.insert(head_index(f), s);
        }
        for (expr const & arg : args) {
            internalize(ctx, arg);
        }
        break;
    }}
}

bool ematch_state::save_instance(expr const & i) {
    if (m_num_instances >= m_config.m_max_instances) {
        if (!m_max_instances_exceeded) {
            lean_trace(name({"smt", "ematch"}),
                       tout() << "maximum number of ematching instances (" << m_config.m_max_instances << ") has been reached\n";);
        }
        m_max_instances_exceeded = true;
        return false;
    }
    if (m_instances.contains(i)) {
        return false;
    } else {
        m_num_instances++;
        m_instances.insert(i);
        return true;
    }
}

bool ematch_state::save_instance(expr const & lemma, buffer<expr> const & args) {
    expr key = mk_app(lemma, args);
    return save_instance(key);
}

/*
structure ematch_config :=
(max_instances  : nat)
(max_generation : nat)
*/
vm_obj ematch_state::mk_vm_ematch_config() const {
    return mk_vm_constructor(0, mk_vm_nat(get_config().m_max_instances), mk_vm_nat(get_config().m_max_generation));
}

/* CACHE_RESET: NO */
/* Allocator for ematching constraints. */
MK_THREAD_LOCAL_GET(small_object_allocator, get_emc_allocator, "ematch constraint");

enum class ematch_cnstr_kind { DefEqOnly, EqvOnly, Match, MatchAC, MatchSS /* match subsingleton */, Continue };
class ematch_cnstr;
/** \brief Base class for Ematching constraints.

    Remark: these objects are thread local. So, we don't need synchronization. */
struct ematch_cnstr_cell {
    unsigned          m_rc;
    ematch_cnstr_kind m_kind;

    void inc_ref() { m_rc++; }
    bool dec_ref_core() { lean_assert(m_rc > 0); m_rc--; return m_rc == 0; }
    void dec_ref() { if (dec_ref_core()) { dealloc(); } }
    void dealloc();
    ematch_cnstr_cell(ematch_cnstr_kind k):m_rc(0), m_kind(k) {}
    ematch_cnstr_kind kind() const { return m_kind; }
    unsigned get_rc() const { return m_rc; }
};

/* Ematching constraint smart pointer */
class ematch_cnstr {
    friend struct ematch_cnstr_cell;
    ematch_cnstr_cell * m_data;
public:
    ematch_cnstr():m_data(nullptr) {}
    explicit ematch_cnstr(ematch_cnstr_cell * c):m_data(c) { m_data->inc_ref(); }
    ematch_cnstr(ematch_cnstr const & o):m_data(o.m_data) { m_data->inc_ref(); }
    ematch_cnstr(ematch_cnstr && o):m_data(o.m_data) { o.m_data = nullptr; }
    ~ematch_cnstr() { if (m_data) m_data->dec_ref(); }
    operator ematch_cnstr_cell*() const { return m_data; }

    ematch_cnstr & operator=(ematch_cnstr const & s) {
        if (s.m_data) s.m_data->inc_ref();
        ematch_cnstr_cell * new_data = s.m_data;
        if (m_data) m_data->dec_ref();
        m_data = new_data;
        return *this;
    }

    ematch_cnstr & operator=(ematch_cnstr && s) {
        if (m_data) m_data->dec_ref();
        m_data   = s.m_data;
        s.m_data = nullptr;
        return *this;
    }

    ematch_cnstr_kind kind() const { return m_data->kind(); }
    ematch_cnstr_cell * raw() const { return m_data; }
};

struct ematch_eq_cnstr : public ematch_cnstr_cell {
    expr m_p;
    expr m_t;
    ematch_eq_cnstr(ematch_cnstr_kind k, expr const & p, expr const & t):
        ematch_cnstr_cell(k), m_p(p), m_t(t) {}
};

struct ematch_ac_cnstr : public ematch_cnstr_cell {
    expr       m_op;
    list<expr> m_p;
    list<expr> m_t;
    ematch_ac_cnstr(expr const & op, list<expr> const & p, list<expr> const & t):
        ematch_cnstr_cell(ematch_cnstr_kind::MatchAC), m_op(op), m_p(p), m_t(t) {}
};

struct ematch_continue : public ematch_cnstr_cell {
    expr m_p;
    ematch_continue(expr const & p):
        ematch_cnstr_cell(ematch_cnstr_kind::Continue), m_p(p) {}
};

inline bool is_eq_cnstr(ematch_cnstr_cell const * c) {
    return
        c->kind() == ematch_cnstr_kind::Match || c->kind() == ematch_cnstr_kind::MatchSS ||
        c->kind() == ematch_cnstr_kind::DefEqOnly || c->kind() == ematch_cnstr_kind::EqvOnly;
}
static bool is_ac_cnstr(ematch_cnstr_cell const * c) { return c->kind() == ematch_cnstr_kind::MatchAC; }
static bool is_continue(ematch_cnstr_cell const * c) { return c->kind() == ematch_cnstr_kind::Continue; }

static ematch_eq_cnstr * to_eq_cnstr(ematch_cnstr_cell * c) { lean_assert(is_eq_cnstr(c)); return static_cast<ematch_eq_cnstr*>(c); }
static ematch_ac_cnstr * to_ac_cnstr(ematch_cnstr_cell * c) { lean_assert(is_ac_cnstr(c)); return static_cast<ematch_ac_cnstr*>(c); }
static ematch_continue * to_continue(ematch_cnstr_cell * c) { lean_assert(is_continue(c)); return static_cast<ematch_continue*>(c); }

void ematch_cnstr_cell::dealloc() {
    lean_assert(get_rc() == 0);
    if (is_ac_cnstr(this)) {
        to_ac_cnstr(this)->~ematch_ac_cnstr();
        get_emc_allocator().deallocate(sizeof(ematch_ac_cnstr), this);
    } else if (is_continue(this)) {
        to_continue(this)->~ematch_continue();
        get_emc_allocator().deallocate(sizeof(ematch_continue), this);
    } else {
        to_eq_cnstr(this)->~ematch_eq_cnstr();
        get_emc_allocator().deallocate(sizeof(ematch_eq_cnstr), this);
    }
}

static ematch_cnstr mk_eq_cnstr(ematch_cnstr_kind k, expr const & p, expr const & t) {
    return ematch_cnstr(new (get_emc_allocator().allocate(sizeof(ematch_eq_cnstr))) ematch_eq_cnstr(k, p, t));
}

static ematch_cnstr mk_match_ac_cnstr(expr const & op, list<expr> const & p, list<expr> const & t) {
    return ematch_cnstr(new (get_emc_allocator().allocate(sizeof(ematch_ac_cnstr))) ematch_ac_cnstr(op, p, t));
}

static ematch_cnstr mk_continue(expr const & p) {
    return ematch_cnstr(new (get_emc_allocator().allocate(sizeof(ematch_continue))) ematch_continue(p));
}

static ematch_cnstr mk_match_eq_cnstr(expr const & p, expr const & t) { return mk_eq_cnstr(ematch_cnstr_kind::Match, p, t); }
static ematch_cnstr mk_match_ss_cnstr(expr const & p, expr const & t) { return mk_eq_cnstr(ematch_cnstr_kind::MatchSS, p, t); }
static ematch_cnstr mk_eqv_cnstr(expr const & p, expr const & t) { return mk_eq_cnstr(ematch_cnstr_kind::EqvOnly, p, t); }
static ematch_cnstr mk_defeq_cnstr(expr const & p, expr const & t) { return mk_eq_cnstr(ematch_cnstr_kind::DefEqOnly, p, t); }

static expr const & cnstr_p(ematch_cnstr const & c) { return to_eq_cnstr(c)->m_p; }
static expr const & cnstr_t(ematch_cnstr const & c) { return to_eq_cnstr(c)->m_t; }
static expr const & cont_p(ematch_cnstr const & c) { return to_continue(c)->m_p; }
static expr const & ac_op(ematch_cnstr const & c) { return to_ac_cnstr(c)->m_op; }
static list<expr> const & ac_p(ematch_cnstr const & c) { return to_ac_cnstr(c)->m_p; }
static list<expr> const & ac_t(ematch_cnstr const & c) { return to_ac_cnstr(c)->m_t; }

/*
  Matching modulo equalities.

  This module also supports matching modulo AC.

  The procedure is (supposed to be) complete for E-matching and AC-matching.
  However, it is currently incomplete for AC-E-matching.

  Here are matching problems that are not supported.
  Assuming + is an AC operation.

  1) Given { a + b = f c }, solve (?x + f ?x) =?= (a + c + b)
  It misses the solution ?x := c

  2) Given { a = a + a }, solve (?x + ?x + ?x + ?y) =?= (a + b)
  It misses the solution ?x := a, ?y := b

  The following implementation is based on standard algorithms for E-matching and
  AC-matching. The following extensions are supported.

  - E-matching modulo heterogeneous equalities.
    Casts are automatically introduced.
    Moreover, in standard E-matching, a sub-problem such as
          ?x =?= t
    where ?x is unassigned, is solved by assigning ?x := t.
    We add the following extension when t is in a heterogeneous equivalence class.
    We peek a term t_i in eqc(t) for each different type, and then create
    the subproblems:
          ?x := t_1 \/ ... \/ ?x := t_k

  - Uses higher-order pattern matching whenever higher-order sub-patterns
    are found. Example: (?f a) =?= (g a a)

  - Subsingleton support. For example, suppose (a b : A), and A is a subsingleton.
    Then, the following pattern is solved.
        (f a ?x) =?= (f b c)
    This is useful when we have proofs embedded in terms.

  - Equality expansion preprocessing step for AC-matching subproblems.
    Given an AC-matching subproblem  p =?= ...+t+...
    For each term t' headed by + in eqc(t), we generate a new case:
          p =?= ...+t'+...

    Limitations:
    1- A term t will be expanded at most once per AC subproblem.
       Example: given {a = a + a}, and constraint (?x + ?x + ?x + ?y) =?= (a + b).
       We produce two cases:
                ?x + ?x + ?x + ?y =?= a + b
                \/
                ?x + ?x + ?x + ?y =?= a + a + b

    2- We do not consider subterms of the form (t+s).
       Example: give {a + b = f c}, and constraint {?x + f ?x =?= a + c + b},
       this procedure will not generate the new case {?x + f ?x =?= f c + c}
       by replacing (a + b) with (f c).
*/
class ematch_fn {
    typedef list<ematch_cnstr> state;
    type_context_old &                m_ctx;
    ematch_state &                m_em_state;
    congruence_closure &          m_cc;
    buffer<new_instance> &        m_new_instances;
    unsigned                      m_gen;

    state                         m_state;
    buffer<pair<state, unsigned>> m_choice_stack;

    expr instantiate_mvars(expr const & e) {
        return m_ctx.instantiate_mvars(e);
    }

    /* Similar to instantiate_mvars, but it makes sure the assignment at m_ctx is not modified by composition.
       That is, suppose we have the assignment { ?x := f ?y, ?y := a }, and we instantiate (g ?x).
       The result is (g (f a)), but this method prevents the assignment to be modified to
              { ?x := f a, ?y := a }

       We need this feature for AC matching, where we want to be able to quickly detect "partially solved"
       variables of the form (?x := ?y + s) where s does not contain metavariables. */
    expr safe_instantiate_mvars(expr const & e) {
        m_ctx.push_scope();
        expr r = instantiate_mvars(e);
        m_ctx.pop_scope();
        return r;
    }

    bool is_metavar(expr const & e) { return m_ctx.is_tmp_mvar(e); }
    bool is_meta(expr const & e) { return is_metavar(get_app_fn(e)); }
    bool has_expr_metavar(expr const & e) { return has_idx_expr_metavar(e); }
    optional<expr> is_ac(expr const & /* e */) {
        // TODO(Leo): enable AC matching when it is done
        return none_expr();
        // return m_cc.is_ac(e);
    }
    optional<expr> get_binary_op(expr const & e) {
        if (is_app(e) && is_app(app_fn(e)))
            return some_expr(app_fn(app_fn(e)));
        else
            return none_expr();
    }

    expr tmp_internalize(expr const & e) {
        expr new_e = m_cc.normalize(e);
        m_cc.internalize(new_e, 0);
        return new_e;
    }

    bool is_ground_eq(expr const & p, expr const & t) {
        lean_assert(!has_expr_metavar(p));
        lean_assert(!has_expr_metavar(t));
        return m_cc.is_eqv(p, t) || m_ctx.is_def_eq(p, t);
    }

    /* Return true iff e is a metavariable, and we have an assignment of the
       form e := ?m + s, where + is an AC operator, and ?m is another metavariable. */
    bool is_partially_solved(expr const & e) {
        lean_assert(is_metavar(e));
        if (auto v = m_ctx.get_assignment(e)) {
            return is_ac(*v) && m_ctx.is_tmp_mvar(app_arg(app_fn(*v)));
        } else {
            return false;
        }
    }

    void flat_ac(expr const & op, expr const & e, buffer<expr> & args) {
        if (optional<expr> curr_op = get_binary_op(e)) {
            if (m_ctx.is_def_eq(op, *curr_op)) {
                flat_ac(op, app_arg(app_fn(e)), args);
                flat_ac(op, app_arg(e), args);
                return;
            }
        }
        args.push_back(e);
    }

    /* Cancel ground terms that occur in p_args and t_args.
       Example:
       Given
          [?x, 0, ?y] [a, b, 0, c],
       the result is:
            [?x, ?y] [a, b, c]
    */
    void ac_cancel_terms(buffer<expr> & p_args, buffer<expr> & t_args) {
        unsigned j = 0;
        for (unsigned i = 0; i < p_args.size(); i++) {
            if (has_expr_metavar(p_args[i])) {
                p_args[j] = p_args[i];
                j++;
            } else {
                expr p = tmp_internalize(p_args[i]);
                unsigned k = 0;
                for (; k < t_args.size(); k++) {
                    if (is_ground_eq(p, t_args[k])) {
                        break;
                    }
                }
                if (k == t_args.size()) {
                    p_args[j] = p;
                    j++;
                } else {
                    // cancelled
                    t_args.erase(k);
                }
            }
        }
        p_args.shrink(j);
    }

    expr mk_ac_term(expr const & op, buffer<expr> const & args) {
        lean_assert(!args.empty());
        expr r = args.back();
        unsigned i = args.size() - 1;
        while (i > 0) {
            --i;
            r = mk_app(op, args[i], r);
        }
        return r;
    }

    expr mk_ac_term(expr const & op, list<expr> const & args) {
        buffer<expr> b;
        to_buffer(args, b);
        return mk_ac_term(op, b);
    }

    void display_ac_cnstr(io_state_stream const & out, ematch_cnstr const & c) {
        expr p = mk_ac_term(ac_op(c), ac_p(c));
        expr t = mk_ac_term(ac_op(c), ac_t(c));
        auto fmt = out.get_formatter();
        format r = group(fmt(p) + line() + format("=?=") + line() + fmt(t));
        out << r;
    }

    void process_new_ac_cnstr(state const & s, expr const & p, expr const & t, buffer<pair<state, unsigned>> & new_states) {
        optional<expr> op = is_ac(t);
        lean_assert(op);
        buffer<expr> p_args, t_args;
        flat_ac(*op, p, p_args);
        flat_ac(*op, t, t_args);
        lean_assert(t_args.size() >= 2);
        if (p_args.empty()) {
            /* This can happen if we fail to unify the operator in p with the one in t. */
            return;
        }
        lean_assert(p_args.size() >= 2);
        ac_cancel_terms(p_args, t_args);
        if (p_args.size() == 1 && t_args.size() == 1) {
            new_states.emplace_back(cons(mk_match_eq_cnstr(p_args[0], t_args[0]), s), m_gen);
            return;
        }
        list<expr> ps  = to_list(p_args);
        buffer<expr> new_t_args;
        /* Create a family of AC-matching constraints by replacing t-arguments
           with op-applications that are in the same equivalence class.

           Example: given (a = b + c) (d = e + f) and t is of the form (a + d).
           expand, will add the following AC constraints

               p =?= a + d
               p =?= a + e + f
               p =?= b + c + d
               p =?= b + c + e + f

           To avoid non termination, we unfold a t_arg at most once.
           Here is an example that would produce non-termination if
           we did not use unfolded.

           Given (a = a + a) and t is of the form (a + d).
           We would be able to produce

              p =?= a + d
              p =?= a + a + d
              ...
              p =?= a + ... + a + d
              ...
        */
        std::function<void(unsigned, rb_expr_tree const &)>
        expand = [&](unsigned i, rb_expr_tree const & unfolded) {
            check_system("ematching");
            if (i == t_args.size()) {
                ematch_cnstr c = mk_match_ac_cnstr(*op, ps, to_list(new_t_args));
                lean_trace(name({"debug", "smt", "ematch"}), tout() << "new ac constraint: "; display_ac_cnstr(tout(), c); tout() << "\n";);
                new_states.emplace_back(cons(c, s), m_gen);
            } else {
                expr const & t_arg = t_args[i];
                new_t_args.push_back(t_arg);
                expand(i+1, unfolded);
                new_t_args.pop_back();
                /* search for op-applications in eqc(t_arg) */
                rb_expr_tree new_unfolded = unfolded;
                bool first = true;
                expr it    = t_arg;
                do {
                    if (auto op2 = is_ac(it)) {
                        if (*op == *op2) {
                            unsigned sz = t_args.size();
                            flat_ac(*op, it, t_args);
                            if (first) {
                                new_unfolded.insert(t_arg);
                                first = false;
                            }
                            expand(i+1, new_unfolded);
                            t_args.shrink(sz);
                        }
                    }
                    it = m_cc.get_next(it);
                } while (it != t_arg);
            }
        };
        expand(0, rb_expr_tree());
    }

    void push_states(buffer<pair<state, unsigned>> & new_states) {
        if (new_states.size() == 1) {
            lean_trace(name({"debug", "smt", "ematch"}), tout() << "(only one match)\n";);
            m_state = new_states[0].first;
            m_gen   = new_states[0].second;
        } else {
            lean_trace(name({"debug", "smt", "ematch"}), tout() << "# matches: " << new_states.size() << "\n";);
            m_state = new_states.back().first;
            m_gen   = new_states.back().second;
            new_states.pop_back();
            m_choice_stack.append(new_states);
            for (unsigned i = 0; i < new_states.size(); i++)
                m_ctx.push_scope();
        }
    }

    bool ac_merge_clash_p(expr const & p, expr const & t) {
        lean_assert(is_metavar(p) && is_partially_solved(p));
        tout() << "ac_merge_clash_p: " << p << " =?= " << t << "\n";
        // TODO(Leo):
        lean_unreachable();
    }

    bool is_ac_eqv(expr const & p, expr const & t) {
        lean_assert(is_ac(t));
        if (is_metavar(p) && is_partially_solved(p)) {
            return ac_merge_clash_p(p, t);
        } else {
            /* When AC support is enabled, metavariables may be assigned to terms
               that have not been internalized. */
            expr new_p = safe_instantiate_mvars(p);
            if (!has_expr_metavar(new_p)) {
                new_p = tmp_internalize(new_p);
                return is_ground_eq(new_p, t);
            } else {
                return m_ctx.is_def_eq(new_p, t);
            }
        }
    }

    bool is_eqv(expr const & p, expr const & t) {
        if (is_ac(t)) {
            return is_ac_eqv(p, t);
        } else if (!has_expr_metavar(p)) {
            return is_ground_eq(p, t);
        } else if (is_meta(p)) {
            expr const & m = get_app_fn(p);
            if (!m_ctx.is_assigned(m)) {
                expr p_type = safe_instantiate_mvars(m_ctx.infer(p));
                expr t_type = m_ctx.infer(t);
                if (m_ctx.is_def_eq(p_type, t_type)) {
                    /* Types are definitionally equal. So, we just assign */
                    return m_ctx.is_def_eq(p, t);
                } else if (!has_expr_metavar(p_type) && !has_expr_metavar(t_type)) {
                    /* Check if types are provably equal and apply cast
                       Here is some background on this case. p is a metavariable ?m.
                       So, it should be the argument of some function application (f a_1 ... a_k ?m ...).
                       Reason: p is a subterm of a valid pattern.
                       Then, t should also be the argument of a function application (f b_1 ... b_k t ...).
                       Reason: how the ematching procedure works.
                       Moreover, the types of ?m and t should be of the form
                             ?m : A_{k+1}[a_1 ... a_k]
                             t  : A_{k+1}[b_1 ... b_k]
                       The function applications are type correct, and the type of f should be of the form:
                          f : Pi (x_1 : A_1) (x_2 : A_2[x_1]) ... (x_k : A_k[x_1, ... x_{k-1}]) (x_{k+1} : A_{k+1}[x_1, ..., x_k]) ..., B
                       The subproblems a_i == b_i have already been processed. So,
                       A[a_1 ... a_k] is probably congruent to A[b_1 ... b_k].
                       We say "probably" because we may miss some cases depending on how the equalities
                       have been processed. For example, A_{k+1}[...] may contain binders,
                       and we may not have visited them.
                       Important: we must process arguments from left to right. Otherwise, the "trick"
                       above will not work.
                    */
                    p_type = tmp_internalize(p_type);
                    t_type = tmp_internalize(t_type);
                    if (auto H = m_cc.get_eq_proof(t_type, p_type)) {
                        expr cast_H_t = mk_cast(m_ctx, *H, t);
                        return m_ctx.is_def_eq(p, cast_H_t);
                    } else {
                        /* Types are not definitionally equal nor provably equal */
                        return false;
                    }
                } else {
                    /* Types are not definitionally equal, and we cannot check whether they are provably equal
                       using cc since they contain metavariables */
                    return false;
                }
            } else if (is_metavar(p) && is_partially_solved(p)) {
                return ac_merge_clash_p(p, t);
            } else {
                expr new_p = safe_instantiate_mvars(p);
                if (!has_expr_metavar(new_p)) {
                    return is_ground_eq(new_p, t);
                } else {
                    return m_ctx.is_def_eq(new_p, t);
                }
            }
        } else {
            return m_ctx.is_def_eq(p, t);
        }
    }

    /* If the eq equivalence class of `t` is heterogeneous, then even though
       `t` may fail to match because of its type, another element that is
       heterogeneously equal to `t`, but that has a different type, may match
       successfully. */
    bool match_leaf(expr const & p, expr const & t) {
        if (m_cc.in_heterogeneous_eqc(t)) {
            buffer<pair<state, unsigned>> new_states;
            rb_expr_set types_seen;
            expr it = t;
            do {
                expr it_type = m_ctx.infer(it);
                if (!types_seen.find(it_type)) {
                    types_seen.insert(it_type);
                    new_states.emplace_back(cons(mk_eqv_cnstr(p, it), m_state), m_gen);
                }
                it = m_cc.get_next(it);
            } while (it != t);
            push_states(new_states);
            return true;
        } else {
            return is_eqv(p, t);
        }
    }

    bool match_args(state & s, buffer<expr> const & p_args, expr const & t) {
        optional<ext_congr_lemma> cg_lemma = m_cc.mk_ext_congr_lemma(t);
        if (!cg_lemma) return false;
        buffer<expr> t_args;
        expr const & fn = get_app_args(t, t_args);
        if (p_args.size() != t_args.size())
            return false;
        if (cg_lemma->m_hcongr_lemma) {
            /* Lemma was created using mk_hcongr_lemma */
            fun_info finfo                 = get_fun_info(m_ctx, fn, t_args.size());
            list<ss_param_info> sinfo      = get_subsingleton_info(m_ctx, fn, t_args.size());
            list<param_info> const * it1   = &finfo.get_params_info();
            list<ss_param_info> const *it2 = &sinfo;
            buffer<ematch_cnstr> new_cnstrs;
            for (unsigned i = 0; i < t_args.size(); i++) {
                if (*it1 && head(*it1).is_inst_implicit()) {
                    new_cnstrs.push_back(mk_defeq_cnstr(p_args[i], t_args[i]));
                    lean_assert(new_cnstrs.back().kind() == ematch_cnstr_kind::DefEqOnly);
                } else if (*it2 && head(*it2).is_subsingleton()) {
                    new_cnstrs.push_back(mk_match_ss_cnstr(p_args[i], t_args[i]));
                    lean_assert(new_cnstrs.back().kind() == ematch_cnstr_kind::MatchSS);
                } else {
                    new_cnstrs.push_back(mk_match_eq_cnstr(p_args[i], t_args[i]));
                    lean_assert(new_cnstrs.back().kind() == ematch_cnstr_kind::Match);
                }
                if (*it1) it1 = &tail(*it1);
                if (*it2) it2 = &tail(*it2);
            }
            s = to_list(new_cnstrs.begin(), new_cnstrs.end(), s);
            return true;
        } else {
            return false;
        }
    }

    bool process_match(expr const & p, expr const & t) {
        lean_trace(name({"debug", "smt", "ematch"}),
                   expr new_p      = safe_instantiate_mvars(p);
                   expr new_p_type = safe_instantiate_mvars(m_ctx.infer(p));
                   expr t_type     = m_ctx.infer(t);
                   tout() << "try process_match: " << p << " ::= " << new_p << " : " << new_p_type << " <=?=> "
                   << t << " : " << t_type << "\n";);
        if (!is_app(p)) {
            return match_leaf(p, t);
        }
        buffer<expr> p_args;
        expr const & fn = get_app_args(p, p_args);
        if (m_ctx.is_tmp_mvar(fn)) {
            return match_leaf(p, t);
        }
        buffer<pair<expr, unsigned>> candidates;
        expr t_fn;
        expr it = t;
        do {
            if (check_generation(it)) {
                expr const & it_fn = get_app_fn(it);
                bool ok = false;
                if ((m_cc.is_congr_root(it) || m_cc.in_heterogeneous_eqc(it)) &&
                    m_ctx.is_def_eq(it_fn, fn) &&
                    get_app_num_args(it) == p_args.size()) {
                    t_fn = it_fn;
                    ok = true;
                    candidates.emplace_back(it, m_cc.get_generation_of(it));
                }
                lean_trace(name({"debug", "smt", "ematch"}),
                           tout() << "candidate: " << it << "..." << (ok ? "ok" : "skip") << "\n";);
            }
            it = m_cc.get_next(it);
        } while (it != t);

        if (candidates.empty()) {
            lean_trace(name({"debug", "smt", "ematch"}), tout() << "(no candidates)\n";);
            return false;
        }
        buffer<pair<state, unsigned>> new_states;
        for (pair<expr, unsigned> const & c_gen : candidates) {
            expr const & c = c_gen.first;
            unsigned gen   = c_gen.second;
            state new_state = m_state;
            if (is_ac(c)) {
                process_new_ac_cnstr(new_state, p, t, new_states);
            } else if (match_args(new_state, p_args, c)) {
                lean_trace(name({"debug", "smt", "ematch"}), tout() << "match: " << c << "\n";);
                new_states.emplace_back(new_state, std::max(m_gen, gen));
            }
        }
        if (new_states.empty()) {
            lean_trace(name({"debug", "smt", "ematch"}), tout() << "(no new states)\n";);
            return false;
        }
        push_states(new_states);
        return true;
    }

    bool match_args_prefix(state & s, buffer<expr> const & p_args, expr const & t) {
        unsigned t_nargs = get_app_num_args(t);
        expr it = t;
        while (t_nargs > p_args.size()) {
            t_nargs--;
            it = app_fn(it);
        }
        return match_args(s, p_args, it);
    }

    bool check_generation(expr const & t) {
        unsigned gen = m_cc.get_generation_of(t);
        if (gen >= m_em_state.m_config.m_max_generation) {
            lean_trace(name({"smt", "ematch"}), tout() << "skipping term generation: " << gen
                       << ", instances based on exceeds the limit\n" << t << "\n";);
            return false;
        } else {
            return true;
        }
    }

    bool process_continue(expr const & p) {
        lean_trace(name({"debug", "smt", "ematch"}), tout() << "process_continue: " << p << "\n";);
        buffer<expr> p_args;
        expr const & f = get_app_args(p, p_args);
        buffer<pair<state, unsigned>> new_states;
        if (auto s = m_em_state.get_app_map().find(head_index(f))) {
            s->for_each([&](expr const & t) {
                    if (check_generation(t) && (m_cc.is_congr_root(t) || m_cc.in_heterogeneous_eqc(t))) {
                        state new_state = m_state;
                        if (match_args_prefix(new_state, p_args, t))
                            new_states.emplace_back(new_state, m_cc.get_generation_of(t));
                    }
                });
            if (new_states.empty()) {
                return false;
            } else {
                push_states(new_states);
                return true;
            }
        } else {
            return false;
        }
    }

    /* (Basic) subsingleton matching support: solve p =?= t when
       typeof(p) and typeof(t) are subsingletons */
    bool process_matchss(expr const & p, expr const & t) {
        lean_trace(name({"debug", "smt", "ematch"}),
                   expr new_p      = safe_instantiate_mvars(p);
                   expr new_p_type = safe_instantiate_mvars(m_ctx.infer(p));
                   expr t_type     = m_ctx.infer(t);
                   tout() << "process_matchss: " << p << " ::= " << new_p << " : " << new_p_type << " <=?=> "
                   << t << " : " << t_type << "\n";);
        if (!is_metavar(p)) {
            /* If p is not a metavariable we simply ignore it.
               We should improve this case in the future. */
            lean_trace(name({"debug", "smt", "ematch"}), tout() << "(p not a metavar)\n";);
            return true;
        }
        expr p_type = safe_instantiate_mvars(m_ctx.infer(p));
        expr t_type = m_ctx.infer(t);
        if (m_ctx.is_def_eq(p_type, t_type)) {
            bool success = m_ctx.is_def_eq(p, t);
            lean_trace(name({"debug", "smt", "ematch"}),
                       tout() << "types are def_eq and assignment..." << (success ? "succeeded" : "failed") << "\n";);
            return success;
        } else {
            /* Check if the types are provably equal, and cast t */
            p_type = tmp_internalize(p_type);
            if (auto H = m_cc.get_eq_proof(t_type, p_type)) {
                expr cast_H_t = mk_cast(m_ctx, *H, t);
                bool success = m_ctx.is_def_eq(p, cast_H_t);
                lean_trace(name({"debug", "smt", "ematch"}),
                           tout() << "types can be proved equal and assignment..." << (success ? "succeeded" : "failed") << "\n";);
                return success;
            }
        }
        lean_trace(name({"debug", "smt", "ematch"}), tout() << "types cannot be proved equal\n";);
        return false;
    }

    bool process_defeq_only(ematch_cnstr const & c) {
        expr const & p = cnstr_p(c);
        expr const & t = cnstr_t(c);
        bool success = m_ctx.is_def_eq(p, t);
        lean_trace(name({"debug", "smt", "ematch"}),
                   expr new_p      = safe_instantiate_mvars(p);
                   expr new_p_type = safe_instantiate_mvars(m_ctx.infer(p));
                   expr t_type     = m_ctx.infer(t);
                   tout() << "must be def-eq: " << new_p << " : " << new_p_type
                   << "  =?= " << t << " : " << t_type
                   << " ... " << (success ? "succeeded" : "failed") << "\n";);
        return success;
    }

    bool process_eqv_only(ematch_cnstr const & c) {
        expr const & p = cnstr_p(c);
        expr const & t = cnstr_t(c);
        bool success = is_eqv(p, t);
        lean_trace(name({"debug", "smt", "ematch"}),
                   expr new_p      = safe_instantiate_mvars(p);
                   expr new_p_type = safe_instantiate_mvars(m_ctx.infer(p));
                   expr t_type     = m_ctx.infer(t);
                   tout() << "must be eqv: " << new_p << " : " << new_p_type << " =?= "
                   << t << " : " << t_type << " ... " << (success ? "succeeded" : "failed") << "\n";);
        return success;
    }

    bool process_match_ac(ematch_cnstr const & /* c */) {
        // TODO(Leo)
        lean_unreachable();
    }

    bool is_done() const {
        return is_nil(m_state);
    }

    bool process_next() {
        lean_assert(!is_done());
        /* TODO(Leo): select easy constraint first */
        ematch_cnstr c = head(m_state);
        m_state        = tail(m_state);

        switch (c.kind()) {
        case ematch_cnstr_kind::DefEqOnly:
            return process_defeq_only(c);
        case ematch_cnstr_kind::Match:
            return process_match(cnstr_p(c), cnstr_t(c));
        case ematch_cnstr_kind::EqvOnly:
            return process_eqv_only(c);
        case ematch_cnstr_kind::MatchSS:
            return process_matchss(cnstr_p(c), cnstr_t(c));
        case ematch_cnstr_kind::Continue:
            return process_continue(cont_p(c));
        case ematch_cnstr_kind::MatchAC:
            return process_match_ac(c);
        }
        lean_unreachable();
    }

    bool backtrack() {
        lean_trace(name({"debug", "smt", "ematch"}), tout() << "backtrack\n";);
        if (m_choice_stack.empty())
            return false;
        m_ctx.pop_scope();
        m_state = m_choice_stack.back().first;
        m_gen   = m_choice_stack.back().second;
        m_choice_stack.pop_back();
        return true;
    }

    void instantiate(hinst_lemma const & lemma) {
        list<bool> const * it = &lemma.m_is_inst_implicit;
        buffer<expr> lemma_args;
        for (expr const & mvar : lemma.m_mvars) {
            if (!m_ctx.is_assigned(mvar)) {
                if (!head(*it)) {
                    lean_trace(name({"debug", "smt", "ematch"}),
                               tout() << "instantiation failure [" << lemma.m_id << "], " <<
                               "unassigned argument not inst-implicit: " << m_ctx.infer(mvar) << "\n";);
                    return; // fail, argument is not instance implicit
                }
                auto new_val = m_ctx.mk_class_instance(m_ctx.infer(mvar));
                if (!new_val) {
                    lean_trace(name({"debug", "smt", "ematch"}),
                               tout() << "instantiation failure [" << lemma.m_id << "], " <<
                               "cannot synthesize unassigned inst-implicit argument: " << m_ctx.infer(mvar) << "\n";);
                    return; // fail, instance could not be generated
                }
                if (!m_ctx.is_def_eq(mvar, *new_val)) {
                    lean_trace(name({"debug", "smt", "ematch"}),
                               tout() << "instantiation failure [" << lemma.m_id << "], " <<
                               "unable to assign inst-implicit argument: " << *new_val << " : " << m_ctx.infer(mvar) << "\n";);
                    return; // fail, type error
                }
            }
            lemma_args.push_back(mvar);
            it = &tail(*it);
        }

        for (expr & lemma_arg : lemma_args) {
            lemma_arg = instantiate_mvars(lemma_arg);
            if (has_idx_metavar(lemma_arg)) {
                lean_trace(name({"debug", "smt", "ematch"}),
                           tout() << "instantiation failure [" << lemma.m_id << "], " <<
                           "there are unassigned metavariables\n";);
                return; // result contains temporary metavariables
            }
        }

        if (!m_em_state.save_instance(lemma.m_prop, lemma_args)) {
            return; // already added this instance
        }

        expr new_inst  = instantiate_mvars(lemma.m_prop);
        if (has_idx_metavar(new_inst)) {
            lean_trace(name({"debug", "smt", "ematch"}),
                       tout() << "new instance contains unassigned metavariables\n"
                       << new_inst << "\n";);
            return; // result contains temporary metavariables
        }

        lean_trace(name({"smt", "ematch"}),
                   tout() << "instance [" << lemma.m_id << "], generation: " << m_gen+1
                   << "\n" << new_inst << "\n";);
        expr new_proof = instantiate_mvars(lemma.m_proof);
        m_new_instances.push_back({new_inst, new_proof, m_gen+1});
    }

    void search(hinst_lemma const & lemma) {
        while (true) {
            check_system("ematching");
            if (is_done()) {
                instantiate(lemma);
                if (!backtrack())
                    return;
            }
            if (!process_next()) {
                if (!backtrack())
                    return;
            }
        }
    }

    void clear_choice_stack() {
        for (unsigned i = 0; i < m_choice_stack.size(); i++) {
            m_ctx.pop_scope();
        }
        m_choice_stack.clear();
    }

    state mk_inital_state(buffer<expr> const & ps) {
        state s;
        unsigned i = ps.size();
        while (i > 1) {
            --i;
            s = cons(mk_continue(ps[i]), s);
        }
        return s;
    }

    /* Ematch p =?= t with initial state init. p is the pattern, and t is a term.
       The inital state init is used for multipatterns.
       The given lemma is instantiated for each solution found.
       The new instances are stored at m_new_instances. */
    void main(hinst_lemma const & lemma, state const & init, expr const & p, expr const & t) {
        type_context_old::tmp_mode_scope scope(m_ctx, lemma.m_num_uvars, lemma.m_num_mvars);
        lean_assert(!has_idx_metavar(t));
        clear_choice_stack();
        m_state = init;
        buffer<expr> p_args;
        expr const & fn = get_app_args(p, p_args);
        m_gen = m_cc.get_generation_of(t);
        if (!m_ctx.is_def_eq(fn, get_app_fn(t)))
            return;
        if (check_generation(t) && !match_args_prefix(m_state, p_args, t))
            return;
        search(lemma);
    }

    void ematch_term(hinst_lemma const & lemma, multi_pattern const & mp, expr const & t) {
        buffer<expr> ps;
        to_buffer(mp, ps);
        /* TODO(Leo): use heuristic to select the pattern we will match first */
        state init_state = mk_inital_state(ps);
        main(lemma, init_state, ps[0], t);
    }

    void ematch_terms_core(hinst_lemma const & lemma, buffer<expr> const & ps, bool filter) {
        expr const & fn  = get_app_fn(ps[0]);
        unsigned gmt     = m_cc.get_gmt();
        state init_state = mk_inital_state(ps);
        if (rb_expr_set const * s = m_em_state.get_app_map().find(head_index(fn))) {
            s->for_each([&](expr const & t) {
                    if ((m_cc.is_congr_root(t) || m_cc.in_heterogeneous_eqc(t)) &&
                        (!filter || m_cc.get_mt(t) == gmt)) {
                        main(lemma, init_state, ps[0], t);
                    }
                });
        }
    }

    /* Match internalized terms in m_em_state with the given multipatterns.
       If filter is true, then we use the term modification time information
       stored in the congruence closure module. Only terms with
       modification time (mt) >= the global modification time (gmt) are considered. */
    void ematch_terms(hinst_lemma const & lemma, multi_pattern const & mp, bool filter) {
        buffer<expr> ps;
        to_buffer(mp, ps);
        if (filter) {
            for (unsigned i = 0; i < ps.size(); i++) {
                std::swap(ps[0], ps[i]);
                ematch_terms_core(lemma, ps, filter);
                std::swap(ps[0], ps[i]);
            }
        } else {
            ematch_terms_core(lemma, ps, filter);
        }
    }


    /* Match internalized terms in m_em_state with the given lemmas. */
    void ematch_using_lemmas(hinst_lemmas const & lemmas, bool filter) {
        lemmas.for_each([&](hinst_lemma const & lemma) {
                if (!m_em_state.max_instances_exceeded()) {
                    ematch_terms(lemma, filter);
                }
            });
    }

public:
    ematch_fn(type_context_old & ctx, ematch_state & ems, congruence_closure & cc, buffer<new_instance> & new_insts):
        m_ctx(ctx), m_em_state(ems), m_cc(cc), m_new_instances(new_insts) {}

    void ematch_term(hinst_lemma const & lemma, expr const & t) {
        /* The following scope is a temporary workaround, we need to refactor this module
           and adapt all improvements added to type_context_old::is_def_eq. */
        for (multi_pattern const & mp : lemma.m_multi_patterns) {
            ematch_term(lemma, mp, t);
        }
    }

    /* Match internalized terms in m_em_state with the given lemma. */
    void ematch_terms(hinst_lemma const & lemma, bool filter) {
        /* The following scope is a temporary workaround, we need to refactor this module
           and adapt all improvements added to type_context_old::is_def_eq. */
        for (multi_pattern const & mp : lemma.m_multi_patterns) {
            ematch_terms(lemma, mp, filter);
        }
    }

    void operator()() {
        if (m_em_state.max_instances_exceeded())
            return;
        /* The following scope is a temporary workaround, we need to refactor this module
           and adapt all improvements added to type_context_old::is_def_eq. */
        ematch_using_lemmas(m_em_state.get_new_lemmas(), false);
        ematch_using_lemmas(m_em_state.get_lemmas(), true);
        m_em_state.m_lemmas.merge(m_em_state.m_new_lemmas);
        m_em_state.m_new_lemmas = hinst_lemmas();
        m_cc.inc_gmt();
    }
};

void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, expr const & t, buffer<new_instance> & result) {
    congruence_closure::state_scope scope(cc);
    ematch_fn(ctx, s, cc, result).ematch_term(lemma, t);
}

void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, bool filter, buffer<new_instance> & result) {
    congruence_closure::state_scope scope(cc);
    ematch_fn(ctx, s, cc, result).ematch_terms(lemma, filter);
}

void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, buffer<new_instance> & result) {
    congruence_closure::state_scope scope(cc);
    ematch_fn(ctx, s, cc, result)();
}

struct vm_ematch_state : public vm_external {
    ematch_state m_val;
    vm_ematch_state(ematch_state const & v): m_val(v) {}
    virtual ~vm_ematch_state() {}
    virtual void dealloc() override { this->~vm_ematch_state(); get_vm_allocator().deallocate(sizeof(vm_ematch_state), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_ematch_state(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_ematch_state))) vm_ematch_state(m_val); }
};

ematch_state const & to_ematch_state(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_ematch_state*>(to_external(o)));
    return static_cast<vm_ematch_state*>(to_external(o))->m_val;
}

vm_obj to_obj(ematch_state const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_ematch_state))) vm_ematch_state(s));
}

/*
structure ematch_config :=
(max_instances  : nat := 10000)
(max_generation : nat := 10)
*/
ematch_config to_ematch_config(vm_obj const & cfg) {
    ematch_config r;
    r.m_max_instances  = force_to_unsigned(cfield(cfg, 0));
    r.m_max_generation = force_to_unsigned(cfield(cfg, 1));
    return r;
}

vm_obj ematch_state_mk(vm_obj const & cfg) {
    return to_obj(ematch_state(to_ematch_config(cfg)));
}

vm_obj ematch_state_internalize(vm_obj const & ems, vm_obj const & e, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    ematch_state S   = to_ematch_state(ems);
    type_context_old ctx = mk_type_context_for(s);
    S.internalize(ctx, to_expr(e));
    return tactic::mk_success(to_obj(S), tactic::to_state(s));
    LEAN_TACTIC_CATCH(tactic::to_state(s));
}

vm_obj mk_ematch_result(buffer<new_instance> const & new_inst_buffer, congruence_closure::state const & ccs,
                        ematch_state const & ems) {
    vm_obj new_insts = mk_vm_nil();
    unsigned i = new_inst_buffer.size();
    while (i > 0) {
        --i;
        new_insts = mk_vm_cons(mk_vm_pair(to_obj(new_inst_buffer[i].m_instance), to_obj(new_inst_buffer[i].m_proof)), new_insts);
    }
    return mk_vm_pair(new_insts, mk_vm_pair(to_obj(ccs), to_obj(ems)));
}

vm_obj ematch_core(vm_obj const & md, vm_obj const & _ccs, vm_obj const & _ems, vm_obj const & hlemma, vm_obj const & t, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    LEAN_TACTIC_TRY;
    type_context_old ctx    = mk_type_context_for(_s, md);
    ematch_state ems    = to_ematch_state(_ems);
    defeq_can_state dcs = s.dcs();
    congruence_closure::state ccs = to_cc_state(_ccs);
    congruence_closure cc(ctx, ccs, dcs);
    buffer<new_instance> new_inst_buffer;
    ematch(ctx, ems, cc, to_hinst_lemma(hlemma), to_expr(t), new_inst_buffer);
    vm_obj r = mk_ematch_result(new_inst_buffer, ccs, ems);
    tactic_state new_s = set_dcs(s, dcs);
    return tactic::mk_success(r, new_s);
    LEAN_TACTIC_CATCH(s);
}

vm_obj ematch_all_core(vm_obj const & md, vm_obj const & _ccs, vm_obj const & _ems, vm_obj const & hlemma, vm_obj const & filter, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    LEAN_TACTIC_TRY;
    type_context_old ctx    = mk_type_context_for(_s, md);
    ematch_state ems    = to_ematch_state(_ems);
    defeq_can_state dcs = s.dcs();
    congruence_closure::state ccs = to_cc_state(_ccs);
    congruence_closure cc(ctx, ccs, dcs);
    buffer<new_instance> new_inst_buffer;
    ematch(ctx, ems, cc, to_hinst_lemma(hlemma), to_bool(filter), new_inst_buffer);
    vm_obj r = mk_ematch_result(new_inst_buffer, ccs, ems);
    tactic_state new_s = set_dcs(s, dcs);
    return tactic::mk_success(r, new_s);
    LEAN_TACTIC_CATCH(s);
}

void initialize_ematch() {
    register_trace_class(name{"smt", "ematch"});
    register_trace_class(name({"debug", "smt", "ematch"}));

    DECLARE_VM_BUILTIN(name({"ematch_state", "mk"}),               ematch_state_mk);
    DECLARE_VM_BUILTIN(name({"ematch_state", "internalize"}),      ematch_state_internalize);
    DECLARE_VM_BUILTIN(name({"tactic", "ematch_core"}),            ematch_core);
    DECLARE_VM_BUILTIN(name({"tactic", "ematch_all_core"}),        ematch_all_core);
}
void finalize_ematch() {
}
}
