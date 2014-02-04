/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include "kernel/for_each_fn.h"
#include "kernel/type_checker.h"
#include "kernel/type_checker_justification.h"
#include "kernel/unification_constraint.h"
#include "library/io_state_stream.h"
#include "library/expr_lt.h"
#include "library/elaborator/elaborator.h"
#include "frontends/lean/parser_imp.h"

namespace lean {
static name g_apply("apply");
static name g_done("done");
static name g_back("back");
static name g_abort("abort");
static name g_assumption("assumption");
static list<name> g_tactic_cmds = { g_apply, g_done, g_back, g_abort, g_assumption };

bool parser_imp::curr_is_tactic_cmd() const {
    return curr_is_identifier() && std::find(g_tactic_cmds.begin(), g_tactic_cmds.end(), curr_name()) != g_tactic_cmds.end();
}

void parser_imp::display_proof_state(proof_state s) {
    regular(m_io_state) << "Proof state:\n" << s << endl;
}

void parser_imp::display_proof_state_if_interactive(proof_state s) {
    if (m_interactive)
        display_proof_state(s);
}

/**
   \brief Apply tactic \c t to state \c s.
   When \c t succeeds, it returns the head and tail of the output state sequence.
   Throws an exception if the tactic fails, and use \c p to sign the error position.
*/
std::pair<proof_state, proof_state_seq> parser_imp::apply_tactic(proof_state const & s, tactic const & t, pos_info const & p) {
    proof_state_seq::maybe_pair r;
    code_with_callbacks([&]() {
            // t may have call-backs we should set ios in the script_state
            proof_state_seq seq = t(m_env, m_io_state, s);
            r = seq.pull();
        });
    if (r) {
        return mk_pair(r->first, r->second);
    } else {
        throw tactic_cmd_error("tactic failed", p, s);
    }
}

/**
   \brief Try to create a proof for the input state \c s.
   It basically applies the proof_builder if \c s does not contain
   any goals left. The position information is used to throw an exception
   if \c s is not a final state.

   The resultant proof must have type \c expected_type in the context \c ctx.
*/
expr parser_imp::mk_proof_for(proof_state const & s, pos_info const & p, context const & ctx, expr const & expected_type) {
    if (s.is_proof_final_state()) {
        assignment a(s.get_menv().copy());
        proof_map  m;
        expr pr = s.get_proof_builder()(m, a);
        if (has_metavar(pr)) {
            // Some tactics generate metavariables that can only be instantiated by type inference elaboration.
            // Example: apply_tactic.
            metavar_env menv = s.get_menv().copy();
            buffer<unification_constraint> ucs;
            expr pr_type = type_checker(m_env).check(pr, ctx, menv, ucs);
            ucs.push_back(mk_convertible_constraint(ctx, pr_type, expected_type, mk_type_match_justification(ctx, expected_type, pr)));
            elaborator elb(m_env, menv, ucs.size(), ucs.data(), m_io_state.get_options());
            metavar_env new_menv = elb.next();
            pr = new_menv->instantiate_metavars(pr);
            if (has_metavar(pr))
                throw exception("synthesized proof object has unsolved metavars");
        }
        return pr;
    } else {
        throw tactic_cmd_error("invalid 'done' command, proof cannot be produced from this state", p, s);
    }
}

/**
   \brief Execute the \c back (backtrack) tactic command.  It
   succeeds if the stack \c stack contains proof states.  When it
   succeeds, \c s is updated with the next state in the state
   sequence on the top of \c stack. The new state is also removed
   from the stack.
*/
void parser_imp::back_cmd(/* inout */ proof_state_seq_stack & stack, /* inout */ proof_state & s) {
    auto p = pos();
    next();
    while (!stack.empty()) {
        check_interrupted();
        lazy_list<proof_state> seq = stack.back();
        stack.pop_back();
        proof_state_seq::maybe_pair r;
        code_with_callbacks([&]() {
                r = seq.pull();
            });
        if (r) {
            stack.push_back(r->second);
            s = r->first;
            return;
        }
    }
    throw tactic_cmd_error("failed to backtrack", p, s);
}

/**
   \brief Execute the tactic.
   This command just applies the tactic to the input state \c s.
   If it succeeds, \c s is assigned to the head of the output
   state sequence produced by the tactic.  The rest/tail of the
   output state sequence is stored on the top of the stack \c
   stack.
*/
void parser_imp::tactic_cmd(/* inout */ proof_state_seq_stack & stack, /* inout */ proof_state & s) {
    auto tac_pos = pos();
    tactic t = parse_tactic_expr();
    auto r = apply_tactic(s, t, tac_pos);
    s = r.first;
    stack.push_back(r.second);
}

/**
   \brief Execute the \c done tactic command. It succeeds if
   a proof for \c s can be built.
*/
expr parser_imp::done_cmd(proof_state const & s, context const & ctx, expr const & expected_type) {
    auto p = pos();
    next();
    return mk_proof_for(s, p, ctx, expected_type);
}

/**
   \brief Parse tactic command sequence for solving input state \c s.

   The proof for \c s must have type \c expected_type in the context \c ctx.
*/
expr parser_imp::parse_tactic_cmds(proof_state s, context const & ctx, expr const & expected_type) {
    proof_state_seq_stack stack;
    optional<expr> pr;
    enum class status { Continue, Done, Eof, Abort };
    status st = status::Continue;
    while (st == status::Continue) {
        protected_call(
            [&]() {
                auto p = pos();
                check_interrupted();
                name id;
                switch (curr()) {
                case scanner::token::Period:
                    display_proof_state_if_interactive(s);
                    show_tactic_prompt();
                    next();
                    break;
                case scanner::token::Eof:
                    st = status::Eof;
                    break;
                case scanner::token::Id:
                    id = curr_name();
                    if (id == g_back) {
                        back_cmd(stack, s);
                    } else if (id == g_done) {
                        pr = done_cmd(s, ctx, expected_type);
                        if (pr)
                            st = status::Done;
                    } else if (id == g_abort) {
                            next();
                            st = status::Abort;
                    } else {
                        tactic_cmd(stack, s);
                    }
                    break;
                case scanner::token::ScriptBlock:
                    tactic_cmd(stack, s);
                    break;
                case scanner::token::CommandId:
                    st = status::Abort;
                    break;
                    default:
                        next();
                        throw tactic_cmd_error("invalid tactic command, identifier expected", p, s);
                }
            },
            [&]() {
                // Keep consuming tokens until we find a Command or End-of-file or Tactic command
                show_tactic_prompt();
                while (curr() != scanner::token::CommandId && curr() != scanner::token::Eof &&
                       curr() != scanner::token::Period && !curr_is_tactic_cmd())
                    next();
                if (curr_is_period())
                    next();
            });
    }
    switch (st) {
    case status::Done:  return *pr;
    case status::Eof:   throw tactic_cmd_error("invalid tactic command, unexpected end of file", pos(), s);
    case status::Abort: throw tactic_cmd_error("failed to prove theorem, proof has been aborted", pos(), s);
    default: lean_unreachable(); // LCOV_EXCL_LINE
    }
}

/**
   \brief Return a 'hint' tactic (if it exists) for the given metavariable.
   If the metavariable is not associated with any hint, then return the
   null tactic. The method also returns the position of the hint.
*/
std::pair<optional<tactic>, pos_info> parser_imp::get_tactic_for(expr const & mvar) {
    expr placeholder = m_elaborator.get_original(mvar);
    auto it = m_tactic_hints.find(placeholder);
    if (it != m_tactic_hints.end()) {
        return mk_pair(some_tactic(it->second), pos_of(placeholder, pos()));
    } else {
        return mk_pair(none_tactic(), pos_of(placeholder, pos()));
    }
}

std::pair<expr, context> parser_imp::get_metavar_ctx_and_type(expr const & mvar, metavar_env const & menv) {
    expr mvar_type = menv->instantiate_metavars(menv->get_type(mvar));
    buffer<context_entry> new_entries;
    for (auto e : menv->get_context(mvar)) {
        optional<expr> d = e.get_domain();
        optional<expr> b = e.get_body();
        if (d) d = menv->instantiate_metavars(*d);
        if (b) b = menv->instantiate_metavars(*b);
        if (d)
            new_entries.emplace_back(e.get_name(), *d, b);
        else
            new_entries.emplace_back(e.get_name(), d, *b);
    }
    context mvar_ctx(new_entries.size(), new_entries.data());
    return mk_pair(mvar_type, mvar_ctx);
}


/**
   \brief Try to fill the 'holes' in \c val using tactics.
   The metavar_env \c menv contains the definition of the metavariables occurring in \c val.

   If a 'hole' is associated with a "hint tactic" ('show-by' and 'by' constructs),
   then this will be the tactic used to "fill" the hole. Otherwise,
   a tactic command sequence is expected in the input stream being parsed.
*/
expr parser_imp::apply_tactics(expr const & val, metavar_env & menv) {
    buffer<expr> mvars;
    for_each(val, [&](expr const & e, unsigned) {
            if (is_metavar(e)) {
                expr m = e;
                if (has_local_context(m))
                    m = mk_metavar(metavar_name(m));
                if (std::find(mvars.begin(), mvars.end(), m) == mvars.end())
                    mvars.push_back(m);
            }
            return true;
        });
    std::sort(mvars.begin(), mvars.end(), [](expr const & e1, expr const & e2) { return is_lt(e1, e2, false); });
    for (auto mvar : mvars) {
        auto p = get_metavar_ctx_and_type(mvar, menv);
        expr mvar_type   = p.first;
        context mvar_ctx = p.second;
        if (has_metavar(mvar_type))
            throw unsolved_metavar_exception(sstream() << "failed to synthesize metavars, type of " << metavar_name(mvar) << " still contains metavariables", val);
        try {
            proof_state s = to_proof_state(m_env, mvar_ctx, mvar_type);
            std::pair<optional<tactic>, pos_info> hint_and_pos = get_tactic_for(mvar);
            if (hint_and_pos.first) {
                // metavariable has an associated tactic hint
                s = apply_tactic(s, *(hint_and_pos.first), hint_and_pos.second).first;
                menv->assign(mvar, mk_proof_for(s, hint_and_pos.second, mvar_ctx, mvar_type));
            } else {
                if (curr_is_period()) {
                    display_proof_state_if_interactive(s);
                    show_tactic_prompt();
                    next();
                }
                expr mvar_val = parse_tactic_cmds(s, mvar_ctx, mvar_type);
                menv->assign(mvar, mvar_val);
            }
        } catch (type_is_not_proposition_exception &) {
            throw unsolved_metavar_exception(sstream() << "failed to synthesize metavar " << metavar_name(mvar) << ", it could not be synthesized by type inference and its type is not a proposition",
                                             val);
        }
    }
    return menv->instantiate_metavars(val);
}
}
