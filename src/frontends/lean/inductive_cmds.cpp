/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Daniel Selsam, Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/sstream.h"
#include "util/name_map.h"
#include "util/fresh_name.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "library/scoped_ext.h"
#include "library/locals.h"
#include "library/attribute_manager.h"
#include "library/deep_copy.h"
#include "library/placeholder.h"
#include "library/aliases.h"
#include "library/protected.h"
#include "library/explicit.h"
#include "library/reducible.h"
#include "library/class.h"
#include "library/trace.h"
#include "library/type_context.h"
#include "library/documentation.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/inductive_compiler/add_decl.h"
#include "library/tactic/tactic_evaluator.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/util.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/type_util.h"
#include "frontends/lean/inductive_cmds.h"

namespace lean {

static level mk_succn(level const & l, unsigned offset) {
    level result = l;
    for (unsigned i = 0; i < offset; ++i)
        result = mk_succ(result);
    return result;
}

static void convert_params_to_kernel(elaborator & elab, buffer<expr> const & lctx_params, buffer<expr> & kernel_params) {
    for (unsigned i = 0; i < lctx_params.size(); ++i) {
        expr new_type = replace_locals(elab.infer_type(lctx_params[i]), i, lctx_params.data(), kernel_params.data());
        kernel_params.push_back(update_mlocal(lctx_params[i], new_type));
    }
}

static void replace_params(buffer<expr> const & params, buffer<expr> const & new_params, buffer<expr> const & inds, buffer<expr> const & new_inds,
                           buffer<expr> const & intro_rules, buffer<expr> & new_intro_rules) {
    for (expr const & ir : intro_rules) {
        expr new_type = replace_locals(mlocal_type(ir), params, new_params);
        new_type = replace_locals(new_type, inds, new_inds);
        new_intro_rules.push_back(update_mlocal(ir, new_type));
    }
}

static level subtract_from_max_core(level const & l, unsigned offset) {
    if (is_max(l)) {
        return mk_max(subtract_from_max_core(max_lhs(l), offset), subtract_from_max_core(max_rhs(l), offset));
    } else {
        auto lvl_offset = to_offset(l);
        if (lvl_offset.second < offset)
            return lvl_offset.first;
        else
            return mk_succn(lvl_offset.first, lvl_offset.second - offset);
    }
}

static level subtract_from_max(level const & l, unsigned offset) {
    return normalize(subtract_from_max_core(l, offset));
}

class inductive_cmd_fn {
    parser &                        m_p;
    environment                     m_env;
    cmd_meta                        m_meta_info;
    buffer<decl_attributes>         m_mut_attrs;
    type_context_old                    m_ctx;
    buffer<name>                    m_lp_names;
    pos_info                        m_pos;
    name_map<implicit_infer_kind>   m_implicit_infer_map;
    bool                            m_explicit_levels; // true if the user is providing explicit universe levels
    level                           m_u_meta;
    level                           m_u_param;
    unsigned                        m_u_param_offset;

    bool                            m_infer_result_universe{false};

    [[ noreturn ]] void throw_error(char const * error_msg) const { throw parser_error(error_msg, m_pos); }
    [[ noreturn ]] void throw_error(sstream const & strm) const { throw parser_error(strm, m_pos); }

    implicit_infer_kind get_implicit_infer_kind(name const & n) {
        if (auto it = m_implicit_infer_map.find(n))
            return *it;
        else
            return implicit_infer_kind::Implicit;
    }

    name mk_rec_name(name const & n) {
        return ::lean::inductive::get_elim_name(n);
    }

    /** \brief Return true if eliminator/recursor can eliminate into any universe */
    bool has_general_eliminator(name const & d_name) {
        declaration d = m_env.get(d_name);
        declaration r = m_env.get(mk_rec_name(d_name));
        return d.get_num_univ_params() != r.get_num_univ_params();
    }

    void remove_non_parameters(buffer<expr> & params) {
        unsigned j = 0;
        for (unsigned i = 0; i < params.size(); i++) {
            expr const & param = params[i];
            if (m_p.is_local_decl_user_name(param) &&
                !m_p.is_local_variable_user_name(mlocal_pp_name(param))) {
                expr const * klocal = m_p.get_local(mlocal_pp_name(param));
                lean_assert(klocal);
                params[j] = *klocal;
                j++;
            }
        }
        params.shrink(j);
    }

    void collect_univ_params_ignoring_locals_core(level const & l, name_set & r) {
        for_each(l, [&](level const & l) {
                if (!has_param(l))
                    return false;
                if (is_param(l) && !is_placeholder(l))
                    r.insert(param_id(l));
                return true;
            });
    }

    name_set collect_univ_params_ignoring_locals(expr const & e, name_set const & ls) {
        if (!has_param_univ(e)) {
            return ls;
        } else {
            name_set r = ls;
            for_each(e, [&](expr const & e, unsigned) {
                    if (!has_param_univ(e)) {
                        return false;
                    } else if (is_sort(e)) {
                        collect_univ_params_core(sort_level(e), r);
                    } else if (is_constant(e)) {
                        for (auto const & l : const_levels(e))
                            collect_univ_params_core(l, r);
                    } else if (is_local(e)) {
                        return false;
                    }
                    return true;
                });
            return r;
        }
    }

    bool has_explicit_level(buffer<buffer<expr> > const & intro_rules) {
        for (buffer<expr> const & irs : intro_rules) {
            for (expr const & ir : irs) {
                name_set ls = collect_univ_params_ignoring_locals(mlocal_type(ir), name_set());
                if (!ls.empty()) {
                    lean_trace(name({"inductive", "lp_names"}), tout() << "explicit universe in '" << mlocal_name(ir) << "': " << mlocal_type(ir) << "\n";);
                    return true;
                }
            }
        }
        return false;
    }

    /** \brief Add aliases for the inductive datatype, introduction and elimination rules */
    void add_aliases(buffer<expr> const & params, buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules) {
        buffer<expr> params_only(params);
        remove_non_parameters(params_only);
        // Create aliases/local refs
        levels ctx_levels = collect_local_nonvar_levels(m_p, to_list(m_lp_names));
        for (expr const & ind : inds) {
            name d_name = mlocal_name(ind);
            name d_short_name(d_name.get_string());
            m_env = add_alias(m_p, m_env, false, d_name, ctx_levels, params_only);
            name rec_name = mk_rec_name(d_name);
            levels rec_ctx_levels = ctx_levels;
            if (ctx_levels && has_general_eliminator(d_name))
                rec_ctx_levels = levels(mk_level_placeholder(), rec_ctx_levels);
            m_env = add_alias(m_p, m_env, true, rec_name, rec_ctx_levels, params_only);
            m_env = add_protected(m_env, rec_name);
        }
        for (buffer<expr> const & irs : intro_rules) {
            for (expr const & ir : irs) {
                name ir_name = mlocal_name(ir);
                m_env = add_alias(m_p, m_env, true, ir_name, ctx_levels, params_only);
            }
        }
    }

    level replace_u(level const & l, level const & rlvl) {
        return replace(l, [&](level const & l) {
                if (l == m_u_param) return some_level(rlvl);
                else return none_level();
            });
    }

    expr replace_u(expr const & type, level const & rlvl) {
        return replace(type, [&](expr const & e) {
                if (is_sort(e)) {
                    return some_expr(update_sort(e, replace_u(sort_level(e), rlvl)));
                } else if (is_constant(e)) {
                    return some_expr(update_constant(e, map(const_levels(e),
                                                            [&](level const & l) { return replace_u(l, rlvl); })));
                } else {
                    return none_expr();
                }
            });
    }

    /** \brief Create a local constant based on the given binding */
    expr mk_local_for(expr const & b) {
        return mk_local(m_p.next_name(), binding_name(b), binding_domain(b), binding_info(b), b.get_tag());
    }

    /* \brief Add \c lvl to \c r_lvls (if it is not already there).

       If the level contains the result level, it must be a `max`, in which case we accumulate the
       other max arguments. Otherwise, we do nothing for now. If it is a nested occurrence,
       then later on we confirm that the level of the argument unifies with the resultant level.
    */
    void accumulate_level(level const & lvl, buffer<level> & r_lvls) {
        if (lvl == mk_succn(m_u_param, m_u_param_offset)) {
            return;
        } else if (occurs(m_u_param, lvl)) {
            if (is_max(lvl)) {
                accumulate_level(max_lhs(lvl), r_lvls);
                accumulate_level(max_rhs(lvl), r_lvls);
            } else {
                // We used to throw an exception here, but with nested inductive types,
                // the argument level may still unify with the inferred resultant level.
            }
        } else {
            if (std::find(r_lvls.begin(), r_lvls.end(), lvl) == r_lvls.end())
                r_lvls.push_back(lvl);
        }
    }

    /** \brief Accumulate the universe levels occurring in an introduction rule argument universe.
        In general, the argument of an introduction rule has type
                 Pi (a_1 : A_1) (a_2 : A_1[a_1]) ..., B[a_1, a_2, ...]
        The universe associated with it will be
                 imax(l_1, imax(l_2, ..., r))
        where l_1 is the unvierse of A_1, l_2 of A_2, and r of B[a_1, ..., a_n].
        The result placeholder m_u_param must only appear as r.
    */
    void accumulate_levels(level const & lvl, buffer<level> & r_lvls) {
        if (lvl == mk_succn(m_u_param, m_u_param_offset)) {
            // ignore this is the auxiliary lvl
        } else if (is_imax(lvl)) {
            level lhs = imax_lhs(lvl);
            level rhs = imax_rhs(lvl);
            accumulate_level(lhs, r_lvls);
            accumulate_levels(rhs, r_lvls);
        } else {
            accumulate_level(lvl, r_lvls);
        }
    }

    /** \brief Traverse the introduction rule type and collect the universes where arguments reside in \c r_lvls.
        This information is used to compute the resultant universe level for the inductive datatype declaration.
    */
    void accumulate_levels(expr intro_type, buffer<level> & r_lvls) {
        while (is_pi(intro_type)) {
            level l = get_level(m_ctx, binding_domain(intro_type));
            accumulate_levels(l, r_lvls);
            intro_type = instantiate(binding_body(intro_type), mk_local_for(intro_type));
        }
    }

    /** \brief Given a sequence of introduction rules (encoded as local constants), compute the resultant
        universe for the inductive datatype declaration.
    */
    level infer_resultant_universe(unsigned num_intro_rules, expr const * intro_rules) {
        lean_assert(m_infer_result_universe);
        buffer<level> r_lvls;
        for (unsigned i = 0; i < num_intro_rules; i++) {
            accumulate_levels(mlocal_type(intro_rules[i]), r_lvls);
        }
        return mk_result_level(r_lvls);
    }

    /** \brief Return the universe level of the given type, if it is not a sort, then raise an exception. */
    level get_datatype_result_level(expr d_type) {
        d_type = m_ctx.relaxed_whnf(d_type);
        type_context_old::tmp_locals locals(m_ctx);
        while (is_pi(d_type)) {
            d_type = instantiate(binding_body(d_type), locals.push_local_from_binding(d_type));
            d_type = m_ctx.relaxed_whnf(d_type);
        }
        if (!is_sort(d_type))
            throw_error(sstream() << "invalid inductive datatype, resultant type is not a sort");
        return sort_level(d_type);
    }

    /** \brief Update the result sort of the given type */
    expr update_result_sort(expr t, level const & l) {
        t = m_ctx.whnf(t);
        if (is_pi(t)) {
            return update_binding(t, binding_domain(t), update_result_sort(binding_body(t), l));
        } else if (is_sort(t)) {
            return update_sort(t, l);
        } else {
            lean_unreachable();
        }
    }

    void unify_nested_occurrences(type_context_old & ctx, expr const & ir_type, buffer<expr> const & inds, level const & resultant_level) {
        expr ty = ir_type;
        while (is_pi(ty)) {
            expr arg_ty = binding_domain(ty);
            for (expr const & ind : inds) {
                if (static_cast<bool>(find(arg_ty, [&](expr const & e, unsigned) { return is_mlocal(e) && mlocal_name(e) == mlocal_name(ind); }))) {
                    level nested_level = get_level(ctx, arg_ty);
                    lean_trace(name({"inductive", "unify"}), tout() << nested_level << " =?= " << resultant_level << "\n";);
                    if (!ctx.is_def_eq(mk_sort(nested_level), mk_sort(resultant_level))) {
                        throw exception(sstream() << "nested occurrence '" << arg_ty << "' lives in universe '" << nested_level << "' but must live in resultant universe '" << resultant_level << "'");
                    }
                }
            }
            expr local = ctx.push_local(binding_name(ty), arg_ty, binding_info(ty));
            ty = instantiate(binding_body(ty), local);
        }
    }

    void check_constant_resultant_universe(expr const & ir, level const & constant_resultant_level) {
        expr ty = mlocal_type(ir);
        unsigned ir_arg = 0;
        while (is_pi(ty)) {
            ir_arg++;
            expr arg_ty = binding_domain(ty);
            type_checker ctx(m_env);
            level arg_level = get_level(ctx, arg_ty);
            if (!(is_geq(constant_resultant_level, arg_level) || is_zero(constant_resultant_level))) {
                throw exception(sstream() << "universe level of type_of(arg #" << ir_arg << ") "
                                << "of '" << mlocal_name(ir) << "' is too big for the corresponding inductive datatype");
            }
            expr local = ctx.push_local(binding_name(ty), arg_ty, binding_info(ty));
            ty = instantiate(binding_body(ty), local);
        }
    }

    void parse_intro_rules(bool has_params, expr const & ind, buffer<expr> & intro_rules, bool prepend_ns) {
        // If the next token is not `|`, then the inductive type has no constructors
        if (m_p.curr_is_token(get_bar_tk())) {
            m_p.next();
            while (true) {
                m_pos = m_p.pos();
                name ir_name = mlocal_name(ind) + m_p.check_atomic_id_next("invalid introduction rule, atomic identifier expected");
                if (prepend_ns)
                    ir_name = get_namespace(m_env) + ir_name;
                parser::local_scope S(m_p);
                buffer<expr> params;
                implicit_infer_kind kind = implicit_infer_kind::Implicit;
                m_p.parse_optional_binders(params, kind);
                m_implicit_infer_map.insert(ir_name, kind);
                for (expr const & param : params)
                    m_p.add_local(param);
                expr ir_type;
                if (has_params || m_p.curr_is_token(get_colon_tk())) {
                    m_p.check_token_next(get_colon_tk(), "invalid introduction rule, ':' expected");
                    ir_type = m_p.parse_expr();
                } else {
                    ir_type = ind;
                }
                ir_type = Pi(params, ir_type, m_p);
                intro_rules.push_back(mk_local(ir_name, ir_type));
                lean_trace(name({"inductive", "parse"}), tout() << ir_name << " : " << ir_type << "\n";);
                if (!m_p.curr_is_token(get_bar_tk()) && !m_p.curr_is_token(get_comma_tk()))
                    break;
                m_p.next();
            }
        }
    }

    /** \brief Add a namespace for each inductive datatype */
    void add_namespaces(buffer<expr> const & inds) {
        for (expr const & ind : inds) {
            m_env = add_namespace(m_env, mlocal_name(ind));
        }
    }

    /* Apply beta and zeta reduction */
    expr normalize(expr const & e) {
        type_context_old::transparency_scope scope(m_ctx, transparency_mode::None);
        return ::lean::normalize(m_ctx, e);
    }

    void elaborate_inductive_decls(buffer<expr> const & params, buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules,
                                   buffer<expr> & new_params, buffer<expr> & new_inds, buffer<buffer<expr> > & new_intro_rules) {
        options opts = m_p.get_options();
        bool recover_from_errors = true;
        elaborator elab(m_env, opts, mlocal_pp_name(inds[0]), metavar_context(), local_context(), recover_from_errors);

        buffer<expr> params_no_inds;
        for (expr const & p : params) {
            if (!std::any_of(inds.begin(), inds.end(), [&](expr const & ind) { return mlocal_name(ind) == mlocal_name(p); }))
                params_no_inds.push_back(p);
        }

        buffer<expr> elab_params;
        elaborate_params(elab, params_no_inds, elab_params);

        convert_params_to_kernel(elab, elab_params, new_params);

        level result_level;
        bool first = true;
        for (expr const & ind : inds) {
            expr new_ind_type = mlocal_type(ind);
            if (is_placeholder(new_ind_type))
                new_ind_type = mk_sort(mk_level_placeholder());
            new_ind_type = elab.elaborate(replace_locals(new_ind_type, params_no_inds, new_params));
            new_ind_type = normalize(new_ind_type);
            level l = get_datatype_result_level(new_ind_type);
            if (is_meta(l)) {
                if (m_explicit_levels)
                    throw_error("resultant universe must be provided, when using explicit universe levels");
                new_ind_type = update_result_sort(new_ind_type, m_u_meta);
                m_infer_result_universe = true;
            }
            if (first) {
                result_level = l;
                first = false;
            } else {
                if (!is_meta(l) && result_level != l) {
                    throw_error("mutually inductive types must live in the same universe");
                }
            }
            new_inds.push_back(update_mlocal(ind, new_ind_type));
        }

        for (buffer<expr> const & irs : intro_rules) {
            new_intro_rules.emplace_back();
            replace_params(params_no_inds, new_params, inds, new_inds, irs, new_intro_rules.back());
            for (expr & new_ir : new_intro_rules.back()) {
                expr new_ir_type = elab.elaborate(mlocal_type(new_ir));
                new_ir_type      = normalize(new_ir_type);
                new_ir = update_mlocal(new_ir, new_ir_type);
                lean_trace(name({"inductive", "infer_resultant"}), tout() << "[elaborated ir]: " << mlocal_type(new_ir) << "\n";);
            }
        }

        buffer<name> implicit_lp_names;

        buffer<unsigned> offsets;
        buffer<expr> all_exprs;
        offsets.push_back(new_params.size());
        all_exprs.append(new_params);
        offsets.push_back(new_inds.size());
        all_exprs.append(new_inds);
        for (buffer<expr> & irs : new_intro_rules) {
            offsets.push_back(irs.size());
            all_exprs.append(irs);
        }

        bool u_meta_has_assignment = static_cast<bool>(elab.mctx().get_assignment(m_u_meta));
        lean_trace(name({"inductive", "infer_resultant"}), tout() << "[has assignment]: " << u_meta_has_assignment << "\n";);

        all_exprs.push_back(mk_sort(m_u_meta));
        elab.finalize(all_exprs, implicit_lp_names, true, false);
        level m_u_meta_assignment = sort_level(all_exprs.back());
        all_exprs.pop_back();

        pair<level, unsigned> m_u_meta_assignment_offset = to_offset(m_u_meta_assignment);
        bool is_shifted_param = is_param(m_u_meta_assignment_offset.first);
        bool is_constant = is_zero(m_u_meta_assignment_offset.first);

        lean_trace(name({"inductive", "infer_resultant"}), tout() << "[assignment]: " << m_u_meta_assignment << "\n";);

        if (!is_shifted_param && !is_constant) {
            // resultant level tried to unify with something that is not a constant or a shifted level parameter
            throw exception(sstream() << "resultant level unifies with complex level '" << m_u_meta_assignment << "', provide the universe levels explicitly");
        }

        lean_assert(is_shifted_param || is_constant);

        for (name const & lp_name : implicit_lp_names) {
            if (!(is_shifted_param && param_id(m_u_meta_assignment_offset.first) == lp_name))
                m_lp_names.emplace_back(lp_name);
        }

        m_u_param = m_u_meta_assignment_offset.first;
        m_u_param_offset = m_u_meta_assignment_offset.second;

        m_env = elab.env();

        new_params.clear();
        new_inds.clear();
        new_intro_rules.clear();

        if (is_constant)
            m_infer_result_universe = false;

        level resultant_level;
        level replacement_level;
        if (m_infer_result_universe) {
            level resultant_level_guess = infer_resultant_universe(all_exprs.size() - offsets[0] - offsets[1], all_exprs.data() + offsets[0] + offsets[1]);
            lean_trace(name({"inductive", "infer_resultant"}), tout() << "[resultant_level_guess]: " << resultant_level_guess << "\n";);
            replacement_level = subtract_from_max(resultant_level_guess, m_u_param_offset);
            resultant_level = mk_succn(replacement_level, m_u_param_offset);
            lean_trace(name({"inductive", "infer_resultant"}), tout() << "[resultant_level]: " << resultant_level << "\n";);
            lean_trace(name({"inductive", "infer_resultant"}), tout() << "[replacement_level]: " << replacement_level << "\n";);
            for (unsigned i = offsets[0]; i < offsets[0] + offsets[1]; ++i) {
                expr ind_type = replace_u(mlocal_type(all_exprs[i]), replacement_level);
                new_inds.push_back(update_mlocal(all_exprs[i], ind_type));
            }
        } else {
            for (unsigned i = offsets[0]; i < offsets[0] + offsets[1]; ++i) {
                new_inds.push_back(all_exprs[i]);
            }
        }

        for (unsigned i = 0; i < offsets[0]; ++i) {
            new_params.push_back(all_exprs[i]);
        }

        // We replace the inds appearing in the types of introduction rules with constants
        buffer<expr> c_inds;
        for (expr const & ind : inds) {
            c_inds.push_back(mk_app(mk_constant(mlocal_name(ind), param_names_to_levels(to_list(m_lp_names))), new_params));
        }

        unsigned offset = offsets[0] + offsets[1];
        for (unsigned i = 2; i < offsets.size(); ++i) {
            new_intro_rules.emplace_back();
            for (unsigned j = 0; j < offsets[i]; ++j) {
                expr new_ir = all_exprs[offset+j];
                if (m_infer_result_universe) {
                    new_ir = update_mlocal(new_ir, replace_u(mlocal_type(new_ir), replacement_level));
                    unify_nested_occurrences(m_ctx, mlocal_type(new_ir), inds, resultant_level);
                } else if (is_constant) {
                    unify_nested_occurrences(m_ctx, mlocal_type(new_ir), inds, m_u_meta_assignment);
                }
                new_ir = replace_locals(new_ir, offsets[1], all_exprs.data() + offsets[0], c_inds.data());
                new_intro_rules.back().push_back(new_ir);
            }
            offset += offsets[i];
        }

        if (is_constant) {
            for (unsigned ind_idx = 0; ind_idx < inds.size(); ++ind_idx) {
                for (expr const & new_ir : new_intro_rules[ind_idx]) {
                    check_constant_resultant_universe(new_ir, m_u_meta_assignment);
                }
            }
        }

        for (expr const & e : all_exprs) {
            lean_trace(name({"inductive", "finalize"}),
                       tout() << mlocal_name(e) << " (" << mlocal_pp_name(e) << ") : " << mlocal_type(e) << "\n";);
        }
    }

    expr parse_inductive(buffer<expr> & params, buffer<expr> & intro_rules) {
        parser::local_scope scope(m_p);
        m_pos = m_p.pos();

        declaration_name_scope nscope;
        expr ind = parse_single_header(m_p, nscope, m_lp_names, params);
        m_explicit_levels = !m_lp_names.empty();
        m_mut_attrs.push_back({});

        ind = mk_local(get_namespace(m_p.env()) + mlocal_name(ind), mlocal_name(ind), mlocal_type(ind), local_info(ind));

        lean_trace(name({"inductive", "parse"}),
                   tout() << mlocal_name(ind) << " : " << mlocal_type(ind) << "\n";);

        m_p.add_local(ind);
        m_p.parse_local_notation_decl();

        parse_intro_rules(!params.empty(), ind, intro_rules, false);

        buffer<expr> ind_intro_rules;
        ind_intro_rules.push_back(ind);
        ind_intro_rules.append(intro_rules);

        collect_implicit_locals(m_p, m_lp_names, params, ind_intro_rules);

        for (expr const & e : params) {
            lean_trace(name({"inductive", "params"}),
                       tout() << mlocal_name(e) << " (" << mlocal_pp_name(e) << ") : " << mlocal_type(e) << "\n";);
        }

        return ind;
    }

    void parse_mutual_inductive(buffer<expr> & params, buffer<expr> & inds, buffer<buffer<expr> > & intro_rules) {
        parser::local_scope scope(m_p);

        buffer<expr> pre_inds;
        parse_mutual_header(m_p, m_lp_names, pre_inds, params);
        m_explicit_levels = !m_lp_names.empty();
        m_p.parse_local_notation_decl();

        for (expr const & pre_ind : pre_inds) {
            m_pos = m_p.pos();
            expr ind_type; decl_attributes attrs;
            std::tie(ind_type, attrs) = parse_inner_header(m_p, mlocal_pp_name(pre_ind));
            check_attrs(attrs);
            m_mut_attrs.push_back(attrs);
            lean_trace(name({"inductive", "parse"}), tout() << mlocal_name(pre_ind) << " : " << ind_type << "\n";);
            intro_rules.emplace_back();
            parse_intro_rules(!params.empty(), pre_ind, intro_rules.back(), true);
            expr ind = mk_local(get_namespace(m_p.env()) + mlocal_name(pre_ind), ind_type);
            inds.push_back(ind);
        }

        for (buffer<expr> & irs : intro_rules) {
            for (expr & ir : irs) {
                ir = replace_locals(ir, pre_inds, inds);
            }
        }

        buffer<expr> all_inds_intro_rules;
        all_inds_intro_rules.append(inds);
        for (buffer<expr> const & irs : intro_rules)
            all_inds_intro_rules.append(irs);

        collect_implicit_locals(m_p, m_lp_names, params, all_inds_intro_rules);
    }

    void check_attrs(decl_attributes const & attrs) const {
        if (!attrs.ok_for_inductive_type())
            throw_error("only attribute [class] accepted for inductive types");
    }

    void check_modifiers() const {
        if (m_meta_info.m_modifiers.m_is_noncomputable)
            throw_error("invalid 'noncomputable' modifier for inductive type");
        if (m_meta_info.m_modifiers.m_is_private)
            throw_error("invalid 'private' modifier for inductive type");
        if (m_meta_info.m_modifiers.m_is_protected)
            throw_error("invalid 'protected' modifier for inductive type");
    }
public:
    inductive_cmd_fn(parser & p, cmd_meta const & meta):
        m_p(p), m_env(p.env()), m_meta_info(meta), m_ctx(p.env()) {
        m_u_meta = m_ctx.mk_univ_metavar_decl();
        check_attrs(m_meta_info.m_attrs);
        check_modifiers();
    }

    void post_process(buffer<expr> const & new_params, buffer<expr> const & new_inds, buffer<buffer<expr> > const & new_intro_rules) {
        add_aliases(new_params, new_inds, new_intro_rules);
        add_namespaces(new_inds);
        for (expr const & ind : new_inds) {
            /* TODO(Leo): add support for doc-strings in mutual inductive definitions.
               We are currently using the same doc string for all elements.
            */
            if (m_meta_info.m_doc_string)
                m_env = add_doc_string(m_env, mlocal_name(ind), *m_meta_info.m_doc_string);
            /* Apply attributes last so that they may access any information on the new decl */
            m_env = m_meta_info.m_attrs.apply(m_env, m_p.ios(), mlocal_name(ind));
        }
        lean_assert(new_inds.size() == m_mut_attrs.size());
        for (unsigned i = 0; i < new_inds.size(); ++i)
            m_env = m_mut_attrs[i].apply(m_env, m_p.ios(), mlocal_name(new_inds[i]));
    }

    struct parse_result {
        buffer<expr>          m_params;
        buffer<expr>          m_inds;
        buffer<buffer<expr> > m_intro_rules;
    };

    void parse(parse_result & result) {
        buffer<expr>          params;
        buffer<expr>          inds;
        buffer<buffer<expr> > intro_rules;

        if (m_meta_info.m_modifiers.m_is_mutual) {
            parse_mutual_inductive(params, inds, intro_rules);
        } else {
            intro_rules.emplace_back();
            inds.push_back(parse_inductive(params, intro_rules.back()));
        }

        if (!m_explicit_levels) {
            m_explicit_levels = has_explicit_level(intro_rules);
        }

        elaborate_inductive_decls(params, inds, intro_rules, result.m_params, result.m_inds, result.m_intro_rules);
    }

    environment inductive_cmd() {
        parse_result r;
        parse(r);
        m_env = add_inductive_declaration(m_p.env(), m_p.get_options(), m_implicit_infer_map, m_lp_names, r.m_params,
                                          r.m_inds, r.m_intro_rules, !m_meta_info.m_modifiers.m_is_meta);
        post_process(r.m_params, r.m_inds, r.m_intro_rules);
        return m_env;
    }

    inductive_decl parse_and_elaborate() {
        parse_result r;
        parse(r);
        buffer<single_inductive_decl> decls;
        for (unsigned i = 0; i < r.m_inds.size(); i++) {
            decls.push_back({m_mut_attrs[i], r.m_inds[i], r.m_intro_rules[i]});
        }
        return { m_lp_names, r.m_params, decls };
    }
};

inductive_decl parse_inductive_decl(parser & p, cmd_meta const & meta) {
    auto pos = p.pos();
    module::scope_pos_info scope_pos(pos);
    return inductive_cmd_fn(p, meta).parse_and_elaborate();
}

environment inductive_cmd(parser & p, cmd_meta const & meta) {
    p.next();
    auto pos = p.pos();
    module::scope_pos_info scope_pos(pos);
    return inductive_cmd_fn(p, meta).inductive_cmd();
}

void register_inductive_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("inductive", "declare an inductive datatype", inductive_cmd, false));
}

void initialize_inductive_cmds() {
    register_trace_class("inductive");
    register_trace_class(name({"inductive", "parse"}));
    register_trace_class(name({"inductive", "elab"}));
    register_trace_class(name({"inductive", "params"}));
    register_trace_class(name({"inductive", "new_params"}));
    register_trace_class(name({"inductive", "finalize"}));
    register_trace_class(name({"inductive", "lp_names"}));
    register_trace_class(name({"inductive", "infer_resultant"}));
    register_trace_class(name({"inductive", "unify"}));
}

void finalize_inductive_cmds() {
}
}
