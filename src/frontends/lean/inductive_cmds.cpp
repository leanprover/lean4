/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Daniel Selsam, Leonardo de Moura
*/
#include <algorithm>
#include <library/attribute_manager.h>
#include "util/sstream.h"
#include "util/name_map.h"
#include "util/fresh_name.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "library/scoped_ext.h"
#include "library/locals.h"
#include "library/deep_copy.h"
#include "library/placeholder.h"
#include "library/aliases.h"
#include "library/protected.h"
#include "library/explicit.h"
#include "library/reducible.h"
#include "library/class.h"
#include "library/trace.h"
#include "library/app_builder.h"
#include "library/type_context.h"
#include "library/inductive_compiler/add_decl.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/util.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/type_util.h"
#include "frontends/lean/inductive_cmds.h"

namespace lean {
static name * g_tmp_global_univ_name = nullptr;

static name tmp_global_univ_name() { return *g_tmp_global_univ_name; }

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

class inductive_cmd_fn {
    parser &                        m_p;
    environment                     m_env;
    decl_attributes                 m_attrs;
    bool                            m_is_trusted;
    buffer<decl_attributes>         m_mut_attrs;
    type_context                    m_ctx;
    buffer<name>                    m_lp_names;
    pos_info                        m_pos;
    name_map<implicit_infer_kind>   m_implicit_infer_map;
    bool                            m_explicit_levels; // true if the user is providing explicit universe levels
    level                           m_u; // temporary auxiliary global universe used for inferring the result
                                         // universe of an inductive datatype declaration.
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
            if (m_p.is_local_decl(param) && !m_p.is_local_variable(param)) {
                // TODO(dhs): need to convert to kernel local explicitly?
                expr const * klocal = m_p.get_local(local_pp_name(param));
                lean_assert(klocal);
                params[j] = *klocal;
                j++;
            }
        }
        params.shrink(j);
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
                if (l == m_u) return some_level(rlvl);
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
        return mk_local(mk_fresh_name(), binding_name(b), binding_domain(b), binding_info(b), b.get_tag());
    }

    /* \brief Add \c lvl to \c r_lvls (if it is not already there).

       If the level contains the result level, it must be a `max`, in which case we accumulate the
       other max arguments. Otherwise, we throw an exception.
    */
    void accumulate_level(level const & lvl, buffer<level> & r_lvls) {
        if (lvl == m_u) {
            return;
        } else if (occurs(m_u, lvl)) {
            if (is_max(lvl)) {
                accumulate_level(max_lhs(lvl), r_lvls);
                accumulate_level(max_rhs(lvl), r_lvls);
            } else {
                throw exception("failed to infer inductive datatype resultant universe, "
                                "provide the universe levels explicitly");
            }
        } else {
            if (std::find(r_lvls.begin(), r_lvls.end(), lvl) == r_lvls.end())
                r_lvls.push_back(lvl);
        }
    }

    /** \bried Accumulate the universe levels occurring in an introduction rule argument universe.
        In general, the argument of an introduction rule has type
                 Pi (a_1 : A_1) (a_2 : A_1[a_1]) ..., B[a_1, a_2, ...]
        The universe associated with it will be
                 imax(l_1, imax(l_2, ..., r))
        where l_1 is the unvierse of A_1, l_2 of A_2, and r of B[a_1, ..., a_n].
        The result placeholder m_u must only appear as r.
    */
    void accumulate_levels(level const & lvl, buffer<level> & r_lvls) {
        if (lvl == m_u) {
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
        type_context::tmp_locals locals(m_ctx);
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

    void parse_intro_rules(bool has_params, expr const & ind, buffer<expr> & intro_rules, bool prepend_ns) {
        // If the next token is not `|`, then the inductive type has no constructors
        if (m_p.curr_is_token(get_bar_tk())) {
            m_p.next();
            while (true) {
                m_pos = m_p.pos();
                name ir_name = mlocal_name(ind) + m_p.check_decl_id_next("invalid introduction rule, identifier expected");
                if (prepend_ns)
                    ir_name = get_namespace(m_env) + ir_name;
                m_implicit_infer_map.insert(ir_name, parse_implicit_infer_modifier(m_p));
                expr ir_type;
                if (has_params || m_p.curr_is_token(get_colon_tk())) {
                    m_p.check_token_next(get_colon_tk(), "invalid introduction rule, ':' expected");
                    ir_type = m_p.parse_expr();
                } else {
                    ir_type = ind;
                }
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

    void elaborate_inductive_decls(buffer<expr> const & params, buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules,
                                   buffer<expr> & new_params, buffer<expr> & new_inds, buffer<buffer<expr> > & new_intro_rules) {
        options opts = m_p.get_options();
        elaborator elab(m_env, opts, metavar_context(), local_context());

        buffer<expr> params_no_inds;
        for (expr const & p : params) {
            if (std::find(inds.begin(), inds.end(), p) == inds.end())
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
            level l = get_datatype_result_level(new_ind_type);
            if (is_placeholder(l)) {
                if (m_explicit_levels)
                    throw_error("resultant universe must be provided, when using explicit universe levels");
                new_ind_type = update_result_sort(new_ind_type, m_u);
                m_infer_result_universe = true;
            }
            if (first) {
                result_level = l;
                first = false;
            } else {
                if (!is_placeholder(l) && result_level != l) {
                    throw_error("mutually inductive types must live in the same universe");
                }
            }
            new_inds.push_back(update_mlocal(ind, elab.elaborate(replace_locals(new_ind_type, params_no_inds, new_params))));
        }

        for (buffer<expr> const & irs : intro_rules) {
            new_intro_rules.emplace_back();
            replace_params(params_no_inds, new_params, inds, new_inds, irs, new_intro_rules.back());
            for (expr & new_ir : new_intro_rules.back())
                new_ir = update_mlocal(new_ir, elab.elaborate(mlocal_type(new_ir)));
        }

        buffer<name> implicit_lp_names;

        // TODO(dhs): this is a crazy (temporary) hack around the rigid elaborator API
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

        elab.finalize(all_exprs, implicit_lp_names, true, false);
        m_env = elab.env();
        m_lp_names.append(implicit_lp_names);

        new_params.clear();
        new_inds.clear();
        new_intro_rules.clear();

        // compute resultant level
        level resultant_level;
        if (m_infer_result_universe) {
            resultant_level = infer_resultant_universe(all_exprs.size() - offsets[0] - offsets[1], all_exprs.data() + offsets[0] + offsets[1]);
            for (unsigned i = offsets[0]; i < offsets[0] + offsets[1]; ++i) {
                expr ind_type = replace_u(mlocal_type(all_exprs[i]), resultant_level);
                new_inds.push_back(update_mlocal(all_exprs[i], ind_type));
            }
        } else {
            for (unsigned i = offsets[0]; i < offsets[0] + offsets[1]; ++i) {
                new_inds.push_back(all_exprs[i]);
            }
        }

        for (unsigned i = 0; i < offsets[0]; ++i) {
            if (m_infer_result_universe)
                new_params.push_back(replace_u(all_exprs[i], resultant_level));
            else
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
                expr new_ir = replace_locals(all_exprs[offset+j], offsets[1], all_exprs.data() + offsets[0], c_inds.data());
                if (m_infer_result_universe)
                    new_ir = update_mlocal(new_ir, replace_u(mlocal_type(new_ir), resultant_level));
                new_intro_rules.back().push_back(new_ir);
            }
            offset += offsets[i];
        }

        for (expr const & e : all_exprs) {
            lean_trace(name({"inductive", "finalize"}),
                       tout() << mlocal_name(e) << " (" << local_pp_name(e) << ") : " << mlocal_type(e) << "\n";);
        }
    }

    expr parse_inductive(buffer<expr> & params, buffer<expr> & intro_rules) {
        parser::local_scope scope(m_p);
        m_pos = m_p.pos();

        m_attrs.parse(m_p);
        check_attrs(m_attrs);

        expr ind = parse_single_header(m_p, m_lp_names, params);
        m_explicit_levels = !m_lp_names.empty();

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
                       tout() << mlocal_name(e) << " (" << local_pp_name(e) << ") : " << mlocal_type(e) << "\n";);
        }

        return ind;
    }

    void parse_mutual_inductive(buffer<expr> & params, buffer<expr> & inds, buffer<buffer<expr> > & intro_rules) {
        parser::local_scope scope(m_p);

        m_attrs.parse(m_p);
        check_attrs(m_attrs);

        buffer<expr> pre_inds;
        parse_mutual_header(m_p, m_lp_names, pre_inds, params);
        m_explicit_levels = !m_lp_names.empty();
        m_p.parse_local_notation_decl();

        for (expr const & pre_ind : pre_inds) {
            m_pos = m_p.pos();
            expr ind_type; decl_attributes attrs;
            std::tie(ind_type, attrs) = parse_inner_header(m_p, local_pp_name(pre_ind));
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
public:
    inductive_cmd_fn(parser & p, decl_attributes const & attrs, bool is_trusted):
        m_p(p), m_env(p.env()), m_attrs(attrs),
        m_is_trusted(is_trusted), m_ctx(p.env()) {
        m_env = m_env.add_universe(tmp_global_univ_name());
        m_u = mk_global_univ(tmp_global_univ_name());
        check_attrs(m_attrs);
    }

    void post_process(buffer<expr> const & new_params, buffer<expr> const & new_inds, buffer<buffer<expr> > const & new_intro_rules) {
        add_aliases(new_params, new_inds, new_intro_rules);
        add_namespaces(new_inds);
        for (expr const & ind : new_inds)
            m_env = m_attrs.apply(m_env, m_p.ios(), mlocal_name(ind));
        if (!m_mut_attrs.empty()) {
            lean_assert(new_inds.size() == m_mut_attrs.size());
            for (unsigned i = 0; i < new_inds.size(); ++i)
                m_env = m_mut_attrs[i].apply(m_env, m_p.ios(), mlocal_name(new_inds[i]));
        }
    }

    environment shared_inductive_cmd(buffer<expr> const & params, buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules) {
        buffer<expr> new_params;
        buffer<expr> new_inds;
        buffer<buffer<expr> > new_intro_rules;
        elaborate_inductive_decls(params, inds, intro_rules, new_params, new_inds, new_intro_rules);
        m_env = add_inductive_declaration(m_p.env(), m_p.get_options(), m_implicit_infer_map, m_lp_names, new_params,
                                          new_inds, new_intro_rules, m_is_trusted);
        post_process(new_params, new_inds, new_intro_rules);
        return m_env;
    }

    environment inductive_cmd() {
        buffer<expr> params;
        buffer<expr> inds;
        buffer<buffer<expr> > intro_rules;
        intro_rules.emplace_back();
        inds.push_back(parse_inductive(params, intro_rules.back()));
        return shared_inductive_cmd(params, inds, intro_rules);
    }

    environment mutual_inductive_cmd() {
        buffer<expr> params;
        buffer<expr> inds;
        buffer<buffer<expr> > intro_rules;
        parse_mutual_inductive(params, inds, intro_rules);
        return shared_inductive_cmd(params, inds, intro_rules);
    }
};

environment inductive_cmd_ex(parser & p, decl_attributes const & attrs, bool is_meta) {
    p.next();
    return inductive_cmd_fn(p, attrs, !is_meta).inductive_cmd();
}

environment mutual_inductive_cmd_ex(parser & p, decl_attributes const & attrs, bool is_meta) {
    p.next();
    return inductive_cmd_fn(p, attrs, !is_meta).mutual_inductive_cmd();
}

environment inductive_cmd(parser & p) {
    return inductive_cmd_ex(p, {}, false);
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

    g_tmp_global_univ_name = new name(mk_tagged_fresh_name("_inductive_result_level"));
}

void finalize_inductive_cmds() {
    delete g_tmp_global_univ_name;
}
}
