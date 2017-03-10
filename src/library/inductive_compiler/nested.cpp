/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
#include <vector>
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/find_fn.h"
#include "kernel/expr.h"
#include "kernel/replace_fn.h"
#include "util/sexpr/options.h"
#include "util/sexpr/option_declarations.h"
#include "util/list_fn.h"
#include "util/fresh_name.h"
#include "util/name_hash_map.h"
#include "library/locals.h"
#include "library/app_builder.h"
#include "library/constants.h"
#include "library/class.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/type_context.h"
#include "library/inverse.h"
#include "library/util.h"
#include "library/protected.h"
#include "library/attribute_manager.h"
#include "library/pattern_attribute.h"
#include "library/constructions/injective.h"
#include "library/tactic/simp_lemmas.h"
#include "library/constructions/has_sizeof.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/inductive_compiler/compiler.h"
#include "library/inductive_compiler/basic.h"
#include "library/inductive_compiler/nested.h"
#include "library/inductive_compiler/util.h"
#include "library/tactic/induction_tactic.h"
#include "library/tactic/subst_tactic.h"
#include "library/tactic/simp_result.h"
#include "library/tactic/simplify.h"
#include "library/tactic/eqn_lemmas.h"

/**
Notes:

1. Delta-reduction.

   The design may need to be updated in the future, especially if the global delta-reduction strategy is changed.
   Here are the important requirements:
   a) All ginductive decls not currently being defined must be unfolded in [whnf], so that all nested occurrences are
      inside BASIC inductive types.
   b) All ginductive decls including the ones currently being defined need to be unfolded in [is_def_eq],
      specifically in the simplifier. It is very difficult to maintain the invariant that only
      one version of each ginductive type ever appears and not worth the trouble.
   c) The "mimic" inductive type at this level must not be unfolded, specically when building the primitive-unpack.
      A different strategy is to temporarily mark it as not reducible during the primitive_unpack processing.
      We continue to use [safe_whnf] everywhere for now because we want to throw an exception if a non-basic ginductive type
      is found that is not reducible.
   d) [sizeof] cannot be unfolded during [is_def_eq] inside the simplifier, or else unification can result in partially-unfolded
      terms that mess up the invariants. This problem may go away once [is_def_eq] uses rfl lemmas.

2. Performance

   There is a known performance problem here: the indexing datastructures we currently use with the simplifier are based
   only on the head-symbol, so simplifying with the [sizeof] simp-set scales with the number of [sizeof] simp lemmas,
   which scales with the number of introduction rules of any inductive type. Although we could implement special-case
   workarounds in this module, we instead will try to address the root of the problem in the future.
 */

namespace lean {

static name * g_nest_prefix = nullptr;

static expr mk_local_for(expr const & b) { return mk_local(mk_fresh_name(), binding_name(b), binding_domain(b), binding_info(b)); }
static expr mk_local_for(expr const & b, name const & n) { return mk_local(mk_fresh_name(), n, binding_domain(b), binding_info(b)); }
static expr mk_local_pp(name const & n, expr const & ty) { return mk_local(mk_fresh_name(), n, ty, binder_info()); }

class add_nested_inductive_decl_fn {
    environment                   m_env;
    options                       m_opts;
    name_map<implicit_infer_kind> m_implicit_infer_map;
    // Note(dhs): m_nested_decl is morally const, but we make it non-const to passing around sizeof_lemmas
    ginductive_decl &             m_nested_decl;
    bool                          m_is_trusted;
    ginductive_decl               m_inner_decl;

    type_context                  m_tctx;

    expr                          m_nested_occ;

    expr                          m_replacement;
    name get_replacement_name() { return const_name(get_app_fn(m_replacement)); }

    expr                          m_primitive_pack;
    expr                          m_primitive_unpack;

    bool                          m_elim_to_type;
    bool                          m_prove_inj;

    buffer<buffer<buffer<optional<unsigned> > > > m_pack_arity; // [ind_idx][ir_idx][ir_arg_idx]

    // For the pack_ir_arg recursion
    bool                          m_in_define_nested_irs{false};
    unsigned                      m_curr_nest_idx{0};
    simp_lemmas                   m_lemmas;
    simp_lemmas                   m_inj_lemmas;

    unsigned get_curr_ind_idx() { lean_assert(m_in_define_nested_irs); return m_pack_arity.size() - 1; }
    unsigned get_curr_ir_idx() { lean_assert(m_in_define_nested_irs); return m_pack_arity[get_curr_ind_idx()].size() - 1; }
    unsigned get_curr_ir_arg_idx() { lean_assert(m_in_define_nested_irs); return m_pack_arity[get_curr_ind_idx()][get_curr_ir_idx()].size(); }

    // For sizeof
    local_context                 m_synth_lctx;
    buffer<expr>                  m_param_insts;

    // For naming
    enum class fn_layer { PI, NESTED, PRIMITIVE };
    enum class fn_type { PACK, UNPACK, PACK_UNPACK, UNPACK_PACK, SIZEOF_PACK };

    struct spec_lemma {
        fn_layer     m_fn_layer;
        fn_type      m_fn_type;
        name         m_ir_name;
        buffer<expr> m_to_abstract;
        expr         m_lhs;
        expr         m_rhs;

        spec_lemma(fn_layer const & layer, fn_type const & type, name const & ir_name, buffer<expr> const & to_abstract, expr const & lhs, expr const & rhs):
            m_fn_layer(layer), m_fn_type(type), m_ir_name(ir_name), m_to_abstract(to_abstract), m_lhs(lhs), m_rhs(rhs) {}
    };

    name to_name(fn_layer l) {
        switch (l) {
        case fn_layer::PI: return "pi";
        case fn_layer::NESTED: return "nested";
        case fn_layer::PRIMITIVE: return "primitive";
        }
        lean_unreachable();
    }

    name to_name(fn_type t) {
        switch (t) {
        case fn_type::PACK: return "pack";
        case fn_type::UNPACK: return "unpack";
        case fn_type::PACK_UNPACK: return "pack_unpack";
        case fn_type::UNPACK_PACK: return "unpack_pack";
        case fn_type::SIZEOF_PACK: return "sizeof_pack";
        }
        lean_unreachable();
    }

    name rcons(name const & n, unsigned i) { return n.append_after(("_" + std::to_string(i)).c_str()); }

    name append_with_ir_arg(name const & n) { return append_with_ir_arg(n, get_curr_ir_idx(), get_curr_ir_arg_idx()); }
    name append_with_ir_arg(name const & n, unsigned ir_idx, unsigned ir_arg_idx) { return rcons(rcons(n, ir_idx), ir_arg_idx); }

    name append_with_nest_idx(name const & n, unsigned nest_idx) { return rcons(n, nest_idx); }

    name mk_pi_name(fn_type t, unsigned ind_idx, unsigned ir_idx, unsigned ir_arg_idx) {
        return append_with_ir_arg(mlocal_name(m_nested_decl.get_ind(ind_idx)) + to_name(t), ir_idx, ir_arg_idx);
    }
    name mk_pi_name(fn_type t) { return mk_pi_name(t, get_curr_ind_idx(), get_curr_ir_idx(), get_curr_ir_arg_idx()); }
    name mk_nested_name(fn_type t, unsigned nest_idx) {
        return append_with_nest_idx(append_with_ir_arg(mlocal_name(m_nested_decl.get_ind(get_curr_ind_idx())) + to_name(fn_layer::NESTED) + to_name(t)), nest_idx);
    }
    name mk_primitive_name(fn_type t) { return mlocal_name(m_nested_decl.get_ind(0)) + to_name(fn_layer::PRIMITIVE) + to_name(t); }

    name nest(name const & n) {
        name prefix = n;
        while (!prefix.is_atomic()) prefix = prefix.get_prefix();

        lean_assert(!prefix.is_anonymous());
        lean_assert(prefix.is_string());

        std::string s1 = prefix.to_string();
        std::string::size_type nest_prefix_len = g_nest_prefix->to_string().size();
        if (s1.length() > nest_prefix_len) {
            std::string s2 = s1;
            s2.resize(nest_prefix_len);
            // Note: the + 1 is for the '_' that `append_after` adds
            std::string rest = s1.substr(nest_prefix_len + 1);

            if (s2 == g_nest_prefix->get_string()) {
                try {
                    // <shared_depth>_<indiv_depth>
                    std::string::size_type sep = rest.find("_");
                    std::string indiv_depth = rest.substr(sep+1);
                    unsigned previous_nest_value = std::stoul(s1.substr(nest_prefix_len+1));
                    return n.replace_prefix(prefix, g_nest_prefix->append_after(m_inner_decl.get_nest_depth()).append_after(previous_nest_value + 1));
                } catch (std::exception & ex) {
                    throw exception(sstream() << "Failed to extract numeral from prefix of string: " << n << ", " << s1 << ", " << rest);
                }
            }
        }
        return g_nest_prefix->append_after(m_inner_decl.get_nest_depth()).append_after((unsigned) 1) + n;
    }

    name mk_inner_name(name const & n) {
        if (m_nested_decl.is_ind_name(n) || m_nested_decl.is_ir_name(n)) {
            return nest(n);
        } else if (!n.is_atomic()) {
            // We want the atomic introduction rule name to stay at the end, but we don't want to introduce
            // a new "nest_" in the beginning.
            return nest(n.get_prefix() + mlocal_name(m_nested_decl.get_ind(0)) + name(n.get_string()));
        } else {
            // We append the ind name at the end so that we don't put the "nest_" in the beginning
            return nest(n + mlocal_name(m_nested_decl.get_ind(0)));
        }
    }

    name mk_spec_name(name const & base, name const & ir_name) { return base + ir_name + "spec"; }

    // Helpers
    static bool is_sizeof_app(expr const & e) {
        expr fn = get_app_fn(e);
        return is_constant(fn) && const_name(fn).is_string() && const_name(fn).get_string() == std::string("sizeof");
    }

    static optional<expr> unfold_sizeof(type_context & tctx, expr const & e) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);

        // If we see a sizeof _ <inst> _, replace with the _.sizeof function
        if (args.size() == 3 && is_constant(fn) && const_name(fn) == get_sizeof_name()) {
            // Note(dhs): *.sizeof is irreducible, and *.sizeof_inst is reducible
            // Here we want to reduce only sizeof_inst to expose the basic *.sizeof application.
            type_context::transparency_scope scope(tctx, transparency_mode::Reducible);
            expr e_sizeof = app_arg(tctx.whnf(args[1]));
            if (is_sizeof_app(e_sizeof)) {
                expr new_e = mk_app(app_arg(tctx.whnf(args[1])), args[2]);
                assert_def_eq(tctx.env(), e, new_e);
                lean_trace(name({"inductive_compiler", "nested", "sizeof"}),
                           tout() << "[unfold sizeof]: " << e << " ==> " << new_e << "\n";);
                return some_expr(new_e);
            }
        }
        return none_expr();
    }

    expr safe_whnf(type_context & tctx, expr const & e) {
        expr r = tctx.whnf_head_pred(e, [&](expr const & t) {
                expr fn = get_app_fn(t);
                if (!is_constant(fn))
                    return true;
                name n = const_name(fn);
                if (!m_inner_decl.get_inds().empty() && n == mlocal_name(m_inner_decl.get_inds().back()))
                    return false;

                auto gind_kind = is_ginductive(m_env, n);
                if (gind_kind && *gind_kind != ginductive_kind::BASIC && !is_semireducible(m_env, n)) {
                    throw exception(sstream() << "simulated (i.e. mutual or nested) inductive type '" << n << "' has been set to not be semireducible, "
                                    << "and as a result it currently cannot be used inside a nested occurrence of another inductive type");
                }
                return true;
            });
        return r;
    }

    void add_inner_decl() {
        try {
            m_env = add_inner_inductive_declaration(m_env, m_opts, m_implicit_infer_map, m_inner_decl, m_is_trusted);
        } catch (exception & ex) {
            throw nested_exception(sstream() << "nested inductive type compiled to invalid inductive type", ex);
        }
        m_tctx.set_env(m_env);
    }

    void check_elim_to_type() {
        declaration d_nest = m_env.get(get_dep_recursor(m_env, const_name(get_app_fn(m_nested_occ))));
        declaration d_inner = m_env.get(get_dep_recursor(m_env, mk_inner_name(const_name(get_app_fn(m_nested_occ)))));
        bool nest_elim_to_type = d_nest.get_num_univ_params() > length(const_levels(get_app_fn(m_nested_occ)));
        bool inner_elim_to_type = d_inner.get_num_univ_params() > m_inner_decl.get_lp_names().size();
        // Note: this exception may not be needed once the kernel is updated so that all inductive types that may or may not live in Prop must
        // eliminate to Type.
        if (nest_elim_to_type != inner_elim_to_type)
            throw exception(sstream() << "invalid nested occurrence '" << m_nested_occ
                            << "', either both must eliminate to Type or both must eliminate only to Prop");

        m_elim_to_type = nest_elim_to_type;
    }

    void check_prove_inj() {
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
                m_prove_inj = static_cast<bool>(m_env.find(mk_injective_arrow_name(mlocal_name(m_inner_decl.get_intro_rule(ind_idx, ir_idx)))));
                return;
            }
        }
        m_prove_inj = false;
    }

    expr mk_pack_injective_type(name const & pack_name, optional<unsigned> pack_arity = optional<unsigned>()) {
        type_context::tmp_locals locals(m_tctx);
        buffer<expr> all_args;
        expr full_ty = m_tctx.infer(mk_constant(pack_name, m_nested_decl.get_levels()));
        expr ty = full_ty;
        expr prev_ty;

        unsigned arg_idx = 0;
        while (is_pi(ty)) {
            expr arg = locals.push_local_from_binding(ty);
            all_args.push_back(arg);
            prev_ty = ty;
            ty = m_tctx.relaxed_whnf(instantiate(binding_body(ty), arg));
            arg_idx++;
            if (static_cast<bool>(pack_arity) && arg_idx == *pack_arity) {
                break;
            }
        }
        expr arg1 = all_args.back();
        all_args.pop_back();
        expr arg2 = locals.push_local_from_binding(prev_ty);

        expr eq_lhs = mk_app(mk_app(mk_constant(pack_name, m_nested_decl.get_levels()), all_args), arg1);
        expr eq_rhs = mk_app(mk_app(mk_constant(pack_name, m_nested_decl.get_levels()), all_args), arg2);

        expr iff_lhs = mk_eq(m_tctx, eq_lhs, eq_rhs);
        expr iff_rhs = mk_eq(m_tctx, arg1, arg2);
        expr pack_inj_type = m_tctx.mk_pi(all_args, m_tctx.mk_pi(arg1, m_tctx.mk_pi(arg2, mk_iff(iff_lhs, iff_rhs))));
        lean_trace(name({"inductive_compiler", "nested", "injective"}),
                   tout() << "[pn_pack_injective_type]: " << full_ty << " ==> " << pack_inj_type << "\n";);
        return pack_inj_type;
    }

    void define_theorem(name const & n, expr const & ty, expr const & val) {
        assert_no_locals(n, ty);
        assert_no_locals(n, val);
        declaration d = mk_definition_inferring_trusted(m_env, n, to_list(m_nested_decl.get_lp_names()), ty, val, true);
        try {
            m_env = module::add(m_env, check(m_env, d));
            lean_trace(name({"inductive_compiler", "nested", "define", "success"}), tout() << n << " : " << ty << "\n";);
        } catch (exception & ex) {
            lean_trace(name({"inductive_compiler", "nested", "define", "failure"}), tout() << n << " : " << ty << " :=\n" << val << "\n";);
            m_env = module::add(m_env, check(m_env, mk_axiom(n, to_list(m_nested_decl.get_lp_names()), ty)));
        }
        m_tctx.set_env(m_env);
    }

    void define(name const & n, expr const & ty, expr const & val) {
        define(n, ty, val, to_list(m_nested_decl.get_lp_names()));
    }

    void define(name const & n, expr const & ty, expr const & val, level_param_names const & lp_names) {
        assert_no_locals(n, ty);
        assert_no_locals(n, val);
        declaration d = mk_definition_inferring_trusted(m_env, n, lp_names, ty, val, true);
        try {
            m_env = module::add(m_env, check(m_env, d));
            lean_trace(name({"inductive_compiler", "nested", "define", "success"}), tout() << n << " : " << ty << " :=\n  " << val << "\n";);
        } catch (exception & ex) {
            lean_trace(name({"inductive_compiler", "nested", "define", "failure"}), tout() << n << " : " << ty << " :=\n  " << val << "\n";);
            throw nested_exception(sstream() << "error when adding '" << n << "' to the environment", ex);
        }
        m_tctx.set_env(m_env);
    }

    bool contains_non_param_locals(expr const & e) {
        if (!has_local(e))
            return false;

        bool found_non_param_local = false;
        for_each(e, [&](expr const & e, unsigned) {
                if (found_non_param_local)
                    return false;
                if (!has_local(e))
                    return false;
                if (is_local(e) && !m_nested_decl.is_param(e)) {
                    found_non_param_local = true;
                    return false;
                }
                return true;
            });
        return found_non_param_local;
    }

    void collect_non_param_locals(expr const & e, collected_locals & ls) {
       if (!has_local(e)) return;
        for_each(e, [&](expr const & e, unsigned) {
                if (!has_local(e)) return false;
                if (is_local(e) && !m_nested_decl.is_param(e)) ls.insert(e);
                return true;
            });
    }

    void collect_non_param_locals(expr const & e, collected_locals & ls, buffer<expr> const & skip) {
       if (!has_local(e)) return;
        for_each(e, [&](expr const & e, unsigned) {
                if (!has_local(e))
                    return false;
                if (is_local(e) && !m_nested_decl.is_param(e) && !std::find(skip.begin(), skip.end(), e))
                    ls.insert(e);
                return true;
            });
    }

    void initialize_synth_lctx() {
        if (optional<declaration> opt_d_has_sizeof = m_env.find(mk_has_sizeof_name(mlocal_name(m_inner_decl.get_ind(0))))) {
            local_context lctx;
            expr ty = opt_d_has_sizeof->get_type();
            for (expr const & param : m_nested_decl.get_params()) {
                ty = instantiate(binding_body(ty), param);
            }

            while (is_pi(ty) && binding_info(ty).is_inst_implicit()) {
                expr param_inst = lctx.mk_local_decl(binding_name(ty), binding_domain(ty), binding_info(ty));
                m_param_insts.push_back(param_inst);
                ty = safe_whnf(m_tctx, instantiate(binding_body(ty), param_inst));
            }
            m_synth_lctx = lctx;
        }
    }

    ///////////////////////////////////////////
    ///// Stage 1: find nested occurrence /////
    ///////////////////////////////////////////

    bool find_nested_occ() {
        for (buffer<expr> const & irs : m_nested_decl.get_intro_rules()) {
            for (expr const & ir : irs) {
                if (find_nested_occ_in_ir_type(mlocal_type(ir)))
                    return true;
            }
        }
        return false;
    }

    bool find_nested_occ_in_ir_type(expr const & ir_type) {
        if (!m_nested_decl.has_ind_occ(ir_type))
            return false;
        expr ty = safe_whnf(m_tctx, ir_type);
        while (is_pi(ty)) {
            expr arg_type = binding_domain(ty);
            if (find_nested_occ_in_ir_arg_type(arg_type))
                return true;
            expr l = mk_local_for(ty);
            ty = safe_whnf(m_tctx, instantiate(binding_body(ty), l));
        }
        return false;
    }

    bool find_nested_occ_in_ir_arg_type(expr const & arg_ty) {
        if (!m_nested_decl.has_ind_occ(arg_ty))
            return false;

        expr ty = safe_whnf(m_tctx, arg_ty);
        while (is_pi(ty)) {
            expr l = mk_local_for(ty);
            ty = safe_whnf(m_tctx, instantiate(binding_body(ty), l));
        }

        return find_nested_occ_in_ir_arg_type_core(ty, none_expr());
    }

    bool find_nested_occ_in_ir_arg_type_core(expr const & ty, optional<expr> outer_app, unsigned num_params = 0) {
        if (!m_nested_decl.has_ind_occ(ty))
            return false;

        buffer<expr> args;
        expr fn = get_app_args(ty, args);

        if (!outer_app && m_nested_decl.is_ind(fn))
            return false;

        if (outer_app && m_nested_decl.is_ind(fn)) {
            buffer<expr> outer_params, outer_indices;
            expr outer_fn = get_app_params_indices(*outer_app, num_params, outer_params, outer_indices);

            // we found a nested occurrence
            m_nested_occ = mk_app(outer_fn, outer_params);

            if (contains_non_param_locals(m_nested_occ))
                throw exception(sstream() << "nested occurrence '" << m_nested_occ << "' contains variables that are not parameters");

            level nested_occ_result_level = get_level(m_tctx, *outer_app);
            if (!m_tctx.is_def_eq(nested_occ_result_level, m_nested_decl.get_result_level(m_env)))
                throw exception(sstream() << "nested occurrence '" << m_nested_occ
                                << "' lives in universe '" << nested_occ_result_level << "' but must live in the same universe "
                                << "as the inductive types being declared, which is '"
                                << m_nested_decl.get_result_level(m_env) << "'");

            m_replacement = m_nested_decl.mk_const_params(mk_inner_name(const_name(outer_fn)));

            lean_trace(name({"inductive_compiler", "nested", "found_occ"}),
                       tout() << m_nested_occ << "\n";);
            return true;
        }

        if (is_constant(fn) && is_ginductive(m_env, const_name(fn))) {
            unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
            for (unsigned i = 0; i < num_params; ++i) {
                if (find_nested_occ_in_ir_arg_type_core(safe_whnf(m_tctx, args[i]), some_expr(ty), num_params))
                    return true;
            }
            throw exception("inductive type being declared cannot occur as an index of another inductive type");
        }

        throw exception("inductive type being declared can only be nested inside the parameters of other inductive types");
    }

    /////////////////////////////////////////
    ///// Stage 2: construct inner decl /////
    /////////////////////////////////////////

    expr pack_constants(expr const & e) {
        return replace(e, [&](expr const & e) {
                if (m_nested_decl.is_ind(e) || m_nested_decl.is_ir(e)) {
                    lean_assert(is_constant(e));
                    return some_expr(mk_constant(mk_inner_name(const_name(e)), const_levels(e)));
                } else {
                    return none_expr();
                }
            });
    }

    expr unpack_constants(expr const & e) {
        return replace(e, [&](expr const & e) {
                if (!is_constant(e))
                    return none_expr();
                for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
                    if (const_name(e) == mlocal_name(m_inner_decl.get_ind(ind_idx)))
                        return some_expr(mk_constant(mlocal_name(m_nested_decl.get_ind(ind_idx)), const_levels(e)));
                    for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
                        if (const_name(e) == mlocal_name(m_inner_decl.get_intro_rule(ind_idx, ir_idx)))
                            return some_expr(mk_constant(mlocal_name(m_nested_decl.get_intro_rule(ind_idx, ir_idx)), const_levels(e)));
                    }
                }
                return none_expr();
            });
    }

    expr pack_nested_occs(expr const & _e) {
        // Note: cannot use replace because we need to whnf to expose the nested occurrences
        // For the same reason, we must instantiate with locals
        // Note: only looks in the places where it would be legal to find a nested occurrence
        expr e = safe_whnf(m_tctx, _e);
        switch (e.kind()) {
        case expr_kind::Sort:
        case expr_kind::Local:
        case expr_kind::Macro:
            return _e;
        case expr_kind::Lambda:
        case expr_kind::Pi:
        {
            expr new_dom = pack_nested_occs(binding_domain(e));
            expr l = mk_local_pp("x_new_dom", new_dom);
            expr new_body = abstract_local(pack_nested_occs(instantiate(binding_body(e), l)), l);
            return update_binding(e, new_dom, new_body);
        }
        case expr_kind::Constant:
        case expr_kind::App:
        {
            buffer<expr> args;
            expr fn = get_app_args(e, args);
            if (is_constant(fn) && is_ginductive(m_env, const_name(fn))) {
                unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
                expr candidate = mk_app(fn, num_params, args.data());
                if (candidate == m_nested_occ) {
                    return copy_tag(e, mk_app(m_replacement, args.size() - num_params, args.data() + num_params));
                } else {
                    // We track whether it was updated just so we return a structurally equal expression if we never pack
                    bool updated = false;
                    for (unsigned i = 0; i < num_params; ++i) {
                        expr new_arg = pack_nested_occs(args[i]);
                        if (new_arg != args[i]) {
                            args[i] = new_arg;
                            updated = true;
                        }
                    }
                    if (updated)
                        return copy_tag(e, mk_app(fn, args));
                    else
                        return _e;
                }
            }
            return _e;
        }
        case expr_kind::Var:
        case expr_kind::Meta:
        case expr_kind::Let:
            lean_unreachable();
        }
        lean_unreachable();
    }

    expr unpack_nested_occs(expr const & _e) {
        // Note: cannot use replace because we need to whnf to expose the nested occurrences
        // For the same reason, we must instantiate with locals
        // Note: only looks in the places where it would be legal to find a nested occurrence
        expr e = safe_whnf(m_tctx, _e);
        switch (e.kind()) {
        case expr_kind::Sort:
        case expr_kind::Local:
        case expr_kind::Macro:
            return _e;
        case expr_kind::Lambda:
        case expr_kind::Pi:
        {
            expr new_dom = unpack_nested_occs(binding_domain(e));
            expr l = mk_local_pp("x_new_dom", new_dom);
            expr new_body = abstract_local(unpack_nested_occs(instantiate(binding_body(e), l)), l);
            return update_binding(e, new_dom, new_body);
        }
        case expr_kind::Constant:
        case expr_kind::App:
        {
            buffer<expr> args;
            expr fn = get_app_args(e, args);
            if (is_constant(fn) && is_ginductive(m_env, const_name(fn))) {
                unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
                expr candidate = mk_app(fn, num_params, args.data());
                if (candidate == m_replacement) {
                    return copy_tag(e, mk_app(m_nested_occ, args.size() - num_params, args.data() + num_params));
                } else {
                    // We track whether it was updated so we can return a structurally equal expression if we never unpack
                    bool updated = false;
                    for (unsigned i = 0; i < num_params; ++i) {
                        expr new_arg = unpack_nested_occs(args[i]);
                        if (new_arg != args[i]) {
                            args[i] = new_arg;
                            updated = true;
                        }
                    }
                    if (updated)
                        return copy_tag(e, mk_app(fn, args));
                    else
                        return _e;
                }
            }
            return _e;
        }
        case expr_kind::Var:
        case expr_kind::Meta:
        case expr_kind::Let:
            lean_unreachable();
        }
        lean_unreachable();
    }

    expr pack_type(expr const & e) { return pack_constants(pack_nested_occs(e)); }
    expr unpack_type(expr const & e) { return unpack_constants(unpack_nested_occs(e)); }

    void construct_inner_decl() {
        unsigned offset = 0;
        // Construct inner inds for each of the nested inds
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            expr const & ind = m_nested_decl.get_ind(ind_idx);
            expr inner_ind = mk_local(mk_inner_name(mlocal_name(ind)), mlocal_type(ind));
            m_inner_decl.get_inds().push_back(inner_ind);

            lean_trace(name({"inductive_compiler", "nested", "inner", "ind"}),
                       tout() << mlocal_name(inner_ind) << " : " << mlocal_type(inner_ind) << "\n";);

            m_inner_decl.get_intro_rules().emplace_back();
            for (expr const & ir : m_nested_decl.get_intro_rules(ind_idx)) {
                offset++;
                expr inner_ir = mk_local(mk_inner_name(mlocal_name(ir)), pack_type(mlocal_type(ir)));
                m_inner_decl.get_intro_rules().back().push_back(inner_ir);

                lean_trace(name({"inductive_compiler", "nested", "inner", "ir"}),
                           tout() << mlocal_name(inner_ir) << " : " << mlocal_type(inner_ir) << "\n";);
            }
        }

        buffer<expr> nested_occ_params;
        expr nested_occ_fn = get_app_args(m_nested_occ, nested_occ_params);
        name mimic_name = const_name(nested_occ_fn);
        if (length(get_ginductive_mut_ind_names(m_env, mimic_name)) > 1)
            throw exception(sstream() << "cannot nest occurrence inside mutually inductive type '" << mimic_name << "'");

        expr c_mimic_ind = mk_app(mk_constant(mimic_name, const_levels(nested_occ_fn)), nested_occ_params);
        expr mimic_ind_type = update_result_sort(m_tctx.infer(c_mimic_ind), m_nested_decl.get_result_level(m_env));
        expr mimic_ind = mk_local(mk_inner_name(mimic_name), mimic_ind_type);
        m_inner_decl.get_inds().push_back(mimic_ind);
        m_inner_decl.get_num_indices().push_back(get_num_indices(m_env, mimic_ind));

        lean_trace(name({"inductive_compiler", "nested", "mimic", "ind"}),
                   tout() << mlocal_name(mimic_ind) << " : " << mlocal_type(mimic_ind) << "\n";);

        m_inner_decl.get_intro_rules().emplace_back();
        list<name> mimic_intro_rule_names = get_ginductive_intro_rules(m_env, mimic_name);
        for (name const & ir : mimic_intro_rule_names) {
            expr c_mimic_ir = mk_app(mk_constant(ir, const_levels(nested_occ_fn)), nested_occ_params);
            expr mimic_ir = mk_local(mk_inner_name(ir), pack_type(m_tctx.infer(c_mimic_ir)));
            m_inner_decl.get_intro_rules().back().push_back(mimic_ir);
            m_inner_decl.get_ir_offsets().emplace_back(offset);
            lean_trace(name({"inductive_compiler", "nested", "mimic", "ir"}),
                       tout() << mlocal_name(mimic_ir) << " : " << mlocal_type(mimic_ir) << "\n";);
            lean_trace(name({"inductive_compiler", "nested", "mimic", "ir", "offset"}),
                       tout() << mlocal_name(mimic_ir) << " ==> " << offset << "\n";);
        }
    }

    ///////////////////////////////////////
    ///// Stage 3: define nested inds /////
    ///////////////////////////////////////

    void define_nested_inds() {
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            expr const & ind = m_nested_decl.get_ind(ind_idx);
            expr new_ind_type = Pi(m_nested_decl.get_params(), mlocal_type(ind));
            expr new_ind_val = m_inner_decl.get_c_ind(ind_idx);

            lean_trace(name({"inductive_compiler", "nested", "nested_ind"}),
                       tout() << mlocal_name(ind) << " : " << new_ind_type << " :=\n  " << new_ind_val << "\n";);

            define(mlocal_name(ind), new_ind_type, new_ind_val);
        }
    }

    //////////////////////////////////////////////
    ///// Stage 5: define nested has_sizeofs /////
    /////////////////////////////////////////////

    expr unpack_sizeof(expr const & _e) {
        return replace(_e, [&](expr const & e) {
                for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
                    if (is_constant(e) && const_name(e) == mk_sizeof_name(mlocal_name(m_inner_decl.get_ind(ind_idx))))
                        return some_expr(mk_constant(mk_sizeof_name(mlocal_name(m_nested_decl.get_ind(ind_idx))), const_levels(e)));
                }
                return none_expr();
            });
    }

    void define_nested_has_sizeofs() {
        initialize_synth_lctx();
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            expr const & ind = m_nested_decl.get_ind(ind_idx);
            name inner_has_sizeof_name = mk_has_sizeof_name(mlocal_name(m_inner_decl.get_ind(ind_idx)));
            optional<declaration> opt_d = m_env.find(inner_has_sizeof_name);
            if (!opt_d) return;
            define(mk_has_sizeof_name(mlocal_name(ind)), unpack_constants(opt_d->get_type()), unpack_constants(opt_d->get_value()));
            name has_sizeof_name = mk_has_sizeof_name(mlocal_name(ind));
            m_env = set_reducible(m_env, has_sizeof_name, reducible_status::Reducible, true);
            m_env = add_instance(m_env, has_sizeof_name, LEAN_DEFAULT_PRIORITY, true);
            m_env = add_protected(m_env, has_sizeof_name);
            m_tctx.set_env(m_env);
        }
    }

    //////////////////////////////////////
    ///// Stage 6: define nested irs /////
    //////////////////////////////////////

    void define_nested_irs() {
        flet<bool> in_define(m_in_define_nested_irs, true);
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            lean_assert(m_pack_arity.size() == ind_idx);
            m_pack_arity.emplace_back();
            for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
                lean_assert(m_pack_arity[ind_idx].size() == ir_idx);
                m_pack_arity[ind_idx].emplace_back();
                expr const & ir = m_nested_decl.get_intro_rule(ind_idx, ir_idx);

                buffer<expr> locals;
                buffer<expr> result_args;

                expr ty = safe_whnf(m_tctx, mlocal_type(ir));
                while (is_pi(ty)) {
                    expr l = mk_local_for(ty);
                    if (optional<pair<expr, unsigned> > packed_arg_arity = pack_ir_arg(l)) {
                        m_pack_arity[ind_idx][ir_idx].push_back(optional<unsigned>(packed_arg_arity->second));
                        result_args.push_back(packed_arg_arity->first);
                    } else {
                        m_pack_arity[ind_idx][ir_idx].push_back(optional<unsigned>());
                        result_args.push_back(l);
                    }
                    locals.push_back(l);
                    ty = safe_whnf(m_tctx, instantiate(binding_body(ty), l));
                }

                expr new_ir_val  = Fun(m_nested_decl.get_params(), Fun(locals, mk_app(m_inner_decl.get_c_ir_params(ind_idx, ir_idx), result_args)));
                expr new_ir_type = Pi(m_nested_decl.get_params(), mlocal_type(ir));
                implicit_infer_kind k = get_implicit_infer_kind(m_implicit_infer_map, mlocal_name(ir));
                new_ir_type = infer_implicit_params(new_ir_type, m_nested_decl.get_params().size(), k);

                define(mlocal_name(ir), new_ir_type, new_ir_val);
                m_env = set_pattern_attribute(m_env, mlocal_name(ir));
                m_tctx.set_env(m_env);
            }
        }
    }

    optional<pair<expr, unsigned> > pack_ir_arg(expr const & ir_arg) {
        m_curr_nest_idx = 0;
        if (auto pack_fn_arity = build_pi_pack_unpack(mlocal_type(ir_arg))) {
            return optional<pair<expr, unsigned> >(mk_app(pack_fn_arity->first, ir_arg), pack_fn_arity->second);
        } else {
            return optional<pair<expr, unsigned> >();
        }
    }

    optional<pair<expr, unsigned> > build_pi_pack_unpack(expr const & arg_ty) {
        expr ty = safe_whnf(m_tctx, arg_ty);

        if (ty == pack_nested_occs(ty))
            return optional<pair<expr, unsigned> >();

        expr x_to_pack = mk_local_pp("x_to_pack", ty);
        expr x_to_unpack = mk_local_pp("x_to_unpack", pack_type(ty));

        buffer<expr> pi_args;
        while (is_pi(ty)) {
            expr l = mk_local_for(ty);
            pi_args.push_back(l);
            ty = safe_whnf(m_tctx, instantiate(binding_body(ty), l));
        }
        expr body_to_pack = mk_app(x_to_pack, pi_args);
        expr body_to_unpack = mk_app(x_to_unpack, pi_args);

        lean_assert(m_tctx.is_def_eq(m_tctx.infer(body_to_pack), ty));
        lean_assert(m_tctx.is_def_eq(m_tctx.infer(body_to_unpack), pack_type(ty)));

        lean_assert(ty != pack_nested_occs(ty));

        buffer<expr> args;
        expr fn = get_app_args(ty, args);

        lean_assert(is_constant(fn) && is_ginductive(m_env, const_name(fn)));
        unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));

        buffer<expr> params, indices;
        split_params_indices(args, num_params, params, indices);
        optional<expr_pair> nested_pack_unpack = build_nested_pack_unpack(fn, params);
        lean_assert(nested_pack_unpack);

        expr const & nested_pack_fn = nested_pack_unpack->first;
        expr const & nested_unpack_fn = nested_pack_unpack->second;

        expr pre_pi_pack = Fun(x_to_pack, Fun(pi_args, mk_app(mk_app(nested_pack_fn, indices), body_to_pack)));
        expr pre_pi_unpack = Fun(x_to_unpack, Fun(pi_args, mk_app(mk_app(nested_unpack_fn, indices), body_to_unpack)));

        collected_locals ls;
        collect_non_param_locals(pre_pi_pack, ls);
        buffer<expr> const & ldeps = ls.get_collected();

        define(mk_pi_name(fn_type::PACK), Pi(m_nested_decl.get_params(), Pi(ldeps, mk_arrow(arg_ty, pack_type(arg_ty)))), Fun(m_nested_decl.get_params(), Fun(ldeps, pre_pi_pack)));
        define(mk_pi_name(fn_type::UNPACK), Pi(m_nested_decl.get_params(), Pi(ldeps, mk_arrow(pack_type(arg_ty), arg_ty))), Fun(m_nested_decl.get_params(), Fun(ldeps, pre_pi_unpack)));

        m_env = set_reducible(m_env, mk_pi_name(fn_type::PACK), reducible_status::Irreducible, true);
        m_env = set_reducible(m_env, mk_pi_name(fn_type::UNPACK), reducible_status::Irreducible, true);

        m_nested_decl.get_packs().push_back(mk_pi_name(fn_type::PACK));
        m_nested_decl.get_unpacks().push_back(mk_pi_name(fn_type::UNPACK));

        m_tctx.set_env(m_env);

        expr pi_pack = mk_app(m_nested_decl.mk_const_params(mk_pi_name(fn_type::PACK)), ldeps);
        expr pi_unpack = mk_app(m_nested_decl.mk_const_params(mk_pi_name(fn_type::UNPACK)), ldeps);

        prove_pi_pack_unpack(pi_pack, pi_unpack, ldeps, nested_pack_fn, nested_unpack_fn, arg_ty);
        prove_pi_unpack_pack(pi_pack, pi_unpack, ldeps, nested_pack_fn, nested_unpack_fn, arg_ty);
        prove_pi_pack_sizeof(pi_pack, ldeps, nested_pack_fn, arg_ty);
        prove_pi_pack_injective(m_nested_decl.get_num_params() + ldeps.size() + 1);

        return optional<pair<expr, unsigned> >(pi_pack, m_nested_decl.get_num_params() + ldeps.size() + 1);
    }

    optional<expr_pair> build_nested_pack_unpack(expr const & fn, buffer<expr> const & params) {
        if (mk_app(fn, params) == m_nested_occ)
            return optional<expr_pair>(m_primitive_pack, m_primitive_unpack);
        if (mk_app(fn, params) == pack_nested_occs(mk_app(fn, params)))
            return optional<expr_pair>();

        unsigned nest_idx = m_curr_nest_idx++;

        lean_assert(is_ginductive(m_env, const_name(fn)));

        buffer<expr> unpacked_params, packed_params;
        for (expr const & param : params) {
            expr p = safe_whnf(m_tctx, param);
            unpacked_params.push_back(p);
            packed_params.push_back(pack_type(p));
        }

        expr start = mk_app(fn, unpacked_params);
        expr end   = mk_app(fn, packed_params);

        expr c_nested_pack = m_nested_decl.mk_const_params(mk_nested_name(fn_type::PACK, nest_idx));
        expr c_nested_unpack = m_nested_decl.mk_const_params(mk_nested_name(fn_type::UNPACK, nest_idx));

        expr remaining_type;
        {
            expr remaining_unpacked_type = safe_whnf(m_tctx, m_tctx.infer(start));
            expr remaining_packed_type = safe_whnf(m_tctx, m_tctx.infer(end));
            lean_assert(remaining_unpacked_type == remaining_packed_type);
            remaining_type = remaining_unpacked_type;
        }

        // Indices
        buffer<expr> indices;
        {
            expr ty = safe_whnf(m_tctx, remaining_type);
            while (is_pi(ty)) {
                expr l = mk_local_for(ty);
                indices.push_back(l);
                ty = safe_whnf(m_tctx, instantiate(binding_body(ty), l));
            }
        }

        // Elim levels
        list<level> elim_levels = const_levels(fn);
        {
            declaration d = m_env.get(get_dep_recursor(m_env, const_name(fn)));
            if (length(elim_levels) < d.get_num_univ_params()) {
                lean_assert(length(elim_levels) + 1 == d.get_num_univ_params());
                level unpacked_level = get_level(m_tctx, mk_app(start, indices));
                level packed_level = get_level(m_tctx, mk_app(end, indices));
                lean_assert(unpacked_level == packed_level);
                elim_levels = list<level>(unpacked_level, elim_levels);
            }
        }

        // Motive
        auto construct_C = [&](expr const & start, expr const & end) {
            expr x_ignore = mk_local_pp("x_ignore", mk_app(start, indices));
            return Fun(indices, Fun(x_ignore, mk_app(end, indices)));
        };

        expr pack_C = construct_C(start, end);
        expr unpack_C = construct_C(end, start);

        // Minor premises
        list<name> intro_rules = get_ginductive_intro_rules(m_env, const_name(fn));
        buffer<expr> pack_minor_premises, unpack_minor_premises;
        buffer<spec_lemma> spec_lemmas;
        for (name const & intro_rule : intro_rules) {
            expr c_unpacked_ir = mk_app(mk_constant(intro_rule, const_levels(fn)), unpacked_params);
            expr c_packed_ir = mk_app(mk_constant(intro_rule, const_levels(fn)), packed_params);

            expr unpacked_ir_type = safe_whnf(m_tctx, m_tctx.infer(c_unpacked_ir));
            expr packed_ir_type = safe_whnf(m_tctx, m_tctx.infer(c_packed_ir));

            // for definition
            buffer<expr> unpacked_rec_args;
            buffer<expr> unpacked_locals;
            buffer<expr> unpacked_return_args;

            buffer<expr> packed_locals;
            buffer<expr> packed_rec_args;
            buffer<expr> packed_return_args;

            // for lemmas
            buffer<expr> unpacked_lhs_args;
            buffer<expr> unpacked_rhs_args;

            buffer<expr> packed_lhs_args;
            buffer<expr> packed_rhs_args;

            while (is_pi(unpacked_ir_type) && is_pi(packed_ir_type)) {
                // In case we have a nesting with a reducible constant
                unpacked_ir_type = update_binding(unpacked_ir_type, safe_whnf(m_tctx, binding_domain(unpacked_ir_type)), binding_body(unpacked_ir_type));
                packed_ir_type = update_binding(packed_ir_type, safe_whnf(m_tctx, binding_domain(packed_ir_type)), binding_body(packed_ir_type));

                buffer<expr> unpacked_arg_args;
                expr unpacked_arg_fn = get_app_args(binding_domain(unpacked_ir_type), unpacked_arg_args);

                buffer<expr> packed_arg_args;
                expr packed_arg_fn = get_app_args(binding_domain(packed_ir_type), packed_arg_args);

                expr unpacked_l = mk_local_for(unpacked_ir_type);
                expr packed_l;

                if (unpacked_arg_args.size() >= unpacked_params.size() && mk_app(unpacked_arg_fn, unpacked_params.size(), unpacked_arg_args.data()) == start) {
                    // it is a recursive argument
                    expr unpacked_rec_arg_type = mk_app(end, unpacked_arg_args.size() - unpacked_params.size(), unpacked_arg_args.data() + unpacked_params.size());
                    expr unpacked_l_rec = mk_local_pp("x_unpacked", unpacked_rec_arg_type);
                    unpacked_rec_args.push_back(unpacked_l_rec);
                    unpacked_return_args.push_back(unpacked_l_rec);
                    unpacked_rhs_args.push_back(mk_app(mk_app(c_nested_pack, unpacked_arg_args.size() - unpacked_params.size(), unpacked_arg_args.data() + unpacked_params.size()),
                                                       unpacked_l));

                    packed_l = mk_local_for(packed_ir_type);

                    expr packed_rec_arg_type = mk_app(start, packed_arg_args.size() - packed_params.size(), packed_arg_args.data() + packed_params.size());
                    expr packed_l_rec = mk_local_pp("x_packed", packed_rec_arg_type);
                    packed_rec_args.push_back(packed_l_rec);
                    packed_return_args.push_back(packed_l_rec);
                    packed_rhs_args.push_back(mk_app(mk_app(c_nested_unpack, packed_arg_args.size() - packed_params.size(), packed_arg_args.data() + packed_params.size()),
                                                     packed_l));
                } else {
                    bool packed_arg = false;
                    if (mlocal_type(unpacked_l) != binding_domain(packed_ir_type)) {
                        lean_assert(pack_type(mlocal_type(unpacked_l)) == binding_domain(packed_ir_type));
                        lean_assert(is_constant(unpacked_arg_fn) && is_ginductive(m_env, const_name(unpacked_arg_fn)));
                        buffer<expr> unpacked_arg_params, unpacked_arg_indices;
                        split_params_indices(unpacked_arg_args, get_ginductive_num_params(m_env, const_name(unpacked_arg_fn)), unpacked_arg_params, unpacked_arg_indices);

                        auto pack_unpack_fn = build_nested_pack_unpack(unpacked_arg_fn, unpacked_arg_params);
                        if (pack_unpack_fn) {
                            lean_assert(static_cast<bool>(pack_unpack_fn));
                            unpacked_return_args.push_back(mk_app(mk_app(pack_unpack_fn->first, unpacked_arg_indices), unpacked_l));
                            unpacked_rhs_args.push_back(mk_app(mk_app(pack_unpack_fn->first, unpacked_arg_indices), unpacked_l));

                            packed_l = mk_local_for(packed_ir_type);

                            packed_return_args.push_back(mk_app(mk_app(pack_unpack_fn->second, unpacked_arg_indices), packed_l));
                            packed_rhs_args.push_back(mk_app(mk_app(pack_unpack_fn->second, unpacked_arg_indices), packed_l));
                            packed_arg = true;
                        }
                    }
                    if (!packed_arg) {
                        assert_def_eq(m_env, mlocal_type(unpacked_l), binding_domain(packed_ir_type));
                        unpacked_return_args.push_back(unpacked_l);
                        unpacked_rhs_args.push_back(unpacked_l);

                        packed_l = unpacked_l;

                        packed_return_args.push_back(packed_l);
                        packed_rhs_args.push_back(packed_l);
                    }
                }

                unpacked_locals.push_back(unpacked_l);
                unpacked_lhs_args.push_back(unpacked_l);

                packed_locals.push_back(packed_l);
                packed_lhs_args.push_back(packed_l);

                unpacked_ir_type = safe_whnf(m_tctx, instantiate(binding_body(unpacked_ir_type), unpacked_l));
                packed_ir_type = safe_whnf(m_tctx, instantiate(binding_body(packed_ir_type), packed_l));
            }

            lean_assert(!is_pi(unpacked_ir_type) && !is_pi(packed_ir_type));

            unpacked_locals.append(unpacked_rec_args);
            packed_locals.append(packed_rec_args);

            expr unpacked_minor_premise = Fun(unpacked_locals, mk_app(c_packed_ir, unpacked_return_args));
            expr packed_minor_premise = Fun(packed_locals, mk_app(c_unpacked_ir, packed_return_args));
            pack_minor_premises.push_back(unpacked_minor_premise);
            unpack_minor_premises.push_back(packed_minor_premise);

            lean_trace(name({"inductive_compiler", "nested", "pack", "nested"}), tout() << " mp := " << unpacked_minor_premise << "\n";);
            lean_trace(name({"inductive_compiler", "nested", "unpack", "nested"}), tout() << " mp := " << packed_minor_premise << "\n";);

            buffer<expr> unpacked_ir_result_indices, packed_ir_result_indices;
            get_app_indices(unpacked_ir_type, unpacked_params.size(), unpacked_ir_result_indices);
            get_app_indices(packed_ir_type, packed_params.size(), packed_ir_result_indices);

            expr unpacked_lhs = mk_app(mk_app(c_nested_pack, unpacked_ir_result_indices), mk_app(c_unpacked_ir, unpacked_lhs_args));
            expr unpacked_rhs = mk_app(c_packed_ir, unpacked_rhs_args);
            spec_lemmas.push_back(spec_lemma(fn_layer::NESTED, fn_type::PACK, intro_rule, unpacked_lhs_args, unpacked_lhs, unpacked_rhs));

            expr packed_lhs = mk_app(mk_app(c_nested_unpack, packed_ir_result_indices), mk_app(c_packed_ir, packed_lhs_args));
            expr packed_rhs = mk_app(c_unpacked_ir, packed_rhs_args);
            spec_lemmas.push_back(spec_lemma(fn_layer::NESTED, fn_type::UNPACK, mk_inner_name(intro_rule), packed_lhs_args, packed_lhs, packed_rhs));

            lean_trace(name({"inductive_compiler", "nested", "pack", "nested"}), tout() << " lemma : " << unpacked_lhs << " = " << unpacked_rhs << "\n";);
            lean_trace(name({"inductive_compiler", "nested", "unpack", "nested"}), tout() << " lemma : " << packed_lhs << " = " << packed_rhs << "\n";);
        }

        expr nested_pack_ty = Pi(m_nested_decl.get_params(), Pi(indices, mk_arrow(mk_app(start, indices), mk_app(end, indices))));
        expr nested_pack_val = Fun(m_nested_decl.get_params(),
                                      mk_app(mk_app(mk_app(mk_constant(get_dep_recursor(m_env, const_name(fn)), elim_levels),
                                                           unpacked_params), pack_C), pack_minor_premises));

        expr nested_unpack_ty = Pi(m_nested_decl.get_params(), Pi(indices, mk_arrow(mk_app(end, indices), mk_app(start, indices))));
        expr nested_unpack_val = Fun(m_nested_decl.get_params(),
                                     mk_app(mk_app(mk_app(mk_constant(get_dep_recursor(m_env, const_name(fn)), elim_levels),
                                                          packed_params), unpack_C), unpack_minor_premises));

        define(mk_nested_name(fn_type::PACK, nest_idx), nested_pack_ty, nested_pack_val);
        define(mk_nested_name(fn_type::UNPACK, nest_idx), nested_unpack_ty, nested_unpack_val);

        m_env = set_reducible(m_env, mk_nested_name(fn_type::PACK, nest_idx), reducible_status::Irreducible, true);
        m_env = set_reducible(m_env, mk_nested_name(fn_type::UNPACK, nest_idx), reducible_status::Irreducible, true);
        m_tctx.set_env(m_env);

        for (auto const & slemma : spec_lemmas) {
            name n  = mk_spec_name(mk_nested_name(slemma.m_fn_type, nest_idx), slemma.m_ir_name);
            expr ty = Pi(m_nested_decl.get_params(), Pi(slemma.m_to_abstract, mk_eq(m_tctx, slemma.m_lhs, slemma.m_rhs)));
            expr pf = Fun(m_nested_decl.get_params(), Fun(slemma.m_to_abstract, mk_eq_refl(m_tctx, slemma.m_lhs)));
            define_theorem(n, ty, pf);
            m_lemmas = add(m_tctx, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
        }

        prove_nested_pack_unpack(start, end, c_nested_pack, c_nested_unpack, indices, nest_idx);
        prove_nested_unpack_pack(start, end, c_nested_pack, c_nested_unpack, indices, nest_idx);
        prove_nested_pack_sizeof(start, end, c_nested_pack, indices, nest_idx);
        prove_nested_pack_injective(nest_idx);

        return optional<expr_pair>(c_nested_pack, c_nested_unpack);
    }

    void build_primitive_pack_unpack() {
        m_primitive_pack = m_nested_decl.mk_const_params(mk_primitive_name(fn_type::PACK));
        m_primitive_unpack = m_nested_decl.mk_const_params(mk_primitive_name(fn_type::UNPACK));

        buffer<expr> nest_params;
        expr nest_fn = get_app_args(m_nested_occ, nest_params);

        expr remaining_unpacked_type = safe_whnf(m_tctx, m_tctx.infer(m_nested_occ));
        expr remaining_packed_type = safe_whnf(m_tctx, m_tctx.infer(m_replacement));
        expr remaining_type = remaining_unpacked_type;

        // Indices
        buffer<expr> indices;
        {
            expr ty = safe_whnf(m_tctx, remaining_type);
            while (is_pi(ty)) {
                expr l = mk_local_for(ty);
                indices.push_back(l);
                ty = safe_whnf(m_tctx, instantiate(binding_body(ty), l));
            }
        }

        // 1. elim levels
        list<level> pack_elim_levels, unpack_elim_levels;
        {
            pack_elim_levels = const_levels(nest_fn);
            unpack_elim_levels = m_inner_decl.get_levels();
            if (m_elim_to_type) {
                pack_elim_levels = list<level>(m_nested_decl.get_result_level(m_env), pack_elim_levels);
                unpack_elim_levels = list<level>(m_nested_decl.get_result_level(m_env), unpack_elim_levels);
            }
        }

        // 2. motives
        auto construct_C = [&](expr const & start, expr const & end) {
            expr x_ignore = mk_local_pp("x_ignore", mk_app(start, indices));
            return Fun(indices, Fun(x_ignore, mk_app(end, indices)));
        };

        expr pack_C = construct_C(m_nested_occ, m_replacement);
        expr unpack_C = construct_C(m_replacement, m_nested_occ);

        lean_trace(name({"inductive_compiler", "nested", "pack", "primitive"}), tout() << " C := " << pack_C << "\n";);
        lean_trace(name({"inductive_compiler", "nested", "unpack", "primitive"}), tout() << " C := " << unpack_C << "\n";);

        // 3. minor premises
        list<name> intro_rules = get_ginductive_intro_rules(m_env, const_name(nest_fn));
        buffer<expr> pack_minor_premises, unpack_minor_premises;
        buffer<spec_lemma> spec_lemmas;
        for (name const & intro_rule : intro_rules) {
            expr c_unpacked_ir = mk_app(mk_constant(intro_rule, const_levels(nest_fn)), nest_params);
            expr c_packed_ir = m_inner_decl.mk_const_params(mk_inner_name(intro_rule));

            expr unpacked_ir_type = safe_whnf(m_tctx, m_tctx.infer(c_unpacked_ir));
            expr packed_ir_type = safe_whnf(m_tctx, m_tctx.infer(c_packed_ir));

            // for definition
            buffer<expr> unpacked_rec_args;
            buffer<expr> unpacked_locals;
            buffer<expr> unpacked_return_args;

            buffer<expr> packed_locals;
            buffer<expr> packed_rec_args;
            buffer<expr> packed_return_args;

            // for lemmas
            buffer<expr> unpacked_lhs_args;
            buffer<expr> unpacked_rhs_args;

            buffer<expr> packed_lhs_args;
            buffer<expr> packed_rhs_args;

            while (is_pi(unpacked_ir_type) && is_pi(packed_ir_type)) {
                buffer<expr> unpacked_arg_args;
                expr unpacked_arg_fn = get_app_args(binding_domain(unpacked_ir_type), unpacked_arg_args);

                buffer<expr> packed_arg_args;
                expr packed_arg_fn = get_app_args(binding_domain(packed_ir_type), packed_arg_args);

                expr unpacked_l = mk_local_for(unpacked_ir_type);
                expr packed_l;

                if (unpacked_arg_fn == nest_fn) {
                    // it is a recursive argument
                    expr unpacked_rec_arg_type = mk_app(m_replacement, unpacked_arg_args.size() - nest_params.size(), unpacked_arg_args.data() + nest_params.size());
                    expr unpacked_l_rec = mk_local_pp("x_unpacked", unpacked_rec_arg_type);
                    unpacked_rec_args.push_back(unpacked_l_rec);
                    unpacked_return_args.push_back(unpacked_l_rec);
                    unpacked_rhs_args.push_back(mk_app(mk_app(m_primitive_pack, unpacked_arg_args.size() - nest_params.size(), unpacked_arg_args.data() + nest_params.size()),
                                                       unpacked_l));

                    packed_l = mk_local_for(packed_ir_type);

                    expr packed_rec_arg_type = mk_app(m_nested_occ, packed_arg_args.size() - m_nested_decl.get_num_params(), packed_arg_args.data() + m_nested_decl.get_num_params());
                    expr packed_l_rec = mk_local_pp("x_packed", packed_rec_arg_type);
                    packed_rec_args.push_back(packed_l_rec);
                    packed_return_args.push_back(packed_l_rec);
                    packed_rhs_args.push_back(mk_app(mk_app(m_primitive_unpack, packed_arg_args.size() - m_nested_decl.get_num_params(), packed_arg_args.data() + m_nested_decl.get_num_params()),
                                                     packed_l));
                } else {
                    assert_def_eq(m_env, mlocal_type(unpacked_l), binding_domain(packed_ir_type));

                    unpacked_return_args.push_back(unpacked_l);
                    unpacked_rhs_args.push_back(unpacked_l);

                    packed_l = unpacked_l;

                    packed_return_args.push_back(packed_l);
                    packed_rhs_args.push_back(packed_l);
                }

                unpacked_locals.push_back(unpacked_l);
                unpacked_lhs_args.push_back(unpacked_l);

                packed_locals.push_back(packed_l);
                packed_lhs_args.push_back(packed_l);

                unpacked_ir_type = safe_whnf(m_tctx, instantiate(binding_body(unpacked_ir_type), unpacked_l));
                packed_ir_type = safe_whnf(m_tctx, instantiate(binding_body(packed_ir_type), packed_l));
            }
            lean_assert(!is_pi(unpacked_ir_type) && !is_pi(packed_ir_type));

            unpacked_locals.append(unpacked_rec_args);
            packed_locals.append(packed_rec_args);

            expr unpacked_minor_premise = Fun(unpacked_locals, mk_app(c_packed_ir, unpacked_return_args));
            expr packed_minor_premise = Fun(packed_locals, mk_app(c_unpacked_ir, packed_return_args));
            pack_minor_premises.push_back(unpacked_minor_premise);
            unpack_minor_premises.push_back(packed_minor_premise);

            lean_trace(name({"inductive_compiler", "nested", "pack", "primitive"}), tout() << " mp := " << unpacked_minor_premise << "\n";);
            lean_trace(name({"inductive_compiler", "nested", "unpack", "primitive"}), tout() << " mp := " << packed_minor_premise << "\n";);

            buffer<expr> unpacked_ir_result_indices, packed_ir_result_indices;
            get_app_indices(unpacked_ir_type, nest_params.size(), unpacked_ir_result_indices);
            get_app_indices(packed_ir_type, m_nested_decl.get_num_params(), packed_ir_result_indices);

            expr unpacked_lhs = mk_app(mk_app(m_primitive_pack, unpacked_ir_result_indices), mk_app(c_unpacked_ir, unpacked_lhs_args));
            expr unpacked_rhs = mk_app(c_packed_ir, unpacked_rhs_args);
            spec_lemmas.push_back(spec_lemma(fn_layer::PRIMITIVE, fn_type::PACK, intro_rule, unpacked_lhs_args, unpacked_lhs, unpacked_rhs));

            expr packed_lhs = mk_app(mk_app(m_primitive_unpack, packed_ir_result_indices), mk_app(c_packed_ir, packed_lhs_args));
            expr packed_rhs = mk_app(c_unpacked_ir, packed_rhs_args);
            spec_lemmas.push_back(spec_lemma(fn_layer::PRIMITIVE, fn_type::UNPACK, mk_inner_name(intro_rule), packed_lhs_args, packed_lhs, packed_rhs));

            lean_trace(name({"inductive_compiler", "nested", "pack", "primitive"}), tout() << " lemma : " << unpacked_lhs << " = " << unpacked_rhs << "\n";);
            lean_trace(name({"inductive_compiler", "nested", "unpack", "primitive"}), tout() << " lemma : " << packed_lhs << " = " << packed_rhs << "\n";);
        }

        expr primitive_pack_ty = Pi(m_nested_decl.get_params(), Pi(indices, mk_arrow(mk_app(m_nested_occ, indices), mk_app(m_replacement, indices))));
        expr primitive_pack_val = Fun(m_nested_decl.get_params(),
                                      mk_app(mk_app(mk_app(mk_constant(get_dep_recursor(m_env, const_name(nest_fn)), pack_elim_levels),
                                                           nest_params), pack_C), pack_minor_premises));

        expr primitive_unpack_ty = Pi(m_nested_decl.get_params(), Pi(indices, mk_arrow(mk_app(m_replacement, indices), mk_app(m_nested_occ, indices))));
        expr primitive_unpack_val = Fun(m_nested_decl.get_params(),
                                        mk_app(mk_app(mk_app(mk_constant(get_dep_recursor(m_env, get_replacement_name()), unpack_elim_levels),
                                                             m_nested_decl.get_params()), unpack_C), unpack_minor_premises));

        define(mk_primitive_name(fn_type::PACK), primitive_pack_ty, primitive_pack_val);
        define(mk_primitive_name(fn_type::UNPACK), primitive_unpack_ty, primitive_unpack_val);

        m_env = set_reducible(m_env, mk_primitive_name(fn_type::PACK), reducible_status::Irreducible, true);
        m_env = set_reducible(m_env, mk_primitive_name(fn_type::UNPACK), reducible_status::Irreducible, true);
        m_tctx.set_env(m_env);

        for (auto const & slemma : spec_lemmas) {
            name n  = mk_spec_name(mk_primitive_name(slemma.m_fn_type), slemma.m_ir_name);
            expr ty = Pi(m_nested_decl.get_params(), Pi(slemma.m_to_abstract, mk_eq(m_tctx, slemma.m_lhs, slemma.m_rhs)));
            expr pf = Fun(m_nested_decl.get_params(), Fun(slemma.m_to_abstract, force_recursors(slemma.m_lhs)));
            define_theorem(n, ty, pf);
            m_lemmas = add(m_tctx, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
        }

        prove_primitive_pack_unpack(indices);
        prove_primitive_unpack_pack(indices);
        prove_primitive_pack_sizeof(indices);
        prove_primitive_pack_injective();
    }

    /////////////////////////////
    ///// Stage 5b: proofs //////
    /////////////////////////////

    expr force_recursors(expr const & lhs) {
        return finalize(m_tctx, get_eq_name(), force_recursors_core(lhs)).get_proof();
    }

    simp_result force_recursors_core(expr const & lhs) {
        expr e = m_tctx.relaxed_whnf(lhs);
        buffer<expr> rec_args;
        expr rec_fn = get_app_args(e, rec_args);
        if (is_constant(rec_fn, get_eq_rec_name())) {
            lean_assert(rec_args.size() == 6);
            simp_result r_first = force_eq_rec(rec_fn, rec_args);
            simp_result r_rest = force_recursors_core(r_first.get_new());
            return join(m_tctx, get_eq_name(), r_first, r_rest);
        } else {
            return simp_result(lhs);
        }
    }

    simp_result force_eq_rec(expr const & rec_fn, buffer<expr> const & rec_args) {
        // See comments above prove_eq_rec_invertible(type_context & ctx, expr const & e) at equation_compiler/util.cpp.
        lean_assert(is_constant(rec_fn, get_eq_rec_name()) && rec_args.size() == 6);
        expr B      = rec_args[0];
        expr from   = rec_args[1]; /* (f (g (f a))) */
        expr C      = rec_args[2];
        expr minor  = rec_args[3]; /* (h (g (f a))) */
        expr to     = rec_args[4]; /* (f a) */
        expr major  = rec_args[5]; /* (f_g_eq (f a)) */
        lean_assert(is_app(from) && is_app(minor));
        assert_def_eq(m_env, app_arg(from), app_arg(minor));
        expr h     = app_fn(minor);
        expr g_f_a = app_arg(from);
        lean_assert(is_app(g_f_a));
        assert_def_eq(m_env, app_arg(g_f_a), to);
        expr g     = get_app_fn(g_f_a);
        lean_assert(is_constant(g));
        expr f_a   = to;
        lean_assert(is_app(f_a));
        expr f     = get_app_fn(f_a);
        expr a     = app_arg(f_a);
        lean_assert(is_constant(f));
        optional<inverse_info> info = has_inverse(m_env, const_name(f));
        lean_assert(info && info->m_inv == const_name(g));
        name g_f_name = info->m_lemma;
        optional<inverse_info> info_inv = has_inverse(m_env, const_name(g));
        lean_assert(info_inv && info_inv->m_inv == const_name(f));
        buffer<expr> major_args;
        expr f_g_eq = get_app_args(major, major_args);
        lean_assert(is_constant(f_g_eq) && !major_args.empty());
        assert_def_eq(m_env, f_a, major_args.back());
        lean_assert(const_name(f_g_eq) == info_inv->m_lemma);
        expr A          = m_tctx.infer(a);
        level A_lvl     = get_level(m_tctx, A);
        expr h_a        = mk_app(h, a);
        expr refl_h_a   = mk_eq_refl(m_tctx, h_a);
        expr f_a_eq_f_a = mk_eq(m_tctx, f_a, f_a);
        /* (fun H : f a = f a, eq.refl (h a)) */
        expr pr_minor   = mk_lambda("_H", f_a_eq_f_a, refl_h_a);
        type_context::tmp_locals aux_locals(m_tctx);
        expr x          = aux_locals.push_local("_x", A);
        /* Remark: we cannot use mk_app(f, x) in the following line.
           Reason: f may have implicit arguments. So, app_fn(f_x) is not equal to f in general,
           and app_fn(f_a) is f + implicit arguments. */
        expr f_x        = mk_app(app_fn(f_a), x);
        expr f_x_eq_f_a = mk_eq(m_tctx, f_x, f_a);
        expr H          = aux_locals.push_local("_H", f_x_eq_f_a);
        expr h_x        = mk_app(h, x);
        /* (@eq.rec B (f x) C (h x) (f a) H) */
        expr eq_rec2    = mk_app(rec_fn, {B, f_x, C, h_x, f_a, H});
        /* (@eq.rec B (f x) C (h x) (f a) H) = h a */
        expr eq_rec2_eq = mk_eq(m_tctx, eq_rec2, h_a);
        /* (fun x : A, (forall H : f x = f a, @eq.rec B (f x) C (h x) (f a) H = h a)) */
        expr pr_motive  = m_tctx.mk_lambda(x, m_tctx.mk_pi(H, eq_rec2_eq));
        expr g_f_eq_a   = mk_app(m_tctx, g_f_name, a);
        /* (eq.symm (g_f_eq a)) */
        expr pr_major   = mk_eq_symm(m_tctx, g_f_eq_a);
        expr pr         = mk_app(mk_constant(get_eq_rec_name(), {mk_level_zero(), A_lvl}),
                                 {A, a, pr_motive, pr_minor, g_f_a, pr_major, major});
        return simp_result(h_a, pr);
    }

    class sizeof_simplify_fn : public simplify_fn {
    protected:
        virtual optional<pair<simp_result, bool>> post(expr const & e, optional<expr> const & parent) override {
            if (optional<expr> r = unfold_sizeof(m_ctx, e))
                return optional<pair<simp_result, bool> >(mk_pair(simp_result(*r), true));

            // If we see a _.sizeof application,
            if (is_sizeof_app(e)) {
                expr fn = get_app_fn(e);
                buffer<simp_lemma> lemmas;
                bool refl_only = true;
                get_eqn_lemmas_for(m_ctx.env(), const_name(fn), refl_only, lemmas);
                for (simp_lemma const & sl : lemmas) {
                    expr result = refl_lemma_rewrite(m_ctx, e, sl);
                    if (result != e) {
                        lean_trace(name({"inductive_compiler", "nested", "simp", "sizeof"}), tout() << "[sizeof rfls]: "
                                   << e << " ==> " << annotated_head_beta_reduce(result) << "\n";);
                        return optional<pair<simp_result, bool> >(mk_pair(simp_result(annotated_head_beta_reduce(result)), true));
                    }
                }
            }
            return simplify_fn::post(e, parent);
        }
    public:
        sizeof_simplify_fn(type_context & ctx, defeq_canonizer::state & dcs, simp_lemmas const & slss, simp_config const & cfg):
        simplify_fn(ctx, dcs, slss, cfg) {}
    };

    simp_config get_simp_config() {
        simp_config cfg;
        cfg.m_max_steps          = 1000000;
        cfg.m_contextual         = false;
        cfg.m_lift_eq            = false;
        cfg.m_canonize_instances = false;
        cfg.m_canonize_proofs    = false;
        cfg.m_use_axioms         = false;
        cfg.m_zeta               = false;
        cfg.m_use_matcher        = false;
        return cfg;
    }

    expr prove_by_tactic(name const & lemma_name, expr const & goal_type, name const & tactic, buffer<vm_obj> const & rev_args) {
        metavar_context mctx;
        expr goal_mvar = mctx.mk_metavar_decl(local_context(), goal_type);
        vm_obj tstate = to_obj(mk_tactic_state_for_metavar(m_env, m_opts, lemma_name, mctx, goal_mvar));
        buffer<vm_obj> all_rev_args;
        all_rev_args.push_back(tstate);
        all_rev_args.append(rev_args);

        vm_state S(m_env, m_opts);
        vm_obj result = S.invoke(tactic, all_rev_args.size(), all_rev_args.begin());

        if (optional<tactic_state> s_new = tactic::is_success(result)) {
            lean_trace(name({"inductive_compiler", "nested", "prove"}), tout() << "[success]: " << lemma_name << "\n";);
            mctx = s_new->mctx();
            return mctx.instantiate_mvars(goal_mvar);
        } else {
            lean_trace(name({"inductive_compiler", "nested", "prove"}), tout() << "[failed]: " << lemma_name << "\n";);
            throw exception(sstream() << "Failed to prove: '" << lemma_name << "'");
        }
    }

    expr prove_by_simp(local_context const & lctx, expr const & thm, list<expr> Hs, bool use_sizeof) {
        environment env = set_reducible(m_env, get_sizeof_name(), reducible_status::Irreducible, false);
        env = set_reducible(env, get_add_name(), reducible_status::Irreducible, false);

        type_context tctx(env, m_tctx.get_options(), lctx, transparency_mode::Semireducible);
        type_context tctx_whnf(env, m_tctx.get_options(), lctx, transparency_mode::None);
        simp_lemmas all_lemmas = use_sizeof ? join(m_lemmas, m_nested_decl.get_sizeof_lemmas()) : m_lemmas;
        for (expr const & H : Hs) {
            expr H_type = tctx_whnf.infer(H);
            all_lemmas = add(tctx_whnf, all_lemmas, mlocal_name(H), H_type, H, LEAN_DEFAULT_PRIORITY);
        }
        lean_trace(name({"inductive_compiler", "nested", "simp", "start"}), tout() << thm << "\n";);
        simp_config cfg = get_simp_config();
        defeq_can_state dcs;
        sizeof_simplify_fn simplifier(tctx, dcs, all_lemmas, cfg);
        auto thm_pr = simplifier.prove_by_simp(get_eq_name(), thm);
        if (!thm_pr) {
            formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
            lean_trace(name({"inductive_compiler", "nested", "simp", "failure"}),
                       tout() << "\n-------------------\n"
                       << lctx.pp(fmtf(m_env, m_tctx.get_options(), m_tctx)) << "\n";);
            throw exception("simplifier failed to prove goal; trace 'inductive_compiler.nested.simp.failure' "
                            "for more information");
        }
        return *thm_pr;
    }

    expr prove_by_induction_simp(name const & rec_name, expr const & thm, bool use_sizeof) {
        lean_trace(name({"inductive_compiler", "nested", "prove"}), tout() << "[goal]: " << thm << "\n";);

        expr ty = thm;
        metavar_context mctx;

        // Note: type_context only used to manage locals and abstract at the end
        type_context tctx(m_env, m_tctx.get_options(), use_sizeof ? m_synth_lctx : local_context());
        type_context::tmp_locals locals(tctx);

        while (is_pi(ty)) {
            expr l = locals.push_local_from_binding(ty);
            ty = instantiate(binding_body(ty), l);
        }
        expr H = locals.as_buffer().back();
        expr goal = mctx.mk_metavar_decl(tctx.lctx(), ty);
        list<list<expr> > subgoal_hypotheses;
        hsubstitution_list subgoal_substitutions;
        list<name> ns;
        list<expr> subgoals = induction(tctx.env(), tctx.get_options(), transparency_mode::None, mctx,
                                        goal, H, rec_name, ns, &subgoal_hypotheses, &subgoal_substitutions);

        for_each2(subgoals, subgoal_hypotheses, [&](expr const & m, list<expr> const & Hs) {
                metavar_decl d = mctx.get_metavar_decl(m);
                expr pf = prove_by_simp(d.get_context(), d.get_type(), Hs, use_sizeof);
                mctx.assign(m, pf);
            });

        expr pf = mctx.instantiate_mvars(goal);
        lean_assert(!has_expr_metavar(pf));
        return locals.mk_lambda(pf);
    }

    void prove_primitive_pack_unpack(buffer<expr> const & index_locals) {
        name n = mk_primitive_name(fn_type::PACK_UNPACK);
        expr x_packed = mk_local_pp("x_packed", mk_app(m_replacement, index_locals));
        name rec_name = get_dep_recursor(m_env, mlocal_name(m_inner_decl.get_inds().back()));
        expr lhs = mk_app(mk_app(m_primitive_pack, index_locals), mk_app(mk_app(m_primitive_unpack, index_locals), x_packed));
        expr goal = mk_eq(m_tctx, lhs, x_packed);
        expr primitive_pack_unpack_type = Pi(m_nested_decl.get_params(), Pi(index_locals, Pi(x_packed, goal)));
        expr primitive_pack_unpack_val = prove_by_induction_simp(rec_name, primitive_pack_unpack_type, false);
        define_theorem(n, primitive_pack_unpack_type, primitive_pack_unpack_val);
        m_lemmas = add(m_tctx, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
    }

    void prove_primitive_unpack_pack(buffer<expr> const & index_locals) {
        name n = mk_primitive_name(fn_type::UNPACK_PACK);
        expr x_unpacked = mk_local_pp("x_unpacked", mk_app(m_nested_occ, index_locals));
        name rec_name = get_dep_recursor(m_env, const_name(get_app_fn(m_nested_occ)));
        expr lhs = mk_app(mk_app(m_primitive_unpack, index_locals), mk_app(mk_app(m_primitive_pack, index_locals), x_unpacked));
        expr goal = mk_eq(m_tctx, lhs, x_unpacked);
        expr primitive_unpack_pack_type = Pi(m_nested_decl.get_params(), Pi(index_locals, Pi(x_unpacked, goal)));
        expr primitive_unpack_pack_val = prove_by_induction_simp(rec_name, primitive_unpack_pack_type, false);
        define_theorem(n, primitive_unpack_pack_type, primitive_unpack_pack_val);
        m_lemmas = add(m_tctx, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
    }

    void prove_primitive_pack_sizeof(buffer<expr> const & index_locals) {
        name n = mk_primitive_name(fn_type::SIZEOF_PACK);
        type_context tctx_synth(m_env, m_tctx.get_options(), m_synth_lctx, transparency_mode::Semireducible);

        expr x_unpacked = mk_local_pp("x_unpacked", mk_app(m_nested_occ, index_locals));
        expr lhs = *unfold_sizeof(tctx_synth, mk_app(tctx_synth, get_sizeof_name(), mk_app(mk_app(m_primitive_pack, index_locals), x_unpacked)));
        expr rhs = mk_app(tctx_synth, get_sizeof_name(), x_unpacked);
        expr goal = mk_eq(tctx_synth, lhs, rhs);
        expr primitive_sizeof_pack_type = Pi(m_nested_decl.get_params(), tctx_synth.mk_pi(m_param_insts, Pi(index_locals, Pi(x_unpacked, goal))));
        name rec_name = get_dep_recursor(m_env, const_name(get_app_fn(m_nested_occ)));
        expr primitive_sizeof_pack_val = prove_by_induction_simp(rec_name, primitive_sizeof_pack_type, true);
        define_theorem(n, primitive_sizeof_pack_type, primitive_sizeof_pack_val);
        tctx_synth.set_env(m_env);
        m_lemmas = add(tctx_synth, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
    }

    void prove_primitive_pack_injective() {
        if (!m_prove_inj) return;
        name pack_name = mk_primitive_name(fn_type::PACK);
        expr goal = mk_pack_injective_type(pack_name);
        name lemma_name = mk_injective_name(pack_name);
        buffer<vm_obj> args;
        args.push_back(to_obj(mk_primitive_name(fn_type::UNPACK_PACK)));
        args.push_back(to_obj(mk_primitive_name(fn_type::UNPACK)));
        expr proof = prove_by_tactic(lemma_name, goal, get_inductive_compiler_tactic_prove_pack_inj_name(), args);
        m_env = module::add(m_env, check(m_env, mk_definition_inferring_trusted(m_env, lemma_name, to_list(m_nested_decl.get_lp_names()), goal, proof, true)));
        m_tctx.set_env(m_env);
        m_inj_lemmas = add(m_tctx, m_inj_lemmas, lemma_name, LEAN_DEFAULT_PRIORITY);
    }

    void prove_nested_pack_unpack(expr const & start, expr const & end, expr const & nested_pack, expr const & nested_unpack, buffer<expr> const & index_locals, unsigned nest_idx) {
        name n = mk_nested_name(fn_type::PACK_UNPACK, nest_idx);
        expr x_packed = mk_local_pp("x_packed", mk_app(end, index_locals));
        name rec_name = get_dep_recursor(m_env, const_name(get_app_fn(start)));
        expr lhs = mk_app(mk_app(nested_pack, index_locals), mk_app(mk_app(nested_unpack, index_locals), x_packed));
        expr goal = mk_eq(m_tctx, lhs, x_packed);
        expr nested_pack_unpack_type = Pi(m_nested_decl.get_params(), Pi(index_locals, Pi(x_packed, goal)));
        expr nested_pack_unpack_val = prove_by_induction_simp(rec_name, nested_pack_unpack_type, false);
        define_theorem(n, nested_pack_unpack_type, nested_pack_unpack_val);
        m_lemmas = add(m_tctx, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
    }

    void prove_nested_unpack_pack(expr const & start, expr const & /* end */, expr const & nested_pack, expr const & nested_unpack, buffer<expr> const & index_locals, unsigned nest_idx) {
        name n = mk_nested_name(fn_type::UNPACK_PACK, nest_idx);
        expr x_unpacked = mk_local_pp("x_unpacked", mk_app(start, index_locals));
        name rec_name = get_dep_recursor(m_env, const_name(get_app_fn(start)));
        expr lhs = mk_app(mk_app(nested_unpack, index_locals), mk_app(mk_app(nested_pack, index_locals), x_unpacked));
        expr goal = mk_eq(m_tctx, lhs, x_unpacked);
        expr nested_unpack_pack_type = Pi(m_nested_decl.get_params(), Pi(index_locals, Pi(x_unpacked, goal)));
        expr nested_unpack_pack_val = prove_by_induction_simp(rec_name, nested_unpack_pack_type, false);
        define_theorem(n, nested_unpack_pack_type, nested_unpack_pack_val);
        m_lemmas = add(m_tctx, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
    }

    void prove_nested_pack_sizeof(expr const & start, expr const & /* end */, expr const & nested_pack, buffer<expr> const & index_locals, unsigned nest_idx) {
        name n = mk_nested_name(fn_type::SIZEOF_PACK, nest_idx);
        type_context tctx_synth(m_env, m_tctx.get_options(), m_synth_lctx);

        expr x_unpacked = mk_local_pp("x_unpacked", mk_app(start, index_locals));
        expr lhs = *unfold_sizeof(tctx_synth, mk_app(tctx_synth, get_sizeof_name(), mk_app(mk_app(nested_pack, index_locals), x_unpacked)));
        expr rhs = mk_app(tctx_synth, get_sizeof_name(), x_unpacked);
        expr goal = mk_eq(tctx_synth, lhs, rhs);
        expr nested_sizeof_pack_type = Pi(m_nested_decl.get_params(), tctx_synth.mk_pi(m_param_insts, Pi(index_locals, Pi(x_unpacked, goal))));
        name rec_name = get_dep_recursor(m_env, const_name(get_app_fn(start)));
        expr nested_sizeof_pack_val = prove_by_induction_simp(rec_name, nested_sizeof_pack_type, true);
        define_theorem(n, nested_sizeof_pack_type, nested_sizeof_pack_val);
        tctx_synth.set_env(m_env);
        m_lemmas = add(tctx_synth, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
    }

    void prove_nested_pack_injective(unsigned nest_idx) {
        if (!m_prove_inj) return;
        name pack_name = mk_nested_name(fn_type::PACK, nest_idx);
        expr goal = mk_pack_injective_type(pack_name);
        name lemma_name = mk_injective_name(pack_name);
        buffer<vm_obj> args;
        args.push_back(to_obj(mk_nested_name(fn_type::UNPACK_PACK, nest_idx)));
        args.push_back(to_obj(mk_nested_name(fn_type::UNPACK, nest_idx)));
        expr proof = prove_by_tactic(lemma_name, goal, get_inductive_compiler_tactic_prove_pack_inj_name(), args);
        m_env = module::add(m_env, check(m_env, mk_definition_inferring_trusted(m_env, lemma_name, to_list(m_nested_decl.get_lp_names()), goal, proof, true)));
        m_tctx.set_env(m_env);
        m_inj_lemmas = add(m_tctx, m_inj_lemmas, lemma_name, LEAN_DEFAULT_PRIORITY);
    }

    expr prove_by_funext(expr const & goal, expr const & fn1, expr const & fn2) {
        buffer<expr> args;
        expr fn = get_app_args(goal, args);
        lean_assert(is_constant(fn) && const_name(fn) == get_eq_name());
        buffer<expr> pi_args;

        type_context tctx(m_env, m_tctx.get_options(), transparency_mode::Semireducible);

        expr ty = safe_whnf(tctx, args[0]);
        while (is_pi(ty)) {
            expr l = tctx.push_local(binding_name(ty), binding_domain(ty), binding_info(ty));
            pi_args.push_back(l);
            ty = safe_whnf(tctx, instantiate(binding_body(ty), l));
        }

        buffer<expr> result_args, result_params, result_indices;
        expr result_fn = get_app_args(ty, result_args);
        split_params_indices(result_args, get_ginductive_num_params(m_env, const_name(result_fn)), result_params, result_indices);
        expr lhs = mk_app(mk_app(fn1, result_indices), mk_app(mk_app(fn2, result_indices), mk_app(args[2], pi_args)));
        expr rhs = mk_app(args[2], pi_args);
        expr pi_goal = mk_eq(tctx, lhs, rhs);
        expr pi_pf = prove_by_simp(tctx.lctx(), pi_goal, list<expr>(), false);

        for (unsigned pi_arg_idx = pi_args.size(); pi_arg_idx > 0; pi_arg_idx--) {
            pi_pf = mk_funext(tctx, tctx.mk_lambda(pi_args[pi_arg_idx-1], pi_pf));
        }

        return pi_pf;
    }

    void prove_pi_pack_unpack(expr const & pi_pack, expr const & pi_unpack, buffer<expr> const & ldeps, expr const & nested_pack_fn, expr const & nested_unpack_fn, expr const & arg_ty) {
        name n = mk_pi_name(fn_type::PACK_UNPACK);
        expr x_packed = mk_local_pp("x_packed", pack_type(arg_ty));
        expr lhs = mk_app(pi_pack, mk_app(pi_unpack, x_packed));
        expr goal = mk_eq(m_tctx, lhs, x_packed);
        expr pi_pack_unpack_type = Pi(m_nested_decl.get_params(), Pi(ldeps, Pi(x_packed, goal)));
        expr pi_pack_unpack_val = Fun(m_nested_decl.get_params(), Fun(ldeps, Fun(x_packed, prove_by_funext(goal, nested_pack_fn, nested_unpack_fn))));
        define_theorem(n, pi_pack_unpack_type, pi_pack_unpack_val);
        m_env = add_inverse_lemma(m_env, n, true);
        m_tctx.set_env(m_env);
    }

    void prove_pi_unpack_pack(expr const & pi_pack, expr const & pi_unpack, buffer<expr> const & ldeps, expr const & nested_pack_fn, expr const & nested_unpack_fn, expr const & arg_ty) {
        name n = mk_pi_name(fn_type::UNPACK_PACK);
        expr x_unpacked = mk_local_pp("x_unpacked", arg_ty);
        expr lhs = mk_app(pi_unpack, mk_app(pi_pack, x_unpacked));
        expr goal = mk_eq(m_tctx, lhs, x_unpacked);
        expr pi_unpack_pack_type = Pi(m_nested_decl.get_params(), Pi(ldeps, Pi(x_unpacked, goal)));
        expr pi_unpack_pack_val = Fun(m_nested_decl.get_params(), Fun(ldeps, Fun(x_unpacked, prove_by_funext(goal, nested_unpack_fn, nested_pack_fn))));
        define_theorem(n, pi_unpack_pack_type, pi_unpack_pack_val);
        m_env = add_inverse_lemma(m_env, n, true);
        m_tctx.set_env(m_env);
    }

    void prove_pi_pack_sizeof(expr const & pi_pack, buffer<expr> const & ldeps, expr const & nested_pack_fn, expr const & arg_ty) {
        name n = mk_pi_name(fn_type::SIZEOF_PACK);
        type_context tctx_synth(m_env, m_tctx.get_options(), m_synth_lctx, transparency_mode::Semireducible);

        expr x_unpacked = mk_local_pp("x_unpacked", arg_ty);
        expr lhs = *unfold_sizeof(tctx_synth, mk_app(tctx_synth, get_sizeof_name(), mk_app(pi_pack, x_unpacked)));
        expr rhs = mk_app(tctx_synth, get_sizeof_name(), x_unpacked);
        expr goal = mk_eq(tctx_synth, lhs, rhs);
        expr pi_unpack_pack_type = Pi(m_nested_decl.get_params(), tctx_synth.mk_pi(m_param_insts, Pi(ldeps, Pi(x_unpacked, goal))));
        expr pi_unpack_pack_val;

        expr ty = safe_whnf(tctx_synth, arg_ty);
        if (is_pi(ty)) {
            pi_unpack_pack_val = Fun(m_nested_decl.get_params(), tctx_synth.mk_lambda(m_param_insts, Fun(ldeps, Fun(x_unpacked, mk_eq_refl(tctx_synth, mk_nat_zero())))));
        } else {
            buffer<expr> result_args, result_params, result_indices;
            expr result_fn = get_app_args(ty, result_args);
            split_params_indices(result_args, get_ginductive_num_params(m_env, const_name(result_fn)), result_params, result_indices);
            expr lhs = mk_app(tctx_synth, get_sizeof_name(), mk_app(mk_app(nested_pack_fn, result_indices), x_unpacked));
            expr rhs = mk_app(tctx_synth, get_sizeof_name(), x_unpacked);
            expr pi_pf = prove_by_simp(tctx_synth.lctx(), mk_eq(tctx_synth, lhs, rhs), list<expr>(), false);
            pi_unpack_pack_val = Fun(m_nested_decl.get_params(), tctx_synth.mk_lambda(m_param_insts, Fun(ldeps, Fun(x_unpacked, pi_pf))));
        }
        define_theorem(n, pi_unpack_pack_type, pi_unpack_pack_val);
        m_env = set_simp_sizeof(m_env, n);
        m_nested_decl.set_sizeof_lemmas(add(m_tctx, m_nested_decl.get_sizeof_lemmas(), n, LEAN_DEFAULT_PRIORITY));
        m_tctx.set_env(m_env);
    }

    void prove_pi_pack_injective(unsigned arity) {
        if (!m_prove_inj) return;
        name pack_name = mk_pi_name(fn_type::PACK);
        expr goal = mk_pack_injective_type(pack_name, optional<unsigned>(arity));
        name lemma_name = mk_injective_name(pack_name);
        buffer<vm_obj> args;
        args.push_back(to_obj(mk_pi_name(fn_type::UNPACK_PACK)));
        args.push_back(to_obj(mk_pi_name(fn_type::UNPACK)));
        expr proof = prove_by_tactic(lemma_name, goal, get_inductive_compiler_tactic_prove_pack_inj_name(), args);
        m_env = module::add(m_env, check(m_env, mk_definition_inferring_trusted(m_env, lemma_name, to_list(m_nested_decl.get_lp_names()), goal, proof, true)));
        m_tctx.set_env(m_env);
        m_inj_lemmas = add(m_tctx, m_inj_lemmas, lemma_name, LEAN_DEFAULT_PRIORITY);
    }

    ////////////////////////////////////////////
    ///// Stage 7: define nested recursors /////
    ////////////////////////////////////////////

    void define_nested_recursors() {
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            expr const & nested_ind = m_nested_decl.get_ind(ind_idx);
            expr const & inner_ind = m_inner_decl.get_ind(ind_idx);

            declaration d = m_env.get(get_dep_recursor(m_env, mlocal_name(inner_ind)));
            level_param_names lp_names = d.get_univ_params();
            levels lvls = param_names_to_levels(lp_names);

            expr inner_recursor = mk_app(mk_constant(get_dep_recursor(m_env, mlocal_name(inner_ind)), lvls), m_nested_decl.get_params());
            expr inner_recursor_type = m_tctx.infer(inner_recursor);

            expr outer_recursor_type = Pi(m_nested_decl.get_params(), unpack_type(inner_recursor_type));
            expr outer_recursor_val = Fun(m_nested_decl.get_params(), build_nested_recursor(ind_idx, inner_recursor, unpack_type(inner_recursor_type)));
            define(get_dep_recursor(m_env, mlocal_name(nested_ind)), outer_recursor_type, outer_recursor_val, lp_names);
        }
    }

    expr build_nested_recursor(unsigned ind_idx, expr const & inner_recursor, expr const & outer_recursor_type) {
        expr C;
        buffer<expr> minor_premises;
        buffer<expr> indices;
        expr major_premise;
        expr goal = introduce_locals_for_nested_recursor(ind_idx, outer_recursor_type, C, minor_premises, indices, major_premise);

        // Only the minor premises need to change
        lean_assert(m_nested_decl.get_num_intro_rules(ind_idx) == minor_premises.size());
        buffer<expr> inner_minor_premises;
        for (unsigned ir_idx = 0; ir_idx < minor_premises.size(); ++ir_idx) {
            expr const & minor_premise = minor_premises[ir_idx];
            expr ty = safe_whnf(m_tctx, pack_type(mlocal_type(minor_premise)));

            buffer<expr> inner_minor_premise_args;
            buffer<expr> inner_minor_premise_rec_args;
            while (is_pi(ty)) {
                expr arg = mk_local_for(ty);
                if (get_app_fn(mlocal_type(arg)) != pack_type(C)) {
                    lean_assert(inner_minor_premise_rec_args.empty());
                    inner_minor_premise_args.push_back(arg);
                } else {
                    inner_minor_premise_rec_args.push_back(arg);
                }
                ty = safe_whnf(m_tctx, instantiate(binding_body(ty), arg));
            }
            inner_minor_premises.push_back(build_nested_minor_premise_fn(*this, ind_idx, ir_idx, minor_premise, inner_minor_premise_args,
                                                                         inner_minor_premise_rec_args, ty)());
        }

        return Fun(C,
                   Fun(minor_premises,
                       Fun(indices,
                           Fun(major_premise,
                               mk_app(mk_app(mk_app(mk_app(inner_recursor, C), inner_minor_premises), indices), major_premise)))));
    }

    expr introduce_locals_for_nested_recursor(unsigned ind_idx, expr const & outer_recursor_type,
                                              expr & C, buffer<expr> & minor_premises,
                                              buffer<expr> & indices, expr & major_premise) {
        expr ty = safe_whnf(m_tctx, outer_recursor_type);

        C = mk_local_for(ty, "C");
        ty = safe_whnf(m_tctx, instantiate(binding_body(ty), C));

        for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
            expr minor_premise = mk_local_for(ty);
            minor_premises.push_back(minor_premise);
            ty = safe_whnf(m_tctx, instantiate(binding_body(ty), minor_premise));
        }

        while (is_pi(ty)) {
            expr l = mk_local_for(ty);
            ty = safe_whnf(m_tctx, instantiate(binding_body(ty), l));
            if (is_pi(ty))
                indices.push_back(l);
            else
                major_premise = l;
        }
        return ty;
    }

    class build_nested_minor_premise_fn {
        add_nested_inductive_decl_fn & m_outer;
        unsigned m_ind_idx;
        unsigned m_ir_idx;
        expr m_minor_premise;
        buffer<expr> const & m_inner_minor_premise_args;
        buffer<expr> const & m_inner_minor_premise_rec_args;

        expr m_motive_app;

        expr build(unsigned arg_idx, list<expr> rev_ir_args, list<expr> rev_mp_args) {
            if (arg_idx == m_inner_minor_premise_args.size()) {
                buffer<expr> mp_args;
                to_buffer(reverse(rev_mp_args), mp_args);
                return mk_app(mk_app(m_minor_premise, mp_args), m_inner_minor_premise_rec_args);
            }

            expr const & arg = m_inner_minor_premise_args[arg_idx];

            optional<unsigned> pack_arity = m_outer.m_pack_arity[m_ind_idx][m_ir_idx][arg_idx];
            if (!pack_arity)
                return build(arg_idx+1, list<expr>(arg, rev_ir_args), list<expr>(arg, rev_mp_args));

            buffer<expr> ir_args;
            to_buffer(reverse(rev_ir_args), ir_args);

            buffer<expr> mp_args;
            to_buffer(reverse(rev_mp_args), mp_args);

            // Need to store the number-of-ldeps so that I can pass the right mask to the app-builder
            name pack_fn = m_outer.mk_pi_name(fn_type::PACK, m_ind_idx, m_ir_idx, arg_idx);
            name unpack_fn = m_outer.mk_pi_name(fn_type::UNPACK, m_ind_idx, m_ir_idx, arg_idx);
            name pack_unpack_fn = m_outer.mk_pi_name(fn_type::PACK_UNPACK, m_ind_idx, m_ir_idx, arg_idx);

            expr motive = Fun(m_inner_minor_premise_args[arg_idx],
                              mk_app(m_motive_app,
                                     mk_app(
                                         mk_app(m_outer.m_inner_decl.get_c_ir_params(m_ind_idx, m_ir_idx),
                                                ir_args),
                                         m_inner_minor_premise_args.size() - arg_idx,
                                         m_inner_minor_premise_args.data() + arg_idx)));

            expr rest = build(arg_idx+1,
                              list<expr>(mk_app(m_outer.m_tctx, pack_fn, *pack_arity, mk_app(m_outer.m_tctx, unpack_fn, *pack_arity, arg)), rev_ir_args),
                              list<expr>(mk_app(m_outer.m_tctx, unpack_fn, *pack_arity, arg), rev_mp_args));
            expr equality_proof = mk_app(m_outer.m_tctx, pack_unpack_fn, *pack_arity, arg);

            assert_type_correct(m_outer.m_env, motive);
            assert_type_correct(m_outer.m_env, rest);
            assert_type_correct(m_outer.m_env, equality_proof);

            return mk_eq_rec(m_outer.m_tctx, motive, rest, equality_proof);
        }

    public:
        build_nested_minor_premise_fn(add_nested_inductive_decl_fn & outer,
                                      unsigned ind_idx,
                                      unsigned ir_idx,
                                      expr const & minor_premise,
                                      buffer<expr> const & inner_minor_premise_args,
                                      buffer<expr> const & inner_minor_premise_rec_args,
                                      expr const & goal):
            m_outer(outer),
            m_ind_idx(ind_idx),
            m_ir_idx(ir_idx),
            m_minor_premise(minor_premise),
            m_inner_minor_premise_args(inner_minor_premise_args),
            m_inner_minor_premise_rec_args(inner_minor_premise_rec_args),
            m_motive_app(app_fn(goal)) {}

        expr operator()() {
            return Fun(m_inner_minor_premise_args,
                       Fun(m_inner_minor_premise_rec_args,
                           build(0, list<expr>(), list<expr>())));
        }
    };

    void define_nested_cases_on() {
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            expr const & nested_ind = m_nested_decl.get_ind(ind_idx);
            expr const & inner_ind = m_inner_decl.get_ind(ind_idx);

            declaration d = m_env.get(inductive::get_elim_name(mlocal_name(inner_ind)));
            level_param_names lp_names = d.get_univ_params();
            levels lvls = param_names_to_levels(lp_names);

            expr inner_cases_on = mk_app(mk_constant(name(mlocal_name(inner_ind), "cases_on"), lvls), m_nested_decl.get_params());
            expr inner_cases_on_type = m_tctx.infer(inner_cases_on);

            expr outer_cases_on_type = Pi(m_nested_decl.get_params(), unpack_type(inner_cases_on_type));
            expr outer_cases_on_val = Fun(m_nested_decl.get_params(), build_nested_cases_on(ind_idx, inner_cases_on, unpack_type(inner_cases_on_type)));
            define(name(mlocal_name(nested_ind), "cases_on"), outer_cases_on_type, outer_cases_on_val, lp_names);
        }
    }

    expr build_nested_cases_on(unsigned ind_idx, expr const & inner_cases_on, expr const & outer_cases_on_type) {
        expr C;
        buffer<expr> indices;
        expr major_premise;
        buffer<expr> minor_premises;
        expr goal = introduce_locals_for_nested_cases_on(ind_idx, outer_cases_on_type, C, indices, major_premise, minor_premises);

        // Only the minor premises need to change
        lean_assert(m_nested_decl.get_num_intro_rules(ind_idx) == minor_premises.size());
        buffer<expr> inner_minor_premises;
        for (unsigned ir_idx = 0; ir_idx < minor_premises.size(); ++ir_idx) {
            expr const & minor_premise = minor_premises[ir_idx];
            expr ty = safe_whnf(m_tctx, pack_type(mlocal_type(minor_premise)));

            buffer<expr> inner_minor_premise_args;
            buffer<expr> inner_minor_premise_rec_args;
            while (is_pi(ty)) {
                expr arg = mk_local_for(ty);
                if (get_app_fn(mlocal_type(arg)) != pack_type(C)) {
                    lean_assert(inner_minor_premise_rec_args.empty());
                    inner_minor_premise_args.push_back(arg);
                } else {
                    inner_minor_premise_rec_args.push_back(arg);
                }
                ty = safe_whnf(m_tctx, instantiate(binding_body(ty), arg));
            }
            inner_minor_premises.push_back(build_nested_minor_premise_fn(*this, ind_idx, ir_idx, minor_premise, inner_minor_premise_args,
                                                                         inner_minor_premise_rec_args, ty)());
        }

        return Fun(C,
                   Fun(indices,
                       Fun(major_premise,
                           Fun(minor_premises,
                               mk_app(mk_app(mk_app(mk_app(inner_cases_on, C), indices), major_premise), inner_minor_premises)))));
    }

    expr introduce_locals_for_nested_cases_on(unsigned ind_idx, expr const & outer_cases_on_type,
                                              expr & C, buffer<expr> & indices, expr & major_premise,
                                              buffer<expr> & minor_premises) {
        expr ty = safe_whnf(m_tctx, outer_cases_on_type);

        C = mk_local_for(ty, "C");
        ty = safe_whnf(m_tctx, instantiate(binding_body(ty), C));

        while (true) {
            expr l = mk_local_for(ty);
            ty = safe_whnf(m_tctx, instantiate(binding_body(ty), l));
            if (m_nested_decl.is_ind_app(mlocal_type(l), ind_idx)) {
                major_premise = l;
                break;
            } else {
                indices.push_back(l);
            }
        }

        for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
            expr minor_premise = mk_local_for(ty);
            minor_premises.push_back(minor_premise);
            ty = safe_whnf(m_tctx, instantiate(binding_body(ty), minor_premise));
        }

        return ty;
    }

    void define_nested_injectives() {
        if (!m_prove_inj) return;
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
                expr const & ir = m_nested_decl.get_intro_rule(ind_idx, ir_idx);
                name inj_name = mk_injective_name(mlocal_name(ir));
                expr inj_type = mk_injective_type(m_env, mlocal_name(ir), Pi(m_nested_decl.get_params(), mlocal_type(ir)),
                                                      m_nested_decl.get_num_params(), to_list(m_nested_decl.get_lp_names()));

                buffer<vm_obj> rev_args;
                rev_args.push_back(to_obj(mk_injective_arrow_name(mlocal_name(m_inner_decl.get_intro_rule(ind_idx, ir_idx)))));
                rev_args.push_back(to_obj(m_inj_lemmas));

                expr inj_val = prove_by_tactic(inj_name, inj_type, get_inductive_compiler_tactic_prove_nested_inj_name(), rev_args);
                m_env = module::add(m_env,
                                    check(m_env,
                                          mk_definition_inferring_trusted(m_env, inj_name, to_list(m_nested_decl.get_lp_names()), inj_type, inj_val, true)));
                m_env = mk_injective_arrow(m_env, mlocal_name(ir));
            }
        }
        m_tctx.set_env(m_env);
    }

public:
    add_nested_inductive_decl_fn(environment const & env, options const & opts,
                                 name_map<implicit_infer_kind> const & implicit_infer_map,
                                 ginductive_decl & nested_decl, bool is_trusted):
        m_env(env), m_opts(opts), m_implicit_infer_map(implicit_infer_map),
        m_nested_decl(nested_decl), m_is_trusted(is_trusted),
        m_inner_decl(m_nested_decl.get_nest_depth() + 1, m_nested_decl.get_lp_names(), m_nested_decl.get_params(),
                     m_nested_decl.get_num_indices(), m_nested_decl.get_ir_offsets()),
        m_tctx(env, opts, transparency_mode::Semireducible) { }

    optional<environment> operator()() {
        if (!find_nested_occ())
            return optional<environment>();

        construct_inner_decl();
        add_inner_decl();

        if (m_inner_decl.has_sizeof_lemmas()) {
            m_nested_decl.set_sizeof_lemmas(m_inner_decl.get_sizeof_lemmas());
        } else {
            m_nested_decl.set_sizeof_lemmas(get_sizeof_simp_lemmas(m_tctx.env(), m_tctx.mode()));
        }

        check_elim_to_type();
        check_prove_inj();
        define_nested_inds();

        define_nested_has_sizeofs();
        build_primitive_pack_unpack();
        define_nested_irs();
        define_nested_recursors();
        define_nested_cases_on();
        define_nested_injectives();


        return optional<environment>(m_env);
    }
};

optional<environment> add_nested_inductive_decl(environment const & env, options const & opts,
                                                name_map<implicit_infer_kind> const & implicit_infer_map,
                                                ginductive_decl & decl, bool is_trusted) {
    return add_nested_inductive_decl_fn(env, opts, implicit_infer_map, decl, is_trusted)();
}

void initialize_inductive_compiler_nested() {
    register_trace_class(name({"inductive_compiler", "nested"}));
    register_trace_class(name({"inductive_compiler", "nested", "found_occ"}));

    register_trace_class(name({"inductive_compiler", "nested", "mimic"}));
    register_trace_class(name({"inductive_compiler", "nested", "mimic", "ind"}));
    register_trace_class(name({"inductive_compiler", "nested", "mimic", "ir"}));
    register_trace_class(name({"inductive_compiler", "nested", "mimic", "ir", "offset"}));

    register_trace_class(name({"inductive_compiler", "nested", "inner"}));
    register_trace_class(name({"inductive_compiler", "nested", "inner", "ind"}));
    register_trace_class(name({"inductive_compiler", "nested", "inner", "ir"}));

    register_trace_class(name({"inductive_compiler", "nested", "sizeof"}));
    register_trace_class(name({"inductive_compiler", "nested", "prove"}));
    register_trace_class(name({"inductive_compiler", "nested", "injective"}));

    register_trace_class(name({"inductive_compiler", "nested", "define"}));
    register_trace_class(name({"inductive_compiler", "nested", "define", "success"}));
    register_trace_class(name({"inductive_compiler", "nested", "define", "failure"}));

    register_trace_class(name({"inductive_compiler", "nested", "simp"}));
    register_trace_class(name({"inductive_compiler", "nested", "simp", "start"}));
    register_trace_class(name({"inductive_compiler", "nested", "simp", "sizeof"}));
    register_trace_class(name({"inductive_compiler", "nested", "simp", "failure"}));

    g_nest_prefix = new name("_nest");
}

void finalize_inductive_compiler_nested() {
    delete g_nest_prefix;
}
}
