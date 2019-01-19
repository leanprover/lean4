/*
Copyright (c) 2018 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich

Lean interface to the old elaborator/elaboration parts of the parser
*/

#include <string>
#include <iostream>
#include "library/replace_visitor.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/annotation.h"
#include "util/timeit.h"
#include "library/locals.h"
#include "library/trace.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_nat.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/definition_cmds.h"
#include "frontends/lean/brackets.h"
#include "frontends/lean/choice.h"
#include "frontends/lean/inductive_cmds.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/util.h"

namespace lean {
struct resolve_names_fn : public replace_visitor {
    parser &         m_p;
    names            m_locals;
    bool             m_assume_local = false;

    resolve_names_fn(parser & p) : m_p(p) {}

    virtual expr visit_constant(expr const &) override {
        lean_unreachable();
    }

    virtual expr visit_local(expr const & e) override {
        if (m_assume_local)
            return e;
        lean_unreachable();
    }

    virtual expr visit_binding(expr const & e) override {
        expr new_d = visit(binding_domain(e));
        flet<names> set(m_locals, cons(binding_name(e), m_locals));
        expr new_b = visit(binding_body(e));
        return update_binding(e, new_d, new_b);
    }

    virtual expr visit_let(expr const & e) override {
        expr new_type = visit(let_type(e));
        expr new_val  = visit(let_value(e));
        flet<names> set(m_locals, cons(let_name(e), m_locals));
        expr new_body = visit(let_body(e));
        return update_let(e, new_type, new_val, new_body);
    }

    expr visit_pre_equations(expr const & e) {
        equations_header header;
        bool is_match = get_bool(mdata_data(e), "match").value_or(false);
        if (is_match) {
            parser::local_scope scope1(m_p);
            match_definition_scope scope2(m_p.env());
            header = mk_match_header(scope2.get_name(), scope2.get_actual_name());
        } else {
            header = mk_match_header("dummy", "dummy");
        }
        buffer<expr> eqns;
        get_app_args(get_annotation_arg(e), eqns);
        if (eqns.empty()) {
            eqns.push_back(copy_pos(e, mk_no_equation()));
        } else {
            for (auto & eqn : eqns) {
                expr lhs = app_fn(eqn);
                expr rhs = app_arg(eqn);
                {
                    flet<bool> _(m_assume_local, true);
                    lhs = visit(lhs);
                }
                buffer<expr> new_locals;
                bool skip_main_fn = true;
                lhs = m_p.patexpr_to_pattern(lhs, skip_main_fn, new_locals);
                if (is_match)
                    new_locals.insert(0, mk_local("_match_fn", mk_expr_placeholder()));
                names locals = m_locals;
                // NOTE: appends `new_locals` to `locals` in reverse
                for (auto const & l : new_locals)
                    locals = cons(local_name_p(l), locals);
                flet<names> _(m_locals, locals);
                rhs = visit(rhs);
                eqn = Fun(new_locals, mk_equation(lhs, rhs), m_p);
            }
        }
        return mk_equations(header, eqns.size(), eqns.data());
    }

    virtual expr visit(expr const & e) override {
        if (is_placeholder(e) || is_as_is(e) || is_emptyc_or_emptys(e) || is_as_atomic(e)) {
            return e;
        } else if (is_annotation(e, "pre_equations")) {
            return visit_pre_equations(e);
        } else if (is_annotation(e, "preresolved")) {
            expr e2 = unwrap_pos(e);
            auto m = mdata_data(e2);
            expr id = mdata_expr(e2);
            if (!m_assume_local) {
                if (auto l = m_p.resolve_local(const_name(id), m_p.pos_of(e), m_locals)) {
                    return copy_pos(e, *l);
                }
            }
            buffer<expr> new_args;
            for (unsigned i = 0;; i++) {
                if (auto n = get_name(m, name(name(), i))) {
                    new_args.push_back(copy_pos(e, mk_const(*n, const_levels(id))));
                } else {
                    break;
                }
            }
            if (new_args.empty()) {
                if (m_assume_local)
                    return mk_local(const_name(id), mk_expr_placeholder());
                throw elaborator_exception(e, format("unknown identifier '") + format(const_name(id).escape()) +
                                              format("'"));
            }
            return mk_choice(new_args.size(), new_args.data());
        } else {
            return replace_visitor::visit(e);
        }
    }
};

expr resolve_names(parser & p, expr const & e) {
    return resolve_names_fn(p)(e);
}


decl_attributes to_decl_attributes(environment const & env, expr const & e, bool local) {
    decl_attributes attributes(!local);
    buffer<expr> attrs;
    get_app_args(e, attrs);
    for (auto const & e : attrs) {
        buffer<expr> args;
        auto attr = get_app_args(e, args);
        auto n = const_name(attr);
        if (n == "recursor") {
            list<unsigned> idxs;
            for (int i = args.size() - 1; i >= 0; i--)
                idxs = cons(lit_value(unwrap_pos(args[i])).get_nat().get_small_value() - 1, idxs);
            attributes.set_attribute(env, n, attr_data_ptr(new indices_attribute_data(idxs)));
        } else {
            lean_assert(args.empty());
            attributes.set_attribute(env, n);
        }
    }
    return attributes;
}

environment elab_attribute_cmd(environment env, expr const & cmd) {
    auto const & data = mdata_data(cmd);
    bool local = *get_bool(data, "local");
    buffer<expr> args, eattrs, eids;
    get_app_args(mdata_expr(cmd), args);
    auto attributes = to_decl_attributes(env, args[0], local);
    get_app_args(args[1], eids);
    for (auto const & e : eids)
        env = attributes.apply(env, get_dummy_ios(), const_name(e));
    return env;
}

cmd_meta to_cmd_meta(environment const & env, expr const & e) {
    auto const & data = mdata_data(e);
    cmd_meta m(to_decl_attributes(env, mdata_expr(e), false));
    m.m_modifiers.m_is_meta = get_bool(data, "meta").value_or(false);
    m.m_modifiers.m_is_mutual = get_bool(data, "mutual").value_or(false);
    m.m_modifiers.m_is_noncomputable = get_bool(data, "noncomputable").value_or(false);
    m.m_modifiers.m_is_private = get_bool(data, "private").value_or(false);
    m.m_modifiers.m_is_protected = get_bool(data, "protected").value_or(false);
    if (auto s = get_string(data, "doc_string"))
        m.m_doc_string = s->to_std_string();
    return m;
}

void elab_check_cmd(parser & p, expr const & cmd) {
    // TODO(Sebastian)
    // transient_cmd_scope cmd_scope(p);
    expr e = mdata_expr(cmd);
    bool check_unassigend = false;
    names ls;
    metavar_context mctx;
    e = resolve_names(p, e);
    std::tie(e, ls) = p.elaborate("_check", mctx, e, check_unassigend);
    names new_ls = to_names(collect_univ_params(e));
    type_context_old tc(p.env());
    expr type = tc.infer(e);
    if (is_synthetic_sorry(e) && (is_synthetic_sorry(type) || is_metavar(type))) {
        // do not show useless type-checking results such as ?? : ?M_1
        return;
    }
    auto out              = p.mk_message(p.cmd_pos(), p.pos(), INFORMATION);
    formatter fmt         = out.get_formatter();
    unsigned indent       = get_pp_indent(p.get_options());
    format e_fmt    = fmt(e);
    format type_fmt = fmt(type);
    format r = group(e_fmt + space() + colon() + nest(indent, line() + type_fmt));
    out.set_caption("check result") << r;
    out.report();
}

expr const & get_arg_names(expr const & e, buffer<name> & ns) {
    buffer<expr> args;
    auto const & fn = get_app_args(e, args);
    for (auto const & e : args)
        ns.push_back(const_name(e));
    return fn;
}

void elab_constant_cmd(parser & p, expr const & cmd) {
    buffer<expr> args;
    buffer<name> ls;
    get_app_args(mdata_expr(cmd), args);
    auto fn = get_arg_names(args[1], ls);
    expr type = args[2];
    type = resolve_names(p, type);
    p.set_env(elab_var(p, variable_kind::Constant, to_cmd_meta(p.env(), args[0]), get_pos_info_provider()->get_pos_info_or_some(cmd),
                       optional<binder_info>(), const_name(fn), type, ls));
}

static expr unpack_mutual_definition(parser & p, expr const & cmd, buffer<name> & lp_names, buffer<expr> & fns, buffer<name> & prv_names,
                                    buffer<expr> & params) {
    parser::local_scope scope1(p);
    auto header_pos = p.pos();
    buffer<expr> args, eqns;
    get_app_args(cmd, args);
    get_arg_names(args[2], lp_names);
    get_app_args(args[3], fns);
    get_app_args(args[4], params);
    for (auto & param : params) {
        param = update_local_p(param, resolve_names(p, local_type_p(param)));
        p.add_local(param);
    }
    auto val = args[5];
    buffer<name> full_names;
    buffer<name> full_actual_names;
    for (unsigned i = 0; i < fns.size(); i++) {
        expr & fn = fns[i];
        expr fn_type = local_type_p(fn);
        fn_type = resolve_names(p, fn_type);
        name n = local_name_p(fn);
        declaration_name_scope scope2(n);
        if (n.is_anonymous())
            n = synthesize_instance_name(p, fn_type, scope2, p.pos_of(fn));
        declaration_name_scope scope3("_main");
        full_names.push_back(scope3.get_name());
        full_actual_names.push_back(scope3.get_actual_name());
        prv_names.push_back(scope2.get_actual_name());
        fn = mk_local(n, n, fn_type, mk_rec_info());
        p.add_local(fn);
        if (!is_annotation(val, "pre_equations")) {
            val = resolve_names(p, val);
        }
    }
    optional<expr> wf_tacs;
    if (args.size() > 6)
        wf_tacs = args[6];
    if (is_annotation(val, "pre_equations")) {
        // TODO(Sebastian): this uses the wrong declaration name scope
        val = resolve_names(p, val);
        to_equations(val, eqns);
        val = mk_equations(p, fns, full_names, full_actual_names, eqns, wf_tacs, header_pos);
    }
    return val;
}

void elab_defs_cmd(parser & p, expr const & cmd) {
    buffer<expr> args;
    get_app_args(mdata_expr(cmd), args);
    auto meta = to_cmd_meta(p.env(), args[0]);
    auto kind = static_cast<decl_cmd_kind>(lit_value(args[1]).get_nat().get_small_value());
    declaration_info_scope scope(p, kind, meta.m_modifiers);
    buffer<name> lp_names;
    buffer<expr> fns, params;
    /* TODO(Leo): allow a different doc string for each function in a mutual definition. */
    optional<std::string> doc_string = meta.m_doc_string;
    environment env = p.env();
    private_name_scope prv_scope(meta.m_modifiers.m_is_private, env);
    buffer<name> prv_names;
    expr val = unpack_mutual_definition(p, mdata_expr(cmd), lp_names, fns, prv_names, params);
    auto header_pos = get_pos_info_provider()->get_pos_info_or_some(cmd);
    p.set_env(elab_defs(p, kind, meta, lp_names, fns, prv_names, params, val, header_pos));
}

static environment elab_inductives_cmd(parser & p, expr const & cmd) {
    parser::local_scope _(p);
    // auto header_pos = get_pos_info_provider()->get_pos_info_or_some(cmd);
    buffer<expr> args, attrs, pre_inds, params, all_intro_rules, infer_kinds;
    buffer<name> lp_names;
    get_app_args(mdata_expr(cmd), args);
    auto meta = to_cmd_meta(p.env(), args[0]);
    get_app_args(args[1], attrs);
    get_arg_names(args[2], lp_names);
    get_app_args(args[3], pre_inds);
    get_app_args(args[4], params);
    get_app_args(args[5], all_intro_rules);
    get_app_args(args[6], infer_kinds);

    for (expr & i : pre_inds)
        p.add_local(i);
    for (expr & param : params) {
        param = update_local_p(param, resolve_names(p, local_type_p(param)));
        p.add_local(param);
    }

    buffer<decl_attributes> mut_attrs;
    name_map<implicit_infer_kind> implicit_infer_map;
    buffer<expr> inds;
    buffer<buffer<expr>> intro_rules;

    for (unsigned i = 0; i < pre_inds.size(); i++) {
        expr const & pre_ind = pre_inds[i];
        auto ind_type = local_type_p(pre_ind);
        ind_type = resolve_names(p, ind_type);
        // check_attrs(attrs);
        mut_attrs.push_back(to_decl_attributes(p.env(), attrs[i], false));
        buffer<expr> intro_rules_i, infer_kinds_i;
        get_app_args(all_intro_rules[i], intro_rules_i);
        get_app_args(infer_kinds[i], infer_kinds_i);
        for (unsigned j = 0; j < intro_rules_i.size(); j++) {
            auto & ir = intro_rules_i[j];
            name ir_name = get_namespace(p.env()) + local_name_p(pre_ind) + local_name_p(ir);
            auto kind = static_cast<implicit_infer_kind>(lit_value(infer_kinds_i[j]).get_nat().get_small_value());
            implicit_infer_map.insert(ir_name, kind);
            expr ir_type = local_type_p(ir);
            ir_type = resolve_names(p, ir_type);
            ir = mk_local(ir_name, ir_type);
        }
        expr ind = mk_local(get_namespace(p.env()) + local_name_p(pre_ind), ind_type);
        inds.push_back(ind);
        intro_rules.push_back(intro_rules_i);
        // HACK: without this line, `ind` would be wrapped in an `as_is` annotation by `collect_implicit_locals`
        params.push_back(ind);
    }

    for (buffer<expr> & irs : intro_rules) {
        for (expr & ir : irs) {
            ir = replace_locals(ir, pre_inds, inds);
        }
    }

    elaborate_inductive_decls(p, meta, mut_attrs, lp_names, implicit_infer_map, params, inds, intro_rules);
    return p.env();
}

static void elab_variables_cmd(parser & p, expr const & cmd) {
    buffer<expr> vars; get_app_args(mdata_expr(cmd), vars);
    for (auto const & var : vars) {
        // Hack: to make sure we get different universe parameters for each parameter.
        // Alternative: elaborate once and copy types replacing universes in new_ls.
        auto id = local_name_p(var);
        auto type = local_type_p(var);
        type = resolve_names(p, type);
        buffer<name> ls;
        p.set_env(elab_var(p, variable_kind::Variable, cmd_meta(), p.pos_of(cmd), some(local_info_p(var)), id, type, ls));
    }
}

static void elaborate_command(parser & p, expr const & cmd) {
    auto const & data = mdata_data(cmd);
    if (auto const & cmd_name = get_name(data, "command")) {
        if (*cmd_name == "attribute") {
            p.set_env(elab_attribute_cmd(p.env(), cmd));
            return;
        } else if (*cmd_name == "#check") {
            elab_check_cmd(p, cmd);
            return;
        } else if (*cmd_name == "constant") {
            elab_constant_cmd(p, cmd);
            return;
        } else if (*cmd_name == "defs") {
            elab_defs_cmd(p, cmd);
            return;
        } else if (*cmd_name == "inductives") {
            p.set_env(elab_inductives_cmd(p, cmd));
            return;
        } else if (*cmd_name == "structure") {
            elab_structure_cmd(p, cmd);
            return;
        } else if (*cmd_name == "init_quot") {
            p.set_env(module::add(p.env(), mk_quot_decl()));
            return;
        } else if (*cmd_name == "variables") {
            elab_variables_cmd(p, cmd);
            return;
        }
    }
    throw elaborator_exception(cmd, "unexpected input to 'elaborate_command'");
}


/* TEMPORARY code for the old runtime */


struct vm_env : public vm_external {
    environment m_env;

    explicit vm_env(environment const & env) : m_env(env) {}

    virtual ~vm_env() {}

    virtual void dealloc() override { delete this; }

    virtual vm_external *ts_clone(vm_clone_fn const &) override { lean_unreachable(); }

    virtual vm_external *clone(vm_clone_fn const &) override { lean_unreachable(); }
};

environment const & to_env(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_env *>(to_external(o)));
    return static_cast<vm_env *>(to_external(o))->m_env;
}

vm_obj vm_environment_empty() {
    return mk_vm_external(new vm_env(environment()));
}

name to_name(vm_obj const & o) {
    switch (cidx(o)) {
        case 0: return name();
        case 1: {
            std::string str = to_string(cfield(o, 1));
            return name(to_name(cfield(o, 0)), str.c_str());
        }
        case 2:
            return name(to_name(cfield(o, 0)), nat(vm_nat_to_mpz1(cfield(o, 1))));
        default: lean_unreachable();
    }
}

vm_obj vm_environment_contains(vm_obj const & vm_env, vm_obj const & vm_n) {
    return mk_vm_simple(static_cast<bool>(to_env(vm_env).find(to_name(vm_n))));
}

vm_obj to_obj(name const & n) {
    if (n.is_anonymous()) {
        return mk_vm_simple(0);
    } else if (n.is_string()) {
        return mk_vm_constructor(1, to_obj(n.get_prefix()), to_obj(n.get_string().to_std_string()));
    } else {
        return mk_vm_constructor(2, to_obj(n.get_prefix()), mk_vm_nat(n.get_numeral().to_mpz()));
    }
}

level to_level(vm_obj const & o) {
    switch (cidx(o)) {
        case 0:
            return mk_level_zero();
        case 1:
            return mk_succ(to_level(cfield(o, 0)));
        case 2:
            return mk_max(to_level(cfield(o, 0)), to_level(cfield(o, 1)));
        case 3:
            return mk_imax(to_level(cfield(o, 0)), to_level(cfield(o, 1)));
        case 4:
            return mk_univ_param(to_name(cfield(o, 0)));
        case 5:
            return mk_univ_mvar(to_name(cfield(o, 0)));
        default: lean_unreachable();
    }
}

levels to_levels(vm_obj const & o) {
    switch (cidx(o)) {
        case 0:
            return levels();
        case 1:
            return levels(to_level(cfield(o, 0)), to_levels(cfield(o, 1)));
        default: lean_unreachable();
    }
}

binder_info to_binder_info(vm_obj const & o) {
    lean_assert(is_simple(o));
    return static_cast<binder_info>(cidx(o));
}

vm_obj to_obj(binder_info const & bi) {
    return mk_vm_simple(static_cast<unsigned>(bi));
}

kvmap to_kvmap(vm_obj const & o) {
    switch (cidx(o)) {
        case 0:
            return kvmap();
        case 1: {
            auto vm_k = cfield(cfield(o, 0), 0);
            auto vm_v = cfield(cfield(o, 0), 1);
            auto vm_d = cfield(vm_v, 0);
            data_value v;
            switch (cidx(vm_v)) {
                case 0:
                    v = data_value(to_string(vm_d));
                    break;
                case 1:
                    v = data_value(nat(vm_nat_to_mpz1(vm_d)));
                    break;
                case 2:
                    v = data_value(to_bool(vm_d));
                    break;
                case 3:
                    v = data_value(to_name(vm_d));
                    break;
                default: lean_unreachable();
            }
            return kvmap({to_name(vm_k), v}, to_kvmap(cfield(o, 1)));
        }
        default: lean_unreachable();
    }
}

// I really don't want to deal with the reverse translation right now
struct vm_expr : public vm_external {
    expr m_expr;
    explicit vm_expr(expr const & expr) : m_expr(expr) {}
    virtual ~vm_expr() {}
    virtual void dealloc() override { delete this; }
    virtual vm_external *ts_clone(vm_clone_fn const &) override { lean_unreachable(); }
    virtual vm_external *clone(vm_clone_fn const &) override { lean_unreachable(); }
};

expr to_expr(vm_obj const & o) {
    if (is_external(o)) {
        lean_vm_check(dynamic_cast<vm_expr *>(to_external(o)));
        return static_cast<vm_expr *>(to_external(o))->m_expr;
    }

    switch (cidx(o)) {
        case 0:
            return mk_bvar(nat(vm_nat_to_mpz1(cfield(o, 0))));
        case 1:
            return mk_local(to_name(cfield(o, 0)), to_name(cfield(o, 1)), to_expr(cfield(o, 2)), to_binder_info(cfield(o, 3)));
        case 2:
            return mk_metavar(to_name(cfield(o, 0)), to_expr(cfield(o, 1)));
        case 3:
            return mk_sort(to_level(cfield(o, 0)));
        case 4:
            return mk_constant(to_name(cfield(o, 0)), to_levels(cfield(o, 1)));
        case 5:
            return mk_app(to_expr(cfield(o, 0)), to_expr(cfield(o, 1)));
        case 6:
            return mk_lambda(to_name(cfield(o, 0)), to_expr(cfield(o, 2)), to_expr(cfield(o, 3)),
                             to_binder_info(cfield(o, 1)));
        case 7:
            return mk_pi(to_name(cfield(o, 0)), to_expr(cfield(o, 2)), to_expr(cfield(o, 3)),
                         to_binder_info(cfield(o, 1)));
        case 8:
            return mk_let(to_name(cfield(o, 0)), to_expr(cfield(o, 1)), to_expr(cfield(o, 2)), to_expr(cfield(o, 3)));
        case 9: {
            auto l = cfield(o, 0);
            switch (cidx(l)) {
                case 0:
                    return mk_lit(literal(to_string(cfield(l, 0)).c_str()));
                case 1:
                    return mk_lit(literal(vm_nat_to_mpz1(cfield(l, 0))));
                default: lean_unreachable();
            }
        }
        case 10:
            return mk_mdata(to_kvmap(cfield(o, 0)), to_expr(cfield(o, 1)));
        case 11:
            return mk_proj(to_name(cfield(o, 0)), nat(vm_nat_to_mpz1(cfield(o, 1))), to_expr(cfield(o, 2)));
        default: lean_unreachable();
    }
}

options to_options(vm_obj o) {
    options opts;
    kvmap m = to_kvmap(o);
    for (auto const & kv : m) {
        switch (kv.snd().kind()) {
            case data_value_kind::Bool:
                opts.update(kv.fst(), kv.snd().get_bool());
                break;
            case data_value_kind::Name:
                opts.update(kv.fst(), kv.snd().get_name());
                break;
            case data_value_kind::Nat:
                opts.update(kv.fst(), kv.snd().get_nat().get_small_value());
                break;
            case data_value_kind::String:
                opts.update(kv.fst(), kv.snd().get_string());
                break;
        }
    }
    return opts;
}

name_set to_name_set(vm_obj o) {
    name_set ns;
    while (o.is_ptr()) {
        ns.insert(to_name(cfield(o, 0)));
        o = cfield(o, 1);
    }
    return ns;
}

name_generator to_name_generator(vm_obj const & o) {
    name_generator ngen;
    ngen.m_prefix = to_name(cfield(o, 0));
    ngen.m_next_idx = to_unsigned(cfield(o, 1));
    return ngen;
}

vm_obj to_obj(name_generator const & ngen) {
    return mk_vm_constructor(0, to_obj(ngen.m_prefix), mk_vm_nat(ngen.m_next_idx));
}

vm_obj to_obj(pos_info const & pos) {
    return mk_vm_constructor(0, mk_vm_simple(pos.first), mk_vm_simple(pos.second));
}

vm_obj to_obj(message const & msg) {
    return mk_vm_constructor(0, {
            to_obj(msg.get_filename()),
            to_obj(msg.get_pos()),
            msg.get_end_pos() ? to_obj(*msg.get_end_pos()) : mk_vm_none(),
            mk_vm_simple(static_cast<unsigned>(msg.get_severity())),
            to_obj(msg.get_caption()),
            to_obj(msg.get_text()),
    });
}

vm_obj to_obj(message_log const & log) {
    auto msgs = log.to_buffer();
    auto o = mk_vm_simple(0);
    for (auto const & msg : msgs)
        o = mk_vm_constructor(1, to_obj(msg), o);
    return o;
}

/* elaborate_command (filename : string) : expr → old_elaborator_state → option old_elaborator_state × message_log */
// TODO(Sebastian): replace `string` with `message` in the new runtime
vm_obj vm_elaborate_command(vm_obj const & vm_filename, vm_obj const & vm_cmd, vm_obj const & vm_st) {
    auto vm_e = cfield(vm_st, 0);
    auto env = to_env(vm_e);
    io_state const & ios = get_dummy_ios();
    auto filename = to_string(vm_filename);
    std::stringstream in;
    parser p(env, ios, in, filename);
    auto s = p.mk_snapshot();
    auto ngen = to_name_generator(cfield(vm_st, 1));
    auto vm_lds = cfield(vm_st, 2);
    local_level_decls lds;
    name_set lvars;
    while (vm_lds.is_ptr()) {
        auto it = cfield(vm_lds, 0);
        auto n = to_name(cfield(it, 0));
        lds.insert(n, to_level(cfield(it, 1)));
        // all local decls are variables in Lean 4
        lvars.insert(n);
        vm_lds = cfield(vm_lds, 1);
    }
    auto vm_eds = cfield(vm_st, 3);
    local_expr_decls eds;
    name_set vars;
    while (vm_eds.is_ptr()) {
        auto it = cfield(vm_eds, 0);
        auto n = to_name(cfield(it, 0));
        auto data = cfield(it, 1);
        eds.insert(n, mk_local(to_name(cfield(data, 0)), n, to_expr(cfield(data, 1)), to_binder_info(cfield(data, 2))));
        // all local decls are variables in Lean 4
        vars.insert(n);
        vm_eds = cfield(vm_eds, 1);
    }
    auto includes = to_name_set(cfield(vm_st, 4));
    auto options = to_options(cfield(vm_st, 5));
    p.reset(snapshot(p.env(), ngen, lds, eds, lvars, vars, includes, options, true, false,
            parser_scope_stack(), to_unsigned(cfield(vm_st, 6)), pos_info {1, 0}));
    auto ns = to_name(cfield(vm_st, 7));
    p.set_env(set_namespace(env, ns));

    auto cmd = to_expr(vm_cmd);
    message_log log;
    scope_message_log _(log);
    vm_obj vm_out = mk_vm_none();
    try {
        elaborate_command(p, cmd);
        s = p.mk_snapshot();

        // sort levels by reverse insertion order. ugh.
        rb_map<unsigned, name, unsigned_rev_cmp> new_lds;
        s->m_lds.for_each([&](name const & n, level const &) {
            new_lds.insert(s->m_lds.find_idx(n), n);
        });
        new_lds.for_each([&](unsigned const &, name const & n) {
            auto vm_n = to_obj(n);
            auto vm_ld = mk_vm_constructor(0, vm_n, mk_vm_constructor(4, vm_n));
            vm_lds = mk_vm_constructor(1, vm_ld, vm_lds);
        });

        for (auto const & ed : s->m_eds.get_entries()) {
            if (!is_local_p(ed.second)) {
                // obsolete local ref, ignore
                continue;
            }
            auto vm_ed = mk_vm_constructor(0, to_obj(ed.first), mk_vm_constructor(0,
                    to_obj(local_name_p(ed.second)),
                    mk_vm_external(new vm_expr(local_type_p(ed.second))),
                    to_obj(local_info_p(ed.second))));
            vm_eds = mk_vm_constructor(1, vm_ed, vm_eds);
        }

        auto vm_st2 = mk_vm_constructor(0, {
            mk_vm_external(new vm_env(p.env())),
            to_obj(s->m_ngen),
            vm_lds,
            vm_eds,
            cfield(vm_st, 4),
            cfield(vm_st, 5),
            cfield(vm_st, 6),
            cfield(vm_st, 7)
        });
        vm_out = mk_vm_some(vm_st2);
    } catch (exception & e) {
        message_builder builder(env, ios, filename, get_pos_info_provider()->get_pos_info_or_some(cmd),
                message_severity::ERROR);
        builder.set_exception(e);
        builder.report();
    }
    return mk_vm_constructor(0, vm_out, to_obj(log));
}

vm_obj vm_expr_local(vm_obj const & vm_pp_name, vm_obj const & vm_name, vm_obj const & vm_type, vm_obj const & vm_binder_info) {
    return mk_vm_constructor(1, vm_pp_name, vm_name, vm_type, vm_binder_info);
}

void initialize_vm_elaborator() {
    DECLARE_VM_BUILTIN(name({"lean", "expr", "local"}), vm_expr_local);
    DECLARE_VM_BUILTIN(name({"lean", "environment", "empty"}), vm_environment_empty);
    DECLARE_VM_BUILTIN(name({"lean", "environment", "contains"}), vm_environment_contains);
    DECLARE_VM_BUILTIN(name({"lean", "elaborator", "elaborate_command"}), vm_elaborate_command);
}

void finalize_vm_elaborator() {
}
}
