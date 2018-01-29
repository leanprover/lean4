/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "kernel/error_msgs.h"
#include "kernel/for_each_fn.h"
#include "kernel/type_checker.h"
#include "library/kernel_serializer.h"
#include "library/scoped_ext.h"
#include "library/annotation.h"
#include "library/locals.h"
#include "library/explicit.h"
#include "library/aliases.h"
#include "library/constants.h"
#include "library/typed_expr.h"
#include "library/placeholder.h"
#include "library/unfold_macros.h"
#include "library/choice.h"
#include "library/string.h"
#include "library/num.h"
#include "library/util.h"
#include "library/normalize.h"
#include "library/metavar_context.h"
#include "library/replace_visitor.h"
#include "library/compiler/vm_compiler.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/decl_util.h" // TODO(Leo): remove
#include "frontends/lean/prenum.h"

#ifndef LEAN_DEFAULT_AUTO_PARAM_CHECK_EXISTS
#define LEAN_DEFAULT_AUTO_PARAM_CHECK_EXISTS true
#endif

namespace lean {
static name * g_auto_param_check_exists = nullptr;

static bool get_auto_param_check_exists(options const & o) {
    return o.get_bool(*g_auto_param_check_exists, LEAN_DEFAULT_AUTO_PARAM_CHECK_EXISTS);
}

void consume_until_end_or_command(parser & p) {
    while (!p.curr_is_command() && !p.curr_is_eof() && !p.curr_is_token(get_period_tk())) {
        if (p.curr() == token_kind::Eof)
            return;
        p.next();
    }
    if (p.curr_is_token(get_end_tk()))
        p.next();
}

void check_command_period_docstring_or_eof(parser const & p) {
    if (!p.curr_is_command() && !p.curr_is_eof() && !p.curr_is_token(get_period_tk()) &&
        p.curr() != token_kind::DocBlock && p.curr() != token_kind::ModDocBlock)
        throw parser_error("unexpected token, '.', command, or end-of-file expected", p.pos());
}

void check_command_period_open_binder_or_eof(parser const & p) {
    if (!p.curr_is_command_like() && !p.curr_is_eof() && !p.curr_is_token(get_period_tk()) &&
        !p.curr_is_token(get_lparen_tk()) && !p.curr_is_token(get_lbracket_tk()) &&
        !p.curr_is_token(get_lcurly_tk()) && !p.curr_is_token(get_ldcurly_tk()))
        throw parser_error("unexpected token, '(', '{', '[', '⦃', '.', command, or end-of-file expected", p.pos());
}

void check_atomic(name const & n) {
    if (!n.is_atomic())
        throw exception(sstream() << "invalid declaration name '" << n << "', identifier must be atomic");
}

void check_in_section(parser const & p) {
    if (!in_section(p.env()))
        throw exception(sstream() << "invalid command, it must be used in a section");
}

bool is_root_namespace(name const & n) {
    return n == get_root_tk();
}

name remove_root_prefix(name const & n) {
    return n.replace_prefix(get_root_tk(), name());
}

bool is_eqn_prefix(parser & p, bool bar_only = false) {
    return p.curr_is_token(get_bar_tk()) || (!bar_only && p.curr_is_token(get_comma_tk()));
}

// Return the local levels in \c ls that are not associated with variables
levels collect_local_nonvar_levels(parser & p, level_param_names const & ls) {
    buffer<level> section_ls_buffer;
    for (name const & l : ls) {
        if (p.is_local_level(l) && !p.is_local_level_variable(l))
            section_ls_buffer.push_back(mk_param_univ(l));
        else
            break;
    }
    return to_list(section_ls_buffer.begin(), section_ls_buffer.end());
}

// Version of collect_locals(expr const & e, collected_locals & ls) that ignores local constants occurring in
// tactics.
static void collect_locals_ignoring_tactics(expr const & e, collected_locals & ls) {
    if (!has_local(e))
        return;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_local(e))
                return false;
            // if (is_by(e))
            // return false; // do not visit children
            if (is_local(e))
                ls.insert(e);
            return true;
        });
}

void remove_local_vars(parser const & p, buffer<expr> & locals) {
    unsigned j = 0;
    for (unsigned i = 0; i < locals.size(); i++) {
        expr const & param = locals[i];
        if (!is_local(param) || !p.is_local_variable(param)) {
            locals[j] = param;
            j++;
        }
    }
    locals.shrink(j);
}

levels remove_local_vars(parser const & p, levels const & ls) {
    return filter(ls, [&](level const & l) {
            return is_placeholder(l) || !is_param(l) || !p.is_local_level_variable(param_id(l));
        });
}

// TODO(Leo): delete these headers
void collect_annonymous_inst_implicit(parser const & p, collected_locals & locals);
void sort_locals(buffer<expr> const & locals, parser const & p, buffer<expr> & ps);

list<expr> locals_to_context(expr const & e, parser const & p) {
    collected_locals ls;
    collect_locals_ignoring_tactics(e, ls);
    collect_annonymous_inst_implicit(p, ls);
    buffer<expr> locals;
    sort_locals(ls.get_collected(), p, locals);
    std::reverse(locals.begin(), locals.end());
    return to_list(locals.begin(), locals.end());
}

expr mk_local_ref(name const & n, levels const & ctx_ls, unsigned num_ctx_params, expr const * ctx_params) {
    buffer<expr> params;
    for (unsigned i = 0; i < num_ctx_params; i++)
        params.push_back(mk_explicit(ctx_params[i]));
    return mk_as_atomic(mk_app(mk_explicit(mk_constant(n, ctx_ls)), params));
}

bool is_local_ref(expr const & e) {
    if (!is_as_atomic(e))
        return false;
    expr const & imp_arg = get_as_atomic_arg(e);
    buffer<expr> locals;
    expr const & f = get_app_args(imp_arg, locals);
    return
        is_explicit(f) &&
        is_constant(get_explicit_arg(f)) &&
        std::all_of(locals.begin(), locals.end(),
                    [](expr const & l) {
                        return is_explicit(l) && is_local(get_explicit_arg(l));
                    });
}

expr update_local_ref(expr const & e, name_set const & lvls_to_remove, name_set const & locals_to_remove) {
    lean_assert(is_local_ref(e));
    if (locals_to_remove.empty() && lvls_to_remove.empty())
        return e;
    buffer<expr> locals;
    expr const & f = get_app_args(get_as_atomic_arg(e), locals);
    lean_assert(is_explicit(f));

    expr new_f;
    if (!lvls_to_remove.empty()) {
        expr const & c = get_explicit_arg(f);
        lean_assert(is_constant(c));
        new_f = mk_explicit(update_constant(c, filter(const_levels(c), [&](level const & l) {
                        return is_placeholder(l) || (is_param(l) && !lvls_to_remove.contains(param_id(l)));
                    })));
    } else {
        new_f = f;
    }

    if (!locals_to_remove.empty()) {
        unsigned j = 0;
        for (unsigned i = 0; i < locals.size(); i++) {
            expr const & l = locals[i];
            if (!locals_to_remove.contains(mlocal_name(get_explicit_arg(l)))) {
                locals[j] = l;
                j++;
            }
        }
        locals.shrink(j);
    }

    if (locals.empty()) {
        return get_explicit_arg(new_f);
    } else {
        return mk_as_atomic(mk_app(new_f, locals));
    }
}

expr Fun(buffer<expr> const & locals, expr const & e, parser & p) {
    bool use_cache = false;
    return p.rec_save_pos(Fun(locals, e, use_cache), p.get_pos_info(e));
}

expr Fun(expr const & local, expr const & e, parser & p) {
    bool use_cache = false;
    return p.rec_save_pos(Fun(local, e, use_cache), p.get_pos_info(e));
}

expr Pi(buffer<expr> const & locals, expr const & e, parser & p) {
    bool use_cache = false;
    return p.rec_save_pos(Pi(locals, e, use_cache), p.get_pos_info(e));
}

expr Pi(expr const & local, expr const & e, parser & p) {
    bool use_cache = false;
    return p.rec_save_pos(Pi(local, e, use_cache), p.get_pos_info(e));
}

template<bool is_lambda>
static expr mk_binding_as_is(unsigned num, expr const * locals, expr const & b) {
    expr r     = abstract_locals(b, num, locals);
    unsigned i = num;
    while (i > 0) {
        --i;
        expr const & l = locals[i];
        expr t = abstract_locals(mlocal_type(l), i, locals);
        if (is_lambda)
            r = mk_lambda(mlocal_pp_name(l), mk_as_is(t), r, local_info(l));
        else
            r = mk_pi(mlocal_pp_name(l), mk_as_is(t), r, local_info(l));
    }
    return r;
}

expr Pi_as_is(buffer<expr> const & locals, expr const & e, parser & p) {
    return p.rec_save_pos(mk_binding_as_is<false>(locals.size(), locals.data(), e), p.get_pos_info(e));
}

expr Pi_as_is(expr const & local, expr const & e) {
    return mk_binding_as_is<false>(1, &local, e);
}

level mk_result_level(buffer<level> const & r_lvls) {
    if (r_lvls.empty()) {
        return mk_level_one();
    } else {
        level r = r_lvls[0];
        for (unsigned i = 1; i < r_lvls.size(); i++)
            r = mk_max(r, r_lvls[i]);
        r = normalize(r);
        if (is_not_zero(r))
            return normalize(r);
        else
            return normalize(mk_max(r, mk_level_one()));
    }
}

std::tuple<expr, level_param_names> parse_local_expr(parser & p, name const & decl_name, metavar_context & mctx, bool relaxed) {
    expr e = p.parse_expr();
    bool check_unassigend = !relaxed;
    expr new_e; level_param_names ls;
    std::tie(new_e, ls) = p.elaborate(decl_name, mctx, e, check_unassigend);
    level_param_names new_ls = to_level_param_names(collect_univ_params(new_e));
    return std::make_tuple(new_e, new_ls);
}

std::tuple<expr, level_param_names> parse_local_expr(parser & p, name const & decl_name, bool relaxed) {
    metavar_context mctx;
    return parse_local_expr(p, decl_name, mctx, relaxed);
}

optional<name> is_uniquely_aliased(environment const & env, name const & n) {
    if (auto it = is_expr_aliased(env, n))
        if (length(get_expr_aliases(env, *it)) == 1)
            return it;
    return optional<name>();
}

name get_decl_short_name(name const & d, environment const & env) {
    // using namespace override resolution rule
    list<name> const & ns_list = get_namespaces(env);
    for (name const & ns : ns_list) {
        if (is_prefix_of(ns, d) && ns != d)
            return d.replace_prefix(ns, name());
    }
    // if the alias is unique use it
    if (auto it = is_uniquely_aliased(env, d))
        return *it;
    else
        return d;
}

environment open_prec_aliases(environment const & env) {
    name prec("std", "prec");
    return overwrite_aliases(env, prec, name());
}

char const * open_binder_string(binder_info const & bi, bool unicode) {
    if (bi.is_implicit()) return "{";
    else if (bi.is_inst_implicit()) return "[";
    else if (bi.is_strict_implicit() && unicode) return "⦃";
    else if (bi.is_strict_implicit() && !unicode) return "{{";
    else return "(";
}

char const * close_binder_string(binder_info const & bi, bool unicode) {
    if (bi.is_implicit()) return "}";
    else if (bi.is_inst_implicit()) return "]";
    else if (bi.is_strict_implicit() && unicode) return "⦄";
    else if (bi.is_strict_implicit() && !unicode) return "}}";
    else return ")";
}

pair<name, option_kind> parse_option_name(parser & p, char const * error_msg) {
    auto id_pos  = p.pos();
    name id = p.check_id_next(error_msg, break_at_pos_exception::token_context::option);
    option_declarations decls = get_option_declarations();
    auto it = decls.find(id);
    if (!it) {
        // add "lean" prefix
        name lean_id = name("lean") + id;
        it = decls.find(lean_id);
        if (!it) {
            throw parser_error(sstream() << "unknown option '" << id
                               << "', type 'help options.' for list of available options", id_pos);
        } else {
            id = lean_id;
        }
    }
    return mk_pair(id, it->kind());
}

expr quote(unsigned u) {
    return mk_prenum(mpz(u));
}

expr quote(char const * str) {
    return from_string(str);
}

expr quote(name const & n) {
    switch (n.kind()) {
        case name_kind::ANONYMOUS:
            return mk_constant(get_name_anonymous_name());
        case name_kind::NUMERAL:
            return mk_app(mk_constant(get_name_mk_numeral_name()), quote(n.get_numeral()), quote(n.get_prefix()));
        case name_kind::STRING:
            return mk_app(mk_constant(get_name_mk_string_name()), quote(n.get_string()), quote(n.get_prefix()));
    }
    lean_unreachable();
}

static name * g_no_info = nullptr;
name const & get_no_info() { return *g_no_info; }

expr mk_no_info(expr const & e) { return mk_annotation(get_no_info(), e); }
bool is_no_info(expr const & e) { return is_annotation(e, get_no_info()); }

expr mk_opt_param(expr const & t, expr const & val) {
    return copy_tag(val, mk_app(copy_tag(val, mk_constant(get_opt_param_name())), t, val));
}

expr mk_auto_param(expr const & t, name const & tac_name) {
    return copy_tag(t, mk_app(copy_tag(t, mk_constant(get_auto_param_name())), t, quote(tac_name)));
}

static bool is_tactic_unit(environment const & env, expr const & c) {
    type_checker tc(env);
    return tc.is_def_eq(tc.infer(c), mk_tactic_unit());
}

expr parse_auto_param(parser & p, expr const & type) {
    p.next();
    auto pos      = p.pos();
    name tac_id   = p.check_decl_id_next("invalid auto_param, identifier expected");
    if (get_auto_param_check_exists(p.get_options())) {
        expr tac_expr = p.id_to_expr(tac_id, pos, true);
        if (!is_tactic_unit(p.env(), tac_expr))
            throw parser_error(sstream() << "invalid auto_param, '" << tac_id << "' must have type (tactic unit)", pos);
        return mk_auto_param(type, const_name(tac_expr));
    } else {
        return mk_auto_param(type, tac_id);
    }
}

static name * g_frozen_name = nullptr;

expr mk_frozen_name_annotation(expr const & e) {
    return mk_annotation(*g_frozen_name, e);
}

bool is_frozen_name(expr const & e) {
    return is_annotation(e, *g_frozen_name);
}

expr freeze_names(expr const & e) {
    return replace(e, [&](expr const e, unsigned) {
            if (is_constant(e))
                return some_expr(mk_frozen_name_annotation(e));
            else
                return none_expr();
        });
}

static name * g_field_notation_name          = nullptr;
static std::string * g_field_notation_opcode = nullptr;

[[ noreturn ]] static void throw_pn_ex() { throw exception("unexpected occurrence of field notation expression"); }

class field_notation_macro_cell : public macro_definition_cell {
    name     m_field;
    unsigned m_field_idx;
public:
    field_notation_macro_cell(name const & f):m_field(f), m_field_idx(0) {}
    field_notation_macro_cell(unsigned fidx):m_field_idx(fidx) {}
    virtual name get_name() const override { return *g_field_notation_name; }
    virtual expr check_type(expr const &, abstract_type_context &, bool) const override { throw_pn_ex(); }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override { throw_pn_ex(); }
    virtual void write(serializer & s) const override { s << *g_field_notation_opcode << m_field << m_field_idx; }
    bool is_anonymous() const { return m_field.is_anonymous(); }
    name const & get_field_name() const { lean_assert(!is_anonymous()); return m_field; }
    unsigned get_field_idx() const { lean_assert(is_anonymous()); return m_field_idx; }
    virtual bool operator==(macro_definition_cell const & other) const override {
        if (auto other_ptr = dynamic_cast<field_notation_macro_cell const *>(&other)) {
            return m_field == other_ptr->m_field && m_field_idx == other_ptr->m_field_idx;
        } else {
            return false;
        }
    }
};

expr mk_field_notation(expr const & e, name const & field) {
    macro_definition def(new field_notation_macro_cell(field));
    return mk_macro(def, 1, &e);
}

expr mk_field_notation_compact(expr const & e, char const * field) {
    name fname(field);
    if (is_choice(e)) {
        buffer<expr> new_es;
        for (unsigned i = 0; i < get_num_choices(e); i++) {
            expr const & c = get_choice(e, i);
            new_es.push_back(copy_tag(c, mk_field_notation(c, fname)));
        }
        return mk_choice(new_es.size(), new_es.data());
    } else {
        return mk_field_notation(e, fname);
    }
}

expr mk_field_notation(expr const & e, unsigned fidx) {
    macro_definition def(new field_notation_macro_cell(fidx));
    return mk_macro(def, 1, &e);
}

bool is_field_notation(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_field_notation_name;
}

bool is_anonymous_field_notation(expr const & e) {
    lean_assert(is_field_notation(e));
    return static_cast<field_notation_macro_cell const*>(macro_def(e).raw())->is_anonymous();
}

name const & get_field_notation_field_name(expr const & e) {
    lean_assert(is_field_notation(e));
    return static_cast<field_notation_macro_cell const*>(macro_def(e).raw())->get_field_name();
}

unsigned get_field_notation_field_idx(expr const & e) {
    lean_assert(is_field_notation(e));
    return static_cast<field_notation_macro_cell const*>(macro_def(e).raw())->get_field_idx();
}

void initialize_frontend_lean_util() {
    g_no_info = new name("no_info");
    register_annotation(*g_no_info);
    g_frozen_name = new name("frozen_name");
    register_annotation(*g_frozen_name);
    g_auto_param_check_exists = new name({"auto_param", "check_exists"});
    register_bool_option(*g_auto_param_check_exists, LEAN_DEFAULT_AUTO_PARAM_CHECK_EXISTS,
                         "Eagerly check that a tactic declaration of the given name exists when declaring an auto param");
    g_field_notation_name   = new name("field_notation");
    g_field_notation_opcode = new std::string("fieldN");
    register_macro_deserializer(*g_field_notation_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    name fname; unsigned fidx;
                                    d >> fname >> fidx;
                                    if (fname.is_anonymous())
                                        return mk_field_notation(args[0], fidx);
                                    else
                                        return mk_field_notation(args[0], fname);
                                });
}

environment compile_expr(environment const & env, name const & n, level_param_names const & ls, expr const & type, expr const & e, pos_info const & pos) {
    environment new_env = env;
    bool use_conv_opt   = true;
    bool is_trusted     = false;
    auto cd = check(new_env, mk_definition(new_env, n, ls, type, e, use_conv_opt, is_trusted));
    new_env = new_env.add(cd);
    new_env = add_transient_decl_pos_info(new_env, n, pos);
    return vm_compile(new_env, new_env.get(n));
}

vm_obj eval_closed_expr(environment const & env, name const & n, expr const & type, expr const & e, pos_info const & pos) {
    environment new_env = compile_expr(env, n, {}, type, e, pos);
    vm_state vm(new_env, {});
    return vm.invoke(n, 0, nullptr);
}

static expr save_pos(parser * p, expr const & e, optional<pos_info> const & pos) {
    if (pos)
        return p->save_pos(e, *pos);
    else
        return e;
}

static expr mk_lean_list(parser * p, buffer<expr> const & es, optional<pos_info> const & pos) {
    expr r = save_pos(p, mk_constant(get_list_nil_name()), pos);
    unsigned i = es.size();
    while (i > 0) {
        --i;
        r = save_pos(p, mk_app(save_pos(p, mk_constant(get_list_cons_name()), pos), es[i], r), pos);
    }
    return r;
}

expr mk_lean_list(parser & p, buffer<expr> const & es, pos_info const & pos) {
    return mk_lean_list(&p, es, optional<pos_info>(pos));
}

expr mk_lean_list(buffer<expr> const & es) {
    return mk_lean_list(nullptr, es, optional<pos_info>());
}

void finalize_frontend_lean_util() {
    delete g_auto_param_check_exists;
    delete g_no_info;
    delete g_frozen_name;
    delete g_field_notation_opcode;
    delete g_field_notation_name;
}
}
