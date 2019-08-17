/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/option_declarations.h"
#include "util/io.h"
#include "util/array_ref.h"
#include "kernel/replace_fn.h"
#include "library/constants.h"
#include "library/class.h"
#include "library/num.h"
#include "library/sorry.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"
#include "frontends/lean/typed_expr.h"

namespace lean {
// ==========================================
// New attribute manager API
extern "C" object* lean_is_attribute(object* n, object* w);
extern "C" object* lean_attribute_application_time(object* n, object* w);
extern "C" object* lean_add_attribute(object* env, object* decl, object* attr, object* args, uint8 persistent, object *w);
extern "C" object* lean_add_scoped_attribute(object* env, object* decl, object* attr, object* args, object *w);
extern "C" object* lean_erase_attribute(object* env, object* decl, object* attr, uint8 persistent, object *w);

bool is_new_attribute(name const & n) {
    return get_io_scalar_result<bool>(lean_is_attribute(n.to_obj_arg(), io_mk_world()));
}
environment add_attribute(environment const & env, name const & decl, name const & attr, syntax const & args, bool persistent) {
    return get_io_result<environment>(lean_add_attribute(env.to_obj_arg(), decl.to_obj_arg(), attr.to_obj_arg(), args.to_obj_arg(), persistent, io_mk_world()));
}
environment add_scoped_attribute(environment const & env, name const & decl, name const & attr, syntax const & args) {
    return get_io_result<environment>(lean_add_scoped_attribute(env.to_obj_arg(), decl.to_obj_arg(), attr.to_obj_arg(), args.to_obj_arg(), io_mk_world()));
}
environment erase_attribute(environment const & env, name const & decl, name const & attr, bool persistent) {
    return get_io_result<environment>(lean_erase_attribute(env.to_obj_arg(), decl.to_obj_arg(), attr.to_obj_arg(), persistent, io_mk_world()));
}
/*
inductive AttributeApplicationTime
| afterTypeChecking | afterCompilation
*/
bool is_after_compilation_attribute(name const & n) {
    return get_io_scalar_result<uint8>(lean_attribute_application_time(n.to_obj_arg(), io_mk_world())) == 1;
}
// ==========================================

expr decl_attributes::parse_attr_arg(parser & p, name const & attr_id) {
    parser::undef_id_to_local_scope scope(p);
    expr e = mk_const(attr_id);
    while (!p.curr_is_token("]") && !p.curr_is_token(",")) {
        expr arg = p.parse_expr(get_max_prec());
        if (has_sorry(arg))
            break;
        e = mk_app(e, arg);
    }
    // the new frontend uses consts instead of locals for unknown names...
    return replace(e, [](expr const & e) {
            if (is_local(e))
                return some_expr(mk_const(local_name(e)));
            return none_expr();
        });
}

extern "C" object* lean_mk_syntax_atom(object*);
extern "C" object* lean_mk_syntax_ident(object*);
extern "C" object* lean_mk_syntax_list(object*);
extern "C" object* lean_mk_syntax_str_lit(object*);
extern "C" object* lean_mk_syntax_num_lit(object*);

syntax mk_syntax_atom(string_ref const & s) { return syntax(lean_mk_syntax_atom(s.to_obj_arg())); }
syntax mk_syntax_ident(name const & n) { return syntax(lean_mk_syntax_ident(n.to_obj_arg())); }
syntax mk_syntax_list(buffer<syntax> const & args) { return syntax(lean_mk_syntax_list(to_array(args))); }
syntax mk_syntax_str_lit(string_ref const & s) { return syntax(lean_mk_syntax_str_lit(s.to_obj_arg())); }
syntax mk_syntax_num_lit(nat const & n) { return syntax(lean_mk_syntax_num_lit(n.to_obj_arg())); }

syntax decl_attributes::expr_to_syntax(expr const & e) {
    buffer<expr> args;
    get_app_args(e, args);
    buffer<syntax> new_args;
    for (expr arg : args) {
        while (is_mdata(arg)) {
            arg = mdata_expr(arg);
        }
        if (is_constant(arg)) {
            new_args.push_back(mk_syntax_ident(const_name(arg)));
        } else if (is_lit(arg)) {
            literal const & val = lit_value(arg);
            switch (val.kind()) {
            case literal_kind::Nat:
                new_args.push_back(mk_syntax_num_lit(val.get_nat()));
                break;
            case literal_kind::String:
                new_args.push_back(mk_syntax_str_lit(val.get_string()));
                break;
            }
        } else {
            throw exception("unsupported kind of attribute parameter");
        }
    }
    switch (new_args.size()) {
    case 0:
        return syntax(box(0));
    default:
        return mk_syntax_list(new_args);
    }
}

void decl_attributes::parse_core(parser & p, bool compact) {
    while (true) {
        auto pos = p.pos();
        bool scoped  = p.curr_is_token_or_id(get_scoped_tk());
        if (scoped) {
            p.next();
        }
        bool deleted = p.curr_is_token_or_id(get_sub_tk());
        if (deleted) {
            if (m_persistent)
                throw parser_error("cannot remove attribute globally (solution: use 'local attribute')", pos);
            if (scoped)
                throw parser_error("cannot remove scoped attribute", pos);
            p.next();
        }
        name id;
        if (p.curr_is_command()) {
            id = p.get_token_info().value();
            p.next();
        } else {
            id = p.check_id_next("invalid attribute declaration, identifier expected");
        }
        if (is_new_attribute(id)) {
            syntax args(box(0));
            if (!deleted) {
                expr e = parse_attr_arg(p, id);
                args = expr_to_syntax(e);
            }
            if (is_after_compilation_attribute(id)) {
                m_after_comp_entries = cons({id, deleted, scoped, args}, m_after_comp_entries);
            } else {
                m_after_tc_entries = cons({id, deleted, scoped, args}, m_after_tc_entries);
            }
        } else {
            throw parser_error(sstream() << "unknown attribute [" << id << "]", pos);
        }
        if (p.curr_is_token(get_comma_tk())) {
            p.next();
        } else {
            p.check_token_next(get_rbracket_tk(), "invalid attribute declaration, ']' expected");
            if (compact)
                break;
            if (p.curr_is_token(get_lbracket_tk()))
                p.next();
            else
                break;
        }
    }
}

void decl_attributes::parse(parser & p) {
    if (!p.curr_is_token(get_lbracket_tk()))
        return;
    p.next();
    parse_core(p, false);
}

void decl_attributes::parse_compact(parser & p) {
    parse_core(p, true);
}

void decl_attributes::set_attribute(environment const & /* env */, name const & attr_name) {
    if (is_new_attribute(attr_name)) {
        // Temporary Hack... ignore attr_data_ptr
        syntax args(box(0));
        if (is_after_compilation_attribute(attr_name)) {
            m_after_comp_entries = cons({attr_name, false, false, args}, m_after_comp_entries);
        } else {
            m_after_tc_entries = cons({attr_name, false, false, args}, m_after_tc_entries);
        }
    } else {
        throw exception(sstream() << "unknown attribute [" << attr_name << "]");
    }
}

bool decl_attributes::has_attribute(list<new_entry> const & entries, name const & attr_name) const {
    for (auto entry : entries) {
        if (entry.m_attr == attr_name)
            return true;
    }
    return false;
}

bool decl_attributes::has_attribute(environment const & /* env */, name const & attr_name) const {
    if (is_new_attribute(attr_name)) {
        return has_attribute(m_after_tc_entries, attr_name) || has_attribute(m_after_comp_entries, attr_name);
    } else {
        throw exception(sstream() << "unknown attribute [" << attr_name << "]");
    }
}

environment decl_attributes::apply_new_entries(environment env, list<new_entry> const & es, name const & d) const {
    buffer<new_entry> new_entries;
    to_buffer(es, new_entries);
    unsigned i = new_entries.size();
    while (i > 0) {
        --i;
        auto const & entry = new_entries[i];
        if (entry.m_deleted) {
            env = erase_attribute(env, d, entry.m_attr, m_persistent);
        } else if (entry.m_scoped) {
            env = add_scoped_attribute(env, d, entry.m_attr, entry.m_args);
        } else {
            env = add_attribute(env, d, entry.m_attr, entry.m_args, m_persistent);
        }
    }
    return env;
}

environment decl_attributes::apply_after_tc(environment env, io_state const & /* ios */, name const & d) const {
    return apply_new_entries(env, m_after_tc_entries, d);
}

environment decl_attributes::apply_after_comp(environment env, name const & d) const {
    return apply_new_entries(env, m_after_comp_entries, d);
}

environment decl_attributes::apply_all(environment env, io_state const & ios, name const & d) const {
    environment new_env = apply_after_tc(env, ios, d);
    return apply_after_comp(new_env, d);
}

bool decl_attributes::ok_for_inductive_type() const {
    for (new_entry const & e : m_after_tc_entries) {
        if (e.m_attr != "class" || e.m_deleted)
            return false;
    }
    return true;
}

bool decl_attributes::has_class() const {
    for (new_entry const & e : m_after_tc_entries)
        if (e.m_attr == "class" && !e.m_deleted)
            return true;
    return false;
}

void initialize_decl_attributes() {
}

void finalize_decl_attributes() {
}
}
