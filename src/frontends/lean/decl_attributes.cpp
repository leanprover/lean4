/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/option_declarations.h"
#include "util/io.h"
#include "util/array_ref.h"
#include "kernel/replace_fn.h"
#include "library/attribute_manager.h"
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
object* is_attribute_core(object* n, object* w);
object* attribute_application_time_core(object* n, object* w);
object* add_attribute_core(object* env, object* decl, object* attr, object* args, uint8 persistent, object *w);
object* add_scoped_attribute_core(object* env, object* decl, object* attr, object* args, object *w);
object* erase_attribute_core(object* env, object* decl, object* attr, uint8 persistent, object *w);

bool is_new_attribute(name const & n) {
    return get_io_scalar_result<bool>(is_attribute_core(n.to_obj_arg(), io_mk_world()));
}
environment add_attribute(environment const & env, name const & decl, name const & attr, syntax const & args, bool persistent) {
    return get_io_result<environment>(add_attribute_core(env.to_obj_arg(), decl.to_obj_arg(), attr.to_obj_arg(), args.to_obj_arg(), persistent, io_mk_world()));
}
environment add_scoped_attribute(environment const & env, name const & decl, name const & attr, syntax const & args) {
    return get_io_result<environment>(add_scoped_attribute_core(env.to_obj_arg(), decl.to_obj_arg(), attr.to_obj_arg(), args.to_obj_arg(), io_mk_world()));
}
environment erase_attribute(environment const & env, name const & decl, name const & attr, bool persistent) {
    return get_io_result<environment>(erase_attribute_core(env.to_obj_arg(), decl.to_obj_arg(), attr.to_obj_arg(), persistent, io_mk_world()));
}
/*
inductive AttributeApplicationTime
| afterTypeChecking | afterCompilation
*/
bool is_after_compilation_attribute(name const & n) {
    return get_io_scalar_result<uint8>(attribute_application_time_core(n.to_obj_arg(), io_mk_world())) == 1;
}
// ==========================================


// ==========================================
// configuration options
static name * g_default_priority = nullptr;

unsigned get_default_priority(options const & opts) {
    return opts.get_unsigned(*g_default_priority, LEAN_DEFAULT_PRIORITY);
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

object* mk_syntax_atom_core(object*);
object* mk_syntax_ident_core(object*);
object* mk_syntax_list_core(object*);
object* mk_syntax_str_lit_core(object*);
object* mk_syntax_num_lit_core(object*);

syntax mk_syntax_atom(string_ref const & s) { return syntax(mk_syntax_atom_core(s.to_obj_arg())); }
syntax mk_syntax_ident(name const & n) { return syntax(mk_syntax_ident_core(n.to_obj_arg())); }
syntax mk_syntax_list(buffer<syntax> const & args) { return syntax(mk_syntax_list_core(to_array(args))); }
syntax mk_syntax_str_lit(string_ref const & s) { return syntax(mk_syntax_str_lit_core(s.to_obj_arg())); }
syntax mk_syntax_num_lit(nat const & n) { return syntax(mk_syntax_num_lit_core(n.to_obj_arg())); }

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
    case 1:
        return new_args[0];
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
        if (is_attribute(p.env(), id)) {
            /* Old attribute manager */
            if (scoped) {
                throw parser_error("old attribute manager does not support scoped attributes", pos);
            }
            auto const & attr = ::lean::get_attribute(p.env(), id);
            if (!deleted) {
                for (auto const & entry : m_entries) {
                    if (!entry.deleted() && are_incompatible(*entry.m_attr, attr)) {
                        throw parser_error(sstream() << "invalid attribute [" << id
                                           << "], declaration was already marked with ["
                                           << entry.m_attr->get_name()
                                           << "]", pos);
                    }
                }
            }
            attr_data_ptr data;
            if (!deleted) {
                expr e = parse_attr_arg(p, id);
                data = attr.parse_data(e);
            }
            m_entries = cons({&attr, data}, m_entries);
        } else if (is_new_attribute(id)) {
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

void decl_attributes::set_attribute(environment const & env, name const & attr_name, attr_data_ptr data) {
    if (is_attribute(env, attr_name)) {
        auto const & attr = ::lean::get_attribute(env, attr_name);
        entry e = {&attr, data};
        m_entries = append(m_entries, to_list(e));
    } else if (is_new_attribute(attr_name)) {
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

attr_data_ptr decl_attributes::get_attribute(environment const & env, name const & attr_name) const {
    if (!is_attribute(env, attr_name))
        throw exception(sstream() << "unknown attribute [" << attr_name << "]");
    auto const & attr = ::lean::get_attribute(env, attr_name);
    for (entry const & e : m_entries) {
        if (e.m_attr == &attr)
            return e.m_params;
    }
    return nullptr;
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

environment decl_attributes::apply_after_tc(environment env, io_state const & ios, name const & d) const {
    buffer<entry> entries;
    to_buffer(m_entries, entries);
    unsigned i = entries.size();
    while (i > 0) {
        --i;
        auto const & entry = entries[i];
        if (entry.deleted()) {
            if (!entry.m_attr->is_instance(env, d))
                throw exception(sstream() << "cannot remove attribute [" << entry.m_attr->get_name()
                                          << "]: no prior declaration on " << d);
            env = entry.m_attr->unset(env, ios, d, m_persistent);
        } else {
            unsigned prio = get_default_priority(ios.get_options());
            env = entry.m_attr->set_untyped(env, ios, d, prio, entry.m_params, m_persistent);
        }
    }
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
    for (entry const & e : m_entries) {
        name const & n = e.m_attr->get_name();
        if (is_system_attribute(n)) {
            if (n != "class" || e.deleted())
                return false;
        }
    }
    return true;
}

bool decl_attributes::has_class() const {
    for (entry const & e : m_entries)
        if (e.m_attr->get_name() == "class" && !e.deleted())
            return true;
    return false;
}

void initialize_decl_attributes() {
    g_default_priority = new name{"default_priority"};
    register_unsigned_option(*g_default_priority, LEAN_DEFAULT_PRIORITY, "default priority for attributes");
}

void finalize_decl_attributes() {
    delete g_default_priority;
}
}
