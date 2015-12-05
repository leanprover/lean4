/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/locals.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/replace_visitor.h"
#include "library/module.h"
#include "library/aliases.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/nested_declaration.h"

namespace lean {
static name * g_nested_decl = nullptr;
static std::string * g_nested_decl_opcode = nullptr;

name const & get_nested_decl_name() { return *g_nested_decl; }
std::string const & get_nested_decl_opcode() { return *g_nested_decl_opcode; }

class nested_decl_macro_definition_cell : public macro_definition_cell {
    optional<name>  m_name;
    decl_attributes m_attributes;

    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid nested declaration, incorrect number of arguments");
    }
public:
    nested_decl_macro_definition_cell(optional<name> const & n, decl_attributes const & attrs):
        m_name(n), m_attributes(attrs) {}
    virtual name get_name() const { return get_nested_decl_name(); }
    virtual pair<expr, constraint_seq> check_type(expr const & m, extension_context & ctx, bool infer_only) const {
        check_macro(m);
        return ctx.check_type(macro_arg(m, 0), infer_only);
    }
    virtual optional<expr> expand(expr const & m, extension_context &) const {
        check_macro(m);
        return some_expr(macro_arg(m, 0));
    }
    virtual void write(serializer & s) const {
        s.write_string(get_nested_decl_opcode());
        s << m_name;
        m_attributes.write(s);
    }
    virtual unsigned hash() const {
        return get_nested_decl_name().hash();
    }
    optional<name> const & get_decl_name() const { return m_name; }
    decl_attributes const & get_decl_attributes() const { return m_attributes; }
};

expr mk_nested_declaration(optional<name> const & n, decl_attributes const & attrs, expr const & e) {
    macro_definition def(new nested_decl_macro_definition_cell(n, attrs));
    return mk_macro(def, 1, &e);
}

bool is_nested_declaration(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == get_nested_decl_name();
}

expr update_nested_declaration(expr const & e, expr const & new_d) {
    lean_assert(is_nested_declaration(e));
    return mk_macro(macro_def(e), 1,  &new_d);
}

expr get_nested_declaration_arg(expr const & e) {
    lean_assert(is_nested_declaration(e));
    return macro_arg(e, 0);
}

optional<name> const & get_nested_declaration_name(expr const & d) {
    lean_assert(is_nested_declaration(d));
    return static_cast<nested_decl_macro_definition_cell const*>(macro_def(d).raw())->get_decl_name();
}

decl_attributes const & get_nested_declaration_attributes(expr const & d) {
    lean_assert(is_nested_declaration(d));
    return static_cast<nested_decl_macro_definition_cell const*>(macro_def(d).raw())->get_decl_attributes();
}

LEAN_THREAD_VALUE(bool, g_allow_nested_declarations, false);

allow_nested_decls_scope::allow_nested_decls_scope(bool enable) {
    m_saved = g_allow_nested_declarations;
    g_allow_nested_declarations = enable;
}

allow_nested_decls_scope::~allow_nested_decls_scope() {
    g_allow_nested_declarations = m_saved;
}

expr parse_nested_declaration(parser & p, unsigned, expr const *, pos_info const & pos) {
    try {
        optional<name> n;
        decl_attributes attrs;
        if (!g_allow_nested_declarations)
            throw parser_error("invalid 'abstract' expression, it is only allowed inside definitions", pos);
        if (p.curr_is_token(get_as_tk())) {
            p.next();
            n = p.check_id_next("invalid 'abstract' expression, identifier expected");
        }
        attrs.parse(p);
        expr e = p.parse_expr();
        p.check_token_next(get_end_tk(), "invalid 'abstract' expression, 'end' expected");
        return p.save_pos(mk_nested_declaration(n, attrs, e), pos);
    } catch (exception & ex) {
        consume_until_end(p);
        ex.rethrow();
        lean_unreachable();
    }
}

bool contains_nested_declarations(expr const & e) {
    return static_cast<bool>(find(e, [&](expr const & n, unsigned) { return is_nested_declaration(n); }));
}

class extractor : public replace_visitor {
    environment  m_env;
    io_state     m_ios;
    type_checker m_tc;
    name         m_dname;
    unsigned     m_idx;
public:
    extractor(environment const & env, io_state const & ios, name const & dname):
        m_env(env), m_ios(ios), m_tc(m_env), m_dname(dname), m_idx(1) {}

    name mk_name_for(expr const & e) {
        lean_assert(is_nested_declaration(e));
        if (auto n = get_nested_declaration_name(e)) {
            return *n;
        } else {
            name ns  = get_namespace(m_env);
            while (true) {
                name aux = m_dname.append_after(m_idx);
                m_idx++;
                if (!m_env.find(ns + aux))
                    return aux;
            }
        }
    }

    expr extract(expr const & e) {
        lean_assert(is_nested_declaration(e));
        expr const & d = visit(get_nested_declaration_arg(e));
        name new_name      = mk_name_for(e);
        name new_real_name = get_namespace(m_env) + new_name;
        collected_locals locals;
        collect_locals(d, locals);
        buffer<name> uparams;
        collect_univ_params(d).to_buffer(uparams);
        expr new_value           = Fun(locals.get_collected(), d);
        expr new_type            = m_tc.infer(new_value).first;
        level_param_names new_ps = to_list(uparams);
        levels ls                = param_names_to_levels(new_ps);
        m_env = module::add(m_env, check(m_env, mk_definition(m_env, new_real_name, new_ps,
                                                              new_type, new_value)));
        if (new_name != new_real_name)
            m_env = add_expr_alias_rec(m_env, new_name, new_real_name);
        decl_attributes const & attrs = get_nested_declaration_attributes(e);
        m_env = attrs.apply(m_env, m_ios, new_real_name, get_namespace(m_env));
        return mk_app(mk_constant(new_real_name, ls), locals.get_collected());
    }

    expr visit_macro(expr const & e) {
        if (is_nested_declaration(e)) {
            return extract(e);
        } else {
            return replace_visitor::visit_macro(e);
        }
    }

    expr visit_binding(expr const & b) {
        expr new_domain = visit(binding_domain(b));
        expr l          = mk_local(m_tc.mk_fresh_name(), new_domain);
        expr new_body   = abstract(visit(instantiate(binding_body(b), l)), l);
        return update_binding(b, new_domain, new_body);
    }

    environment const & get_env() const { return m_env; }
};

std::tuple<environment, expr> extract_nested_declarations(environment const & env, io_state const & ios,
                                                          name const & dname, expr const & e) {
    if (contains_nested_declarations(e)) {
        extractor ex(env, ios, dname);
        expr new_e = ex(e);
        return std::make_tuple(ex.get_env(), new_e);
    } else {
        return std::make_tuple(env, e);
    }
}

void initialize_nested_declaration() {
    g_nested_decl        = new name("nested_decl");
    g_nested_decl_opcode = new std::string("NDecl");
    register_macro_deserializer(get_nested_decl_opcode(),
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    optional<name> n; decl_attributes attrs;
                                    d >> n; attrs.read(d);
                                    return mk_nested_declaration(n, attrs, args[0]);
                                });
}
void finalize_nested_declaration() {
    delete g_nested_decl;
    delete g_nested_decl_opcode;
}
}
