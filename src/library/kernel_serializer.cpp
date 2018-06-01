/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/object_serializer.h"
#include "kernel/expr.h"
#include "kernel/declaration.h"
#include "library/kernel_serializer.h"

// Procedures for serializing and deserializing kernel objects (levels, exprs, declarations)
namespace lean {
// Expression serialization
typedef std::unordered_map<std::string, macro_definition_cell::reader> macro_readers;
static macro_readers * g_macro_readers = nullptr;

macro_readers & get_macro_readers() {
    return *g_macro_readers;
}

void register_macro_deserializer(std::string const & k, macro_definition_cell::reader rd) {
    macro_readers & readers = get_macro_readers();
    lean_assert(readers.find(k) == readers.end());
    readers[k] = rd;
}

static expr read_macro_definition(deserializer & d, unsigned num, expr const * args) {
    auto k  = d.read_string();
    macro_readers & readers = get_macro_readers();
    auto it = readers.find(k);
    if (it == readers.end()) throw corrupted_stream_exception();
    return it->second(d, num, args);
}

serializer & operator<<(serializer & s, binder_info const & i) {
    unsigned w =
        (i.is_rec() ?             8 : 0) +
        (i.is_implicit() ?        4 : 0) +
        (i.is_strict_implicit() ? 2 : 0) +
        (i.is_inst_implicit() ?   1 : 0);
    s.write_char(w);
    return s;
}

static binder_info read_binder_info(deserializer & d) {
    unsigned w = d.read_char();
    bool rec   = (w & 8) != 0;
    bool imp   = (w & 4)  != 0;
    bool s_imp = (w & 2)  != 0;
    bool i_imp = (w & 1)  != 0;
    return binder_info(imp, s_imp, i_imp, rec);
}

static name * g_binder_name = nullptr;

class expr_serializer : public object_serializer<expr, expr_hash, is_bi_equal_proc> {
    typedef object_serializer<expr, expr_hash, is_bi_equal_proc> super;
    unsigned       m_next_id;

    void write_binder_name(serializer & s, name const & a) {
        // make sure binding names are atomic string
        if (!a.is_atomic() || a.is_numeral()) {
            s << g_binder_name->append_after(m_next_id);
            m_next_id++;
        } else {
            s << a;
        }
    }

    void write_core(expr const & a) {
        auto k = a.kind();
        super::write_core(a, static_cast<char>(k), [&]() {
                serializer & s = get_owner();
                switch (k) {
                case expr_kind::Var:
                    s << var_idx(a);
                    break;
                case expr_kind::Constant:
                    lean_assert(!const_name(a).is_anonymous());
                    s << const_name(a) << const_levels(a);
                    break;
                case expr_kind::Sort:
                    s << sort_level(a);
                    break;
                case expr_kind::Macro:
                    s << macro_num_args(a);
                    for (unsigned i = 0; i < macro_num_args(a); i++) {
                        write_core(macro_arg(a, i));
                    }
                    macro_def(a).write(s);
                    break;
                case expr_kind::App:
                    write_core(app_fn(a)); write_core(app_arg(a));
                    break;
                case expr_kind::Lambda: case expr_kind::Pi:
                    lean_assert(!binding_name(a).is_anonymous());
                    write_binder_name(s, binding_name(a));
                    s << binding_info(a); write_core(binding_domain(a)); write_core(binding_body(a));
                    break;
                case expr_kind::Let:
                    s << let_name(a);
                    write_core(let_type(a)); write_core(let_value(a)); write_core(let_body(a));
                    break;
                case expr_kind::Meta:
                    lean_assert(!mlocal_name(a).is_anonymous());
                    s << mlocal_name(a) << mlocal_pp_name(a); write_core(mlocal_type(a));
                    break;
                case expr_kind::Local:
                    lean_assert(!mlocal_name(a).is_anonymous());
                    lean_assert(!mlocal_pp_name(a).is_anonymous());
                    s << mlocal_name(a) << mlocal_pp_name(a) << local_info(a); write_core(mlocal_type(a));
                    break;
                }
            });
    }
public:
    expr_serializer() { m_next_id = 0; }
    void write(expr const & a) {
        write_core(a);
    }
};

class expr_deserializer : public object_deserializer<expr> {
    typedef object_deserializer<expr> super;
public:
    expr read_binding(expr_kind k) {
        deserializer & d   = get_owner();
        name n             = read_name(d);
        binder_info i      = read_binder_info(d);
        expr t             = read();
        return mk_binding(k, n, t, read(), i);
    }

    expr read() {
        return super::read_core([&](char c) {
                deserializer & d = get_owner();
                auto k = static_cast<expr_kind>(c);
                switch (k) {
                case expr_kind::Var:
                    return mk_var(d.read_unsigned());
                case expr_kind::Constant: {
                    auto n = read_name(d);
                    return mk_constant(n, read_levels(d));
                }
                case expr_kind::Sort:
                    return mk_sort(read_level(d));
                case expr_kind::Macro: {
                    unsigned n = d.read_unsigned();
                    buffer<expr> args;
                    for (unsigned i = 0; i < n; i++) {
                        args.push_back(read());
                    }
                    return read_macro_definition(d, args.size(), args.data());
                }
                case expr_kind::App: {
                    expr f = read();
                    return mk_app(f, read());
                }
                case expr_kind::Lambda: case expr_kind::Pi:
                    return read_binding(k);
                case expr_kind::Let: {
                    name n = read_name(d);
                    expr t = read();
                    expr v = read();
                    return mk_let(n, t, v, read());
                }
                case expr_kind::Meta: {
                    name n    = read_name(d);
                    name pp_n = read_name(d);
                    return mk_metavar(n, pp_n, read());
                }
                case expr_kind::Local: {
                    name n         = read_name(d);
                    name pp_n      = read_name(d);
                    binder_info bi = read_binder_info(d);
                    return mk_local(n, pp_n, read(), bi);
                }}
                throw corrupted_stream_exception(); // LCOV_EXCL_LINE
            });
    }
};

struct expr_sd {
    unsigned m_s_extid;
    unsigned m_d_extid;
    expr_sd() {
        m_s_extid = serializer::register_extension([](){ return std::unique_ptr<serializer::extension>(new expr_serializer()); });
        m_d_extid = deserializer::register_extension([](){ return std::unique_ptr<deserializer::extension>(new expr_deserializer()); });
    }
};
static expr_sd * g_expr_sd = nullptr;

serializer & operator<<(serializer & s, expr const & n) {
    s.get_extension<expr_serializer>(g_expr_sd->m_s_extid).write(n);
    return s;
}

expr read_expr(deserializer & d) {
    return d.get_extension<expr_deserializer>(g_expr_sd->m_d_extid).read();
}

serializer & operator<<(serializer & s, reducibility_hints const & h) {
    s << static_cast<char>(h.get_kind());
    if (h.is_regular())
        s << static_cast<char>(h.use_self_opt()) << h.get_height();
    return s;
}

reducibility_hints read_hints(deserializer & d) {
    char k;
    d >> k;
    reducibility_hints::kind kind = static_cast<reducibility_hints::kind>(k);
    if (kind == reducibility_hints::Regular) {
        char use_conv; unsigned height;
        d >> use_conv >> height;
        return reducibility_hints::mk_regular(height, static_cast<bool>(use_conv));
    } else if (kind == reducibility_hints::Opaque) {
        return reducibility_hints::mk_opaque();
    } else {
        return reducibility_hints::mk_abbreviation();
    }
}

// Declaration serialization
level_param_names read_level_params(deserializer & d) { return read_names(d); }
serializer & operator<<(serializer & s, declaration const & d) {
    char k = 0;
    if (d.is_definition())
        k |= 1;
    if (d.is_theorem() || d.is_axiom())
        k |= 2;
    if (d.is_meta())
        k |= 4;
    s << k << d.get_name() << d.get_univ_params() << d.get_type();
    if (d.is_definition()) {
        s << d.get_value();
        if (!d.is_theorem())
            s << d.get_hints();
    }
    return s;
}

declaration read_declaration(deserializer & d) {
    char k               = d.read_char();
    bool has_value       = (k & 1) != 0;
    bool is_th_ax        = (k & 2) != 0;
    bool is_meta         = (k & 4) != 0;
    name n               = read_name(d);
    level_param_names ps = read_level_params(d);
    expr t               = read_expr(d);
    if (has_value) {
        expr v      = read_expr(d);
        if (is_th_ax) {
            return mk_theorem(n, ps, t, v);
        } else {
            reducibility_hints hints = read_hints(d);
            return mk_definition(n, ps, t, v, hints, is_meta);
        }
    } else {
        if (is_th_ax)
            return mk_axiom(n, ps, t);
        else
            return mk_constant_assumption(n, ps, t, is_meta);
    }
}

serializer & operator<<(serializer & s, inductive::certified_inductive_decl::comp_rule const & r) {
    s << r.m_num_bu << r.m_comp_rhs;
    return s;
}

inductive::certified_inductive_decl::comp_rule read_comp_rule(deserializer & d) {
    unsigned n; expr e;
    d >> n >> e;
    return inductive::certified_inductive_decl::comp_rule(n, e);
}

serializer & operator<<(serializer & s, inductive::inductive_decl const & d) {
    s << d.m_name << d.m_level_params << d.m_num_params << d.m_type << length(d.m_intro_rules);
    for (inductive::intro_rule const & r : d.m_intro_rules)
        s << inductive::intro_rule_name(r) << inductive::intro_rule_type(r);
    return s;
}

inductive::inductive_decl read_inductive_decl(deserializer & d) {
    name d_name                 = read_name(d);
    level_param_names d_lparams = read_level_params(d);
    unsigned d_nparams          = d.read_unsigned();
    expr d_type                 = read_expr(d);
    unsigned num_intros         = d.read_unsigned();
    buffer<inductive::intro_rule> rules;
    for (unsigned j = 0; j < num_intros; j++) {
        name r_name = read_name(d);
        expr r_type = read_expr(d);
        rules.push_back(inductive::mk_intro_rule(r_name, r_type));
    }
    return inductive::inductive_decl(d_name, d_lparams, d_nparams, d_type, to_list(rules.begin(), rules.end()));
}

serializer & operator<<(serializer & s, inductive::certified_inductive_decl const & d) {
    s << d.get_num_ACe() << d.elim_prop_only() << d.has_dep_elim()
      << d.get_elim_levels() << d.get_elim_type() << d.get_decl()
      << d.is_K_target() << d.get_num_indices() << d.is_meta();
    write_list<inductive::certified_inductive_decl::comp_rule>(s, d.get_comp_rules());
    return s;
}

class read_certified_inductive_decl_fn {
public:
    inductive::certified_inductive_decl operator()(deserializer & d) {
        unsigned nACe        = d.read_unsigned();
        bool elim_prop       = d.read_bool();
        bool dep_elim        = d.read_bool();
        level_param_names ls = read_names(d);
        expr elim_type       = read_expr(d);
        inductive::inductive_decl decl  = read_inductive_decl(d);
        bool       K         = d.read_bool();
        unsigned   nind      = d.read_unsigned();
        bool is_meta         = d.read_bool();
        auto rs              = read_list<inductive::certified_inductive_decl::comp_rule>(d, read_comp_rule);
        return inductive::certified_inductive_decl(nACe, elim_prop, dep_elim, ls, elim_type, decl,
                                        K, nind, rs, is_meta);
    }
};

inductive::certified_inductive_decl read_certified_inductive_decl(deserializer & d) {
    return read_certified_inductive_decl_fn()(d);
}

void initialize_kernel_serializer() {
    g_macro_readers = new macro_readers();
    g_binder_name   = new name("a");
    g_expr_sd       = new expr_sd();
}

void finalize_kernel_serializer() {
    delete g_expr_sd;
    delete g_binder_name;
    delete g_macro_readers;
}
}
