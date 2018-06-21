/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/expr.h"
#include "kernel/declaration.h"
#include "library/kernel_serializer.h"

// Procedures for serializing and deserializing kernel objects (levels, exprs, declarations)
namespace lean {
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
}

void finalize_kernel_serializer() {
}
}
