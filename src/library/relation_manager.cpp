/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/optional.h"
#include "util/name.h"
#include "util/rb_map.h"
#include "util/sstream.h"
#include "library/constants.h"
#include "library/scoped_ext.h"
#include "library/relation_manager.h"

namespace lean {
// Check whether e is of the form (f ...) where f is a constant. If it is return f.
static name const & get_fn_const(expr const & e, char const * msg) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        throw exception(msg);
    return const_name(fn);
}

static pair<expr, unsigned> extract_arg_types_core(environment const & env, name const & f, buffer<expr> & arg_types) {
    declaration d = env.get(f);
    expr f_type = d.get_type();
    while (is_pi(f_type)) {
        arg_types.push_back(binding_domain(f_type));
        f_type = binding_body(f_type);
    }
    return mk_pair(f_type, d.get_num_univ_params());
}

enum class op_kind { Relation, Subst, Trans, Refl, Symm };

struct rel_entry {
    op_kind m_kind;
    name    m_name;
    rel_entry() {}
    rel_entry(op_kind k, name const & n):m_kind(k), m_name(n) {}
};

struct rel_state {
    typedef name_map<refl_info> refl_table;
    typedef name_map<subst_info> subst_table;
    typedef name_map<symm_info> symm_table;
    typedef rb_map<name_pair, trans_info, name_pair_quick_cmp> trans_table;
    typedef name_map<relation_info> rop_table;
    trans_table    m_trans_table;
    refl_table     m_refl_table;
    subst_table    m_subst_table;
    symm_table     m_symm_table;
    rop_table      m_rop_table;
    rel_state() {}

    bool is_equivalence(name const & rop) const {
        return m_trans_table.contains(mk_pair(rop, rop)) && m_refl_table.contains(rop) && m_symm_table.contains(rop);
    }

    static void throw_invalid_relation(name const & rop) {
        throw exception(sstream() << "invalid binary relation declaration, relation '" << rop
                        << "' must have two explicit parameters");
    }

    void register_rop(environment const & env, name const & rop) {
        if (m_rop_table.contains(rop))
            return;
        declaration const & d = env.get(rop);
        optional<unsigned> lhs_pos;
        optional<unsigned> rhs_pos;
        unsigned i = 0;
        expr type = d.get_type();
        while (is_pi(type)) {
            if (is_explicit(binding_info(type))) {
                if (!lhs_pos) {
                    lhs_pos = i;
                } else if (!rhs_pos) {
                    rhs_pos = i;
                } else {
                    lhs_pos = rhs_pos;
                    rhs_pos = i;
                }
            }
            type = binding_body(type);
            i++;
        }
        if (lhs_pos && rhs_pos) {
            m_rop_table.insert(rop, relation_info(i, *lhs_pos, *rhs_pos));
        } else {
            throw_invalid_relation(rop);
        }
    }

    void add_subst(environment const & env, name const & subst) {
        buffer<expr> arg_types;
        auto p          = extract_arg_types_core(env, subst, arg_types);
        expr r_type     = p.first;
        unsigned nunivs = p.second;
        unsigned nargs  = arg_types.size();
        if (nargs < 2)
            throw exception("invalid substitution theorem, it must have at least 2 arguments");
        name const & rop = get_fn_const(arg_types[nargs-2], "invalid substitution theorem, penultimate argument must be an operator application");
        m_subst_table.insert(rop, subst_info(subst, nunivs, nargs));
    }

    void add_refl(environment const & env, name const & refl) {
        buffer<expr> arg_types;
        auto p          = extract_arg_types_core(env, refl, arg_types);
        expr r_type     = p.first;
        unsigned nunivs = p.second;
        unsigned nargs  = arg_types.size();
        if (nargs < 1)
            throw exception("invalid reflexivity rule, it must have at least 1 argument");
        name const & rop = get_fn_const(r_type, "invalid reflexivity rule, result type must be an operator application");
        register_rop(env, rop);
        m_refl_table.insert(rop, refl_info(refl, nunivs, nargs));
    }

    void add_trans(environment const & env, name const & trans) {
        buffer<expr> arg_types;
        auto p = extract_arg_types_core(env, trans, arg_types);
        expr r_type     = p.first;
        unsigned nunivs = p.second;
        unsigned nargs  = arg_types.size();
        if (nargs < 5)
            throw exception("invalid transitivity rule, it must have at least 5 arguments");
        name const & rop = get_fn_const(r_type, "invalid transitivity rule, result type must be an operator application");
        name const & op1 = get_fn_const(arg_types[nargs-2], "invalid transitivity rule, penultimate argument must be an operator application");
        name const & op2 = get_fn_const(arg_types[nargs-1], "invalid transitivity rule, last argument must be an operator application");
        register_rop(env, rop);
        m_trans_table.insert(name_pair(op1, op2), trans_info(trans, nunivs, nargs, rop));
    }

    void add_symm(environment const & env, name const & symm) {
        buffer<expr> arg_types;
        auto p          = extract_arg_types_core(env, symm, arg_types);
        expr r_type     = p.first;
        unsigned nunivs = p.second;
        unsigned nargs  = arg_types.size();
        if (nargs < 1)
            throw exception("invalid symmetry rule, it must have at least 1 argument");
        name const & rop = get_fn_const(r_type, "invalid symmetry rule, result type must be an operator application");
        register_rop(env, rop);
        m_symm_table.insert(rop, symm_info(symm, nunivs, nargs));
    }
};

static name * g_rel_name  = nullptr;
static std::string * g_key = nullptr;

struct rel_config {
    typedef rel_state state;
    typedef rel_entry entry;
    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        switch (e.m_kind) {
        case op_kind::Relation: s.register_rop(env, e.m_name); break;
        case op_kind::Refl:     s.add_refl(env, e.m_name); break;
        case op_kind::Subst:    s.add_subst(env, e.m_name); break;
        case op_kind::Trans:    s.add_trans(env, e.m_name); break;
        case op_kind::Symm:     s.add_symm(env, e.m_name); break;
        }
    }
    static name const & get_class_name() {
        return *g_rel_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << static_cast<char>(e.m_kind) << e.m_name;
    }
    static entry read_entry(deserializer & d) {
        entry e;
        char cmd;
        d >> cmd >> e.m_name;
        e.m_kind = static_cast<op_kind>(cmd);
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const &) {
        return optional<unsigned>();
    }
};

template class scoped_ext<rel_config>;
typedef scoped_ext<rel_config> rel_ext;

environment add_relation(environment const & env, name const & n, bool persistent) {
    return rel_ext::add_entry(env, get_dummy_ios(), rel_entry(op_kind::Relation, n), persistent);
}

environment add_subst(environment const & env, name const & n, bool persistent) {
    return rel_ext::add_entry(env, get_dummy_ios(), rel_entry(op_kind::Subst, n), persistent);
}

environment add_refl(environment const & env, name const & n, bool persistent) {
    return rel_ext::add_entry(env, get_dummy_ios(), rel_entry(op_kind::Refl, n), persistent);
}

environment add_symm(environment const & env, name const & n, bool persistent) {
    return rel_ext::add_entry(env, get_dummy_ios(), rel_entry(op_kind::Symm, n), persistent);
}

environment add_trans(environment const & env, name const & n, bool persistent) {
    return rel_ext::add_entry(env, get_dummy_ios(), rel_entry(op_kind::Trans, n), persistent);
}

static optional<relation_lemma_info> get_info(name_map<relation_lemma_info> const & table, name const & op) {
    if (auto it = table.find(op)) {
        return optional<relation_lemma_info>(*it);
    } else {
        return optional<relation_lemma_info>();
    }
}

optional<refl_info> get_refl_extra_info(environment const & env, name const & op) {
    return get_info(rel_ext::get_state(env).m_refl_table, op);
}
optional<subst_info> get_subst_extra_info(environment const & env, name const & op) {
    return get_info(rel_ext::get_state(env).m_subst_table, op);
}
optional<symm_info> get_symm_extra_info(environment const & env, name const & op) {
    return get_info(rel_ext::get_state(env).m_symm_table, op);
}

optional<trans_info> get_trans_extra_info(environment const & env, name const & op1, name const & op2) {
    if (auto it = rel_ext::get_state(env).m_trans_table.find(mk_pair(op1, op2))) {
        return optional<trans_info>(*it);
    } else {
        return optional<trans_info>();
    }
}

bool is_subst_relation(environment const & env, name const & op) {
    return rel_ext::get_state(env).m_subst_table.contains(op);
}

optional<name> get_refl_info(environment const & env, name const & op) {
    if (auto it = get_refl_extra_info(env, op))
        return optional<name>(it->m_name);
    else
        return optional<name>();
}

optional<name> get_symm_info(environment const & env, name const & op) {
    if (auto it = get_symm_extra_info(env, op))
        return optional<name>(it->m_name);
    else
        return optional<name>();
}

optional<name> get_trans_info(environment const & env, name const & op) {
    if (auto it = get_trans_extra_info(env, op, op))
        return optional<name>(it->m_name);
    else
        return optional<name>();
}

bool is_equivalence(environment const & env, name const & rop) {
    return rel_ext::get_state(env).is_equivalence(rop);
}

relation_info const * get_relation_info(environment const & env, name const & rop) {
    return rel_ext::get_state(env).m_rop_table.find(rop);
}

void initialize_relation_manager() {
    g_rel_name = new name("rel");
    g_key       = new std::string("rel");
    rel_ext::initialize();
}

void finalize_relation_manager() {
    rel_ext::finalize();
    delete g_key;
    delete g_rel_name;
}
}
