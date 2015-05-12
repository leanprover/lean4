/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/sstream.h"
#include "kernel/inductive/inductive.h"
#include "library/scoped_ext.h"
#include "library/util.h"
#include "library/kernel_serializer.h"
#include "library/user_recursors.h"

namespace lean {
bool recursor_info::is_minor(unsigned pos) const {
    if (pos <= get_motive_pos())
        return false;
    if (get_first_index_pos() <= pos && pos <= m_major_pos)
        return false;
    return true;
}

recursor_info::recursor_info(name const & r, name const & I, unsigned num_params, unsigned num_indices, unsigned major,
                             optional<unsigned> const & motive_univ_pos, bool dep_elim):
    m_recursor(r), m_type_name(I), m_num_params(num_params), m_num_indices(num_indices), m_major_pos(major),
    m_motive_univ_pos(motive_univ_pos), m_dep_elim(dep_elim) {}
recursor_info::recursor_info() {}

void recursor_info::write(serializer & s) const {
    s << m_recursor << m_type_name << m_num_params << m_num_indices << m_major_pos << m_motive_univ_pos << m_dep_elim;
}

recursor_info recursor_info::read(deserializer & d) {
    recursor_info info;
    d >> info.m_recursor >> info.m_type_name >> info.m_num_params >> info.m_num_indices >> info.m_major_pos
      >> info.m_motive_univ_pos >> info.m_dep_elim;
    return info;
}

static void throw_invalid_motive(expr const & C) {
    throw exception(sstream() << "invalid user defined recursor, motive '" << C
                    << "' must have a type of the form (C : Pi (i : B A), I A i -> Type), "
                    "where A is (possibly empty) sequence of bound variables (aka parameters), "
                    "(i : B A) is a (possibly empty) telescope (aka indices), "
                    "and I is a constant");
}

static void throw_invalid_major(buffer<expr> const & tele, expr const & I, unsigned num_params,
                                unsigned num_indices, unsigned major_pos) {
    sstream msg;
    msg << "invalid user defined recursor, major premise '" << tele[major_pos] << "' is expected to have type " << I;
    for (unsigned i = 0; i < num_params; i++)
        msg << " " << tele[i];
    for (unsigned i = major_pos - num_indices; i < major_pos; i++)
        msg << " " << tele[i];
    throw exception(msg);
}

recursor_info mk_recursor_info(environment const & env, name const & r) {
    if (auto I = inductive::is_elim_rule(env, r)) {
        if (*inductive::get_num_type_formers(env, *I) > 1)
            throw exception(sstream() << "unsupported recursor '" << r << "', it has multiple motives");
        optional<unsigned> motive_univ_pos;
        if (env.get(name(*I, "rec")).get_num_univ_params() != env.get(name(*I)).get_num_univ_params())
            motive_univ_pos = 0;
        return recursor_info(r, *I,
                             *inductive::get_num_params(env, *I),
                             *inductive::get_num_indices(env, *I),
                             *inductive::get_elim_major_idx(env, r),
                             motive_univ_pos,
                             inductive::has_dep_elim(env, *I));
    }
    declaration d = env.get(r);
    type_checker tc(env);
    buffer<expr> tele;
    expr rtype    = to_telescope(tc, d.get_type(), tele);
    buffer<expr> C_args;
    expr C        = get_app_args(rtype, C_args);
    if (!is_local(C) || !std::all_of(C_args.begin(), C_args.end(), is_local) || C_args.empty()) {
        throw exception("invalid user defined recursor, result type must be of the form (C i t), "
                        "where C and t are bound variables, and i is a (possibly empty) sequence of bound variables");
    }
    unsigned num_indices = C_args.size() - 1;
    unsigned num_params  = 0;
    for (expr const & x : tele) {
        if (mlocal_name(x) == mlocal_name(C))
            break;
        num_params++;
    }
    buffer<expr> C_tele;
    expr C_rtype  = to_telescope(tc, mlocal_type(C), C_tele);
    if (!is_sort(C_rtype) || C_tele.size() != C_args.size()) {
        throw_invalid_motive(C);
    }
    optional<unsigned> C_univ_pos;
    level C_lvl = sort_level(C_rtype);
    if (!is_standard(env) || !is_zero(C_lvl)) {
        if (!is_param(C_lvl)) {
            if (is_standard(env))
                throw exception("invalid user defined recursor, "
                                "motive result sort must be Prop or Type.{l} where l is a universe parameter");
            else
                throw exception("invalid user defined recursor, "
                                "motive result sort must be Type.{l} where l is a universe parameter");
        }
        name l  = param_id(C_lvl);
        C_univ_pos = 0;
        for (name const & l_curr : d.get_univ_params()) {
            if (l_curr == l)
                break;
            C_univ_pos = *C_univ_pos + 1;
        }
        lean_assert(*C_univ_pos < length(d.get_univ_params()));
    }

    buffer<expr> I_args;
    expr I = get_app_args(mlocal_type(C_tele.back()), I_args);
    if (!is_constant(I) || I_args.size() != num_params + num_indices) {
        throw_invalid_motive(C);
    }
    for (unsigned i = 0; i < num_params; i++) {
        if (mlocal_name(I_args[i]) != mlocal_name(tele[i]))
            throw_invalid_motive(C);
    }
    for (unsigned i = 0; i < num_indices; i++) {
        if (mlocal_name(I_args[num_params + i]) != mlocal_name(C_tele[i]))
            throw_invalid_motive(C);
    }
    expr const & major  = C_args.back();
    unsigned major_pos  = 0;
    for (expr const & x : tele) {
        if (mlocal_name(x) == mlocal_name(major))
            break;
        major_pos++;
    }
    lean_assert(major_pos < tele.size());
    if (major_pos < num_indices)
        throw exception(sstream() << "invalid user defined recursor, indices must occur before major premise '"
                        << major << "'");
    recursor_info info(r, const_name(I), num_params, num_indices, major_pos, C_univ_pos, true);
    unsigned first_index_pos = info.get_first_index_pos();
    for (unsigned i = 0; i < num_indices; i++) {
        if (mlocal_name(tele[first_index_pos+i]) != mlocal_name(C_args[i])) {
            throw exception(sstream() << "invalid user defined recursor, index '" << C_args[i]
                            << "' expected, but got '" << tele[i] << "'");
        }
    }
    buffer<expr> I_args_major;
    expr I_major = get_app_args(mlocal_type(tele[major_pos]), I_args_major);
    if (I != I_major)
        throw_invalid_major(tele, I, num_params, num_indices, major_pos);
    for (unsigned i = 0; i < num_params; i++) {
        if (mlocal_name(I_args_major[i]) != mlocal_name(tele[i]))
            throw_invalid_major(tele, I, num_params, num_indices, major_pos);
    }
    for (unsigned i = 0; i < num_indices; i++) {
        if (mlocal_name(I_args_major[num_params + i]) != mlocal_name(tele[first_index_pos + i]))
            throw_invalid_major(tele, I, num_params, num_indices, major_pos);
    }
    for (unsigned i = 0; i < tele.size(); i++) {
        if (info.is_minor(i)) {
            buffer<expr> minor_tele;
            expr minor_rtype = to_telescope(tc, mlocal_type(tele[i]), minor_tele);
            expr minor_C     = get_app_fn(minor_rtype);
            if (!is_local(minor_C) || mlocal_name(minor_C) != mlocal_name(C))
                throw exception(sstream() << "invalid user defined recursor, resultant type of minor premise '"
                                << tele[i] << "' must be of the form (" << C << " ...)");
        }
    }
    return info;
}

struct recursor_state {
    name_map<recursor_info> m_recursors;
    name_map<list<name>>    m_type2recursors;

    void insert(recursor_info const & info) {
        m_recursors.insert(info.get_name(), info);
        if (auto l = m_type2recursors.find(info.get_type_name())) {
            m_type2recursors.insert(info.get_type_name(),
                                    cons(info.get_name(),
                                         filter(*l, [&](name const & n) { return n != info.get_name(); })));
        } else {
            m_type2recursors.insert(info.get_type_name(), to_list(info.get_name()));
        }
    }
};

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct recursor_config {
    typedef recursor_state  state;
    typedef recursor_info   entry;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        s.insert(e);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        e.write(s);
    }
    static entry read_entry(deserializer & d) {
        return recursor_info::read(d);
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.get_name().hash());
    }
};

template class scoped_ext<recursor_config>;
typedef scoped_ext<recursor_config> recursor_ext;

environment add_user_recursor(environment const & env, name const & r, bool persistent) {
    if (inductive::is_elim_rule(env, r))
        throw exception(sstream() << "invalid user defined recursor, '" << r << "' is a builtin recursor");
    recursor_info info = mk_recursor_info(env, r);
    return recursor_ext::add_entry(env, get_dummy_ios(), info, persistent);
}

recursor_info get_recursor_info(environment const & env, name const & r) {
    if (auto info = recursor_ext::get_state(env).m_recursors.find(r))
        return *info;
    return mk_recursor_info(env, r);
}

list<name> get_recursors_for(environment const & env, name const & I) {
    if (auto l = recursor_ext::get_state(env).m_type2recursors.find(I))
        return *l;
    else
        return list<name>();
}

void initialize_user_recursors() {
    g_class_name = new name("recursor");
    g_key        = new std::string("urec");
    recursor_ext::initialize();
}

void finalize_user_recursors() {
    recursor_ext::finalize();
    delete g_class_name;
    delete g_key;
}
}
