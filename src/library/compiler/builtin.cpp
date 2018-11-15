/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include "util/list.h"
#include "kernel/expr.h"
#include "library/compiler/util.h"

namespace lean {
struct builtin_decl {
    expr              m_type;
    unsigned          m_arity;
    char const *      m_cname;
    bool              m_borrowed_res;
    list<bool>        m_borrowed_args;
    builtin_decl() {}
    builtin_decl(expr const & type, unsigned arity, char const * cname, bool bres, list<bool> const & bargs):
        m_type(type), m_arity(arity), m_cname(cname), m_borrowed_res(bres), m_borrowed_args(bargs) {
    }
};

typedef std::unordered_map<name, builtin_decl, name_hash> builtin_map;

static builtin_map * g_builtin_decls = nullptr;

void register_builtin(name const & n, expr const & type, unsigned arity, char const * cname, bool borrowed_res, list<bool> const & borrowed_arg) {
    lean_assert(!g_builtin_decls->contains(n));
    g_builtin_decls->insert(mk_pair(n, builtin_decl(type, arity, cname, borrowed_res, borrowed_arg)));
}

void register_builtin(name const & n, expr const & type, char const * cname, bool borrowed_res, list<bool> const & borrowed_arg) {
    unsigned arity = get_arity(type);
    return register_builtin(n, type, arity, cname, borrowed_res, borrowed_arg);
}

void register_builtin(name const & n, expr const & type, char const * cname, list<bool> const & borrowed_arg) {
    return register_builtin(n, type, cname, false, borrowed_arg);
}

void register_builtin(name const & n, expr const & type, unsigned arity, char const * cname) {
    buffer<bool> borrowed;
    borrowed.resize(arity, false);
    return register_builtin(n, type, arity, cname, false, to_list(borrowed));
}

void register_builtin(name const & n, expr const & type, char const * cname) {
    unsigned arity = get_arity(type);
    return register_builtin(n, type, arity, cname);
}

#define V(p) reinterpret_cast<void*>(p)

void initialize_builtin() {
    g_builtin_decls = new builtin_map();

    expr o       = mk_enf_object_type();
    expr u8      = mk_constant(get_uint8_name());
    expr u32     = mk_constant(get_uint32_name());
    expr o_o     = mk_arrow(o, o);
    expr o_o_o   = mk_arrow(o, o_o);
    expr o_u32_o = mk_arrow(o, mk_arrow(u32, o));
    expr o_u8    = mk_arrow(o, u8);
    list<bool> b{true};
    list<bool> bb{true, true};
    list<bool> c{false};
    list<bool> cc{false, false};
    list<bool> cb{false, true};

    /* nat builtin functions */
    register_builtin(name({"nat", "add"}), o_o_o, "nat_add", bb);
    register_builtin(name({"nat", "sub"}), o_o_o, "nat_sub", bb);
    register_builtin(name({"nat", "mul"}), o_o_o, "nat_mul", bb);
    register_builtin(name({"nat", "div"}), o_o_o, "nat_div", bb);
    register_builtin(name({"nat", "mod"}), o_o_o, "nat_mod", bb);
    register_builtin(name({"nat", "dec_eq"}), o_o_o, "nat_dec_eq", bb);
    register_builtin(name({"nat", "dec_lt"}), o_o_o, "nat_dec_lt", bb);
    register_builtin(name({"nat", "dec_le"}), o_o_o, "nat_dec_le", bb);

    /* int builtin functions */
    register_builtin(name({"int", "of_nat"}), o_o, "nat2int", b);
    register_builtin(name({"int", "neg_succ_of_nat"}), o_o, "int_neg_succ_of_nat", b);
    register_builtin(name({"int", "nat_abs"}), o_o, "nat_abs", b);
    register_builtin(name({"int", "neg"}), o_o, "int_neg", b);
    register_builtin(name({"int", "add"}), o_o_o, "int_add", bb);
    register_builtin(name({"int", "sub"}), o_o_o, "int_sub", bb);
    register_builtin(name({"int", "mul"}), o_o_o, "int_mul", bb);
    register_builtin(name({"int", "quot"}), o_o_o, "int_div", bb);
    register_builtin(name({"int", "rem"}), o_o_o, "int_rem", bb);
    register_builtin(name({"int", "dec_eq"}), o_o_o, "int_dec_eq", bb);
    register_builtin(name({"int", "dec_lt"}), o_o_o, "int_dec_lt", bb);
    register_builtin(name({"int", "dec_le"}), o_o_o, "int_dec_le", bb);

    /* string builtin functions */
    register_builtin(name({"string", "mk"}), o_o, "string_mk", c);
    register_builtin(name({"string", "data"}), o_o, "string_data", c);
    register_builtin(name({"string", "length"}), o_o, "string_length", b);
    register_builtin(name({"string", "push"}), o_u32_o, "string_push", cc);
    register_builtin(name({"string", "append"}), o_o_o, "string_append", cb);
    register_builtin(name({"string", "mk_iterator"}), o_o, "string_mk_iterator", c);
    register_builtin(name({"string", "dec_eq"}), o_o_o, "string_dec_eq", bb);
    register_builtin(name({"string", "dec_lt"}), o_o_o, "string_dec_lt", bb);
    register_builtin(name({"string", "iterator", "curr"}), o_o, "string_iterator_curr", b);
    register_builtin(name({"string", "iterator", "set_curr"}), o_u32_o, "string_iterator_set_curr", cc);
    register_builtin(name({"string", "iterator", "next"}), o_o, "string_iterator_next", c);
    register_builtin(name({"string", "iterator", "prev"}), o_o, "string_iterator_prev", c);
    register_builtin(name({"string", "iterator", "has_next"}), o_u8, "string_iterator_has_next", b);
    register_builtin(name({"string", "iterator", "has_prev"}), o_u8, "string_iterator_has_prev", b);
    register_builtin(name({"string", "iterator", "insert"}), o_o_o, "string_iterator_insert", cb);
    register_builtin(name({"string", "iterator", "remove"}), o_o_o, "string_iterator_remove", cb);
    register_builtin(name({"string", "iterator", "remaining"}), o_o, "string_iterator_remaining", b);
    register_builtin(name({"string", "iterator", "offset"}), o_o, "string_iterator_offset", b);
    register_builtin(name({"string", "iterator", "to_string"}), o_o, "string_iterator_to_string", b);
    register_builtin(name({"string", "iterator", "to_end"}), o_o, "string_iterator_to_end", c);
    register_builtin(name({"string", "iterator", "remaining_to_string"}), o_o, "string_iterator_remaining_to_string", b);
    register_builtin(name({"string", "iterator", "prev_to_string"}), o_o, "string_iterator_prev_to_string", b);
    register_builtin(name({"string", "iterator", "extract"}), o_o_o, "string_iterator_extract", bb);
    register_builtin(name({"string", "iterator", "mk"}), o_o_o, "string_iterator_mk", bb);
    register_builtin(name({"string", "iterator", "fst"}), o_o, "string_iterator_fst", b);
    register_builtin(name({"string", "iterator", "snd"}), o_o, "string_iterator_snd", b);
}

void finalize_builtin() {
    delete g_builtin_decls;
}
}
