/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Max Wagner
*/
#include <unordered_map>
#include <string>
#include "util/list.h"
#include "kernel/expr.h"
#include "library/compiler/util.h"

namespace lean {

struct native_decl {
    expr                  m_ll_type;
    unsigned              m_arity;
    std::string           m_cname;
    bool                  m_borrowed_res;
    list<bool>            m_borrowed_args;

    native_decl() {}
    native_decl(expr const & ll_type, unsigned arity, std::string cname, bool bres, list<bool> const & bargs):
        m_ll_type(ll_type), m_arity(arity), m_cname(cname), m_borrowed_res(bres), m_borrowed_args(bargs) {
    }
};

typedef name_map<native_decl> native_decl_map;
static native_decl_map * g_initial_native_decls;

bool is_builtin_constant(name const & c) {
    return g_initial_native_decls->contains(c);
}

struct native_decls_ext : public environment_extension {
    native_decl_map m_decls;

    native_decls_ext() {
        g_initial_native_decls->for_each([&](name const & n, native_decl const & d) {
           m_decls.insert(n, d);
        });
    }
};

struct native_decls_reg {
    unsigned m_ext_id;
    native_decls_reg() {
        std::shared_ptr<native_decls_ext> decl_reg = std::make_shared<native_decls_ext>();
        m_ext_id = environment::register_extension(decl_reg);
    }
};

static native_decls_reg * g_ext = nullptr;

static environment update(environment const & env, native_decls_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<native_decls_ext>(ext));
}


void register_builtin(name const & n, expr const & ll_type, unsigned arity, char const * cname,
                      bool borrowed_res, list<bool> const & borrowed_arg) {
    lean_assert(g_initial_native_decls->find(n) == nullptr);
    g_initial_native_decls->insert(n, native_decl(ll_type, arity, cname, borrowed_res, borrowed_arg));
}

void register_builtin(name const & n, expr const & ll_type, char const * cname,
                      bool borrowed_res, list<bool> const & borrowed_arg) {
    unsigned arity = get_arity(ll_type);
    return register_builtin(n, ll_type, arity, cname, borrowed_res, borrowed_arg);
}

void register_builtin(name const & n, expr const & ll_type, char const * cname, list<bool> const & borrowed_arg) {
    return register_builtin(n, ll_type, cname, false, borrowed_arg);
}

void register_builtin(name const & n, expr const & ll_type, unsigned arity, char const * cname) {
    buffer<bool> borrowed;
    borrowed.resize(arity, false);
    return register_builtin(n, ll_type, arity, cname, false, to_list(borrowed));
}

void register_builtin(name const & n, expr const & ll_type, char const * cname) {
    unsigned arity = get_arity(ll_type);
    return register_builtin(n, ll_type, arity, cname);
}

static inline native_decls_ext const & get_ext(environment const & env) {
    return static_cast<native_decls_ext const & >(env.get_extension(g_ext->m_ext_id));
}

environment add_native_constant_decl(environment const & env, name const & n, expr const & ll_type, std::string cname,
                                     bool bres, list<bool> const & bargs) {
    native_decl d(ll_type, get_arity(ll_type), cname, bres, bargs);
    native_decls_ext ext = get_ext(env);
    ext.m_decls.insert(n, d);
    return update(env, ext);
}

void for_each_native_constant(environment const & env, std::function<void(name const & n)> const & f) {
    auto ext = get_ext(env);
    ext.m_decls.for_each([&](name const & n, native_decl const &) { f(n); });
}

static inline native_decl const * get_native_constant_core(environment const & env, name const & n) {
    auto ext = get_ext(env);
    return ext.m_decls.find(n);
}

optional<name> get_native_constant_cname(environment const & env, name const & c) {
    auto d =  get_native_constant_core(env, c);
    if (d == nullptr)
        return optional<name>();
    return optional<name>(d->m_cname);
}

bool is_native_constant(environment const & env, name const & c) {
    return get_native_constant_core(env, c) != nullptr;
}

optional<expr> get_native_constant_ll_type(environment const & env, name const & c) {
    auto d = get_native_constant_core(env, c);
    if (d == nullptr)
        return none_expr();
    return some_expr(d->m_ll_type);
}

optional<unsigned> get_native_constant_arity(environment const & env, name const & c) {
    auto d = get_native_constant_core(env, c);
    if (d == nullptr)
        return optional<unsigned>();
    return optional<unsigned>(d->m_arity);
}

bool get_native_borrowed_info(environment const & env, name const & c, buffer<bool> &borrowed_args, bool &borrowed_res) {
    auto d = get_native_constant_core(env, c);
    if (d == nullptr)
        return false;

    to_buffer(d->m_borrowed_args, borrowed_args);
    borrowed_res = d->m_borrowed_res;
    return true;
}

void initialize_builtin() {
    g_initial_native_decls = new native_decl_map();

    expr o           = mk_enf_object_type();
    expr u8          = mk_constant(get_uint8_name());
    expr u16         = mk_constant(get_uint16_name());
    expr u32         = mk_constant(get_uint32_name());
    expr u64         = mk_constant(get_uint64_name());
    expr us          = mk_constant(get_usize_name());
    expr o_o         = mk_arrow(o, o);
    expr o_o_o       = mk_arrow(o, o_o);
    expr o_o_o_o     = mk_arrow(o, o_o_o);
    expr o_o_o_o_o   = mk_arrow(o, o_o_o_o);

    expr o_u8        = mk_arrow(o, u8);
    expr o_u8_u8_o_o = mk_arrow(o, mk_arrow(u8, mk_arrow(u8, o_o)));
    expr u8_u8       = mk_arrow(u8, u8);
    expr u8_u8_u8    = mk_arrow(u8, u8_u8);
    expr u8_o_u8     = mk_arrow(u8, o_u8);
    expr u8_o        = mk_arrow(u8, o);
    expr u8_u8_o     = mk_arrow(u8, u8_o);
    expr o_o_u8      = mk_arrow(o, o_u8);

    expr o_u16         = mk_arrow(o, u16);
    expr o_u16_u16_o_o = mk_arrow(o, mk_arrow(u16, mk_arrow(u16, o_o)));
    expr u16_u16       = mk_arrow(u16, u16);
    expr u16_u16_u16   = mk_arrow(u16, u16_u16);
    expr u16_o_u16     = mk_arrow(u16, o_u16);
    expr u16_o         = mk_arrow(u16, o);
    expr u16_u16_o     = mk_arrow(u16, u16_o);
    expr u16_u16_u8    = mk_arrow(u16, mk_arrow(u16, u8));

    expr o_u32         = mk_arrow(o, u32);
    expr o_u32_o       = mk_arrow(o, mk_arrow(u32, o));
    expr o_u32_u32_o_o = mk_arrow(o, mk_arrow(u32, mk_arrow(u32, o_o)));
    expr u32_u32       = mk_arrow(u32, u32);
    expr u32_u32_u32   = mk_arrow(u32, u32_u32);
    expr u32_o_u32     = mk_arrow(u32, o_u32);
    expr u32_o         = mk_arrow(u32, o);
    expr u32_u32_o     = mk_arrow(u32, u32_o);
    expr u32_u32_u8    = mk_arrow(u32, mk_arrow(u32, u8));

    expr o_u64         = mk_arrow(o, u64);
    expr o_u64_u64_o_o = mk_arrow(o, mk_arrow(u64, mk_arrow(u64, o_o)));
    expr u64_u64       = mk_arrow(u64, u64);
    expr u64_u64_u64   = mk_arrow(u64, u64_u64);
    expr u64_o_u64     = mk_arrow(u64, o_u64);
    expr u64_o         = mk_arrow(u64, o);
    expr u64_u64_o     = mk_arrow(u64, u64_o);
    expr u64_u64_u8    = mk_arrow(u64, mk_arrow(u64, u8));

    expr o_us          = mk_arrow(o, us);
    expr o_us_us_o_o   = mk_arrow(o, mk_arrow(us, mk_arrow(us, o_o)));
    expr us_us         = mk_arrow(us, us);
    expr us_us_us      = mk_arrow(us, us_us);
    expr us_o_us       = mk_arrow(us, o_us);
    expr us_o          = mk_arrow(us, o);
    expr us_us_o       = mk_arrow(us, us_o);
    expr us_us_u8      = mk_arrow(us, mk_arrow(us, u8));

    list<bool> b{true};
    list<bool> bb{true, true};
    list<bool> c{false};
    list<bool> cc{false, false};
    list<bool> cb{false, true};
    list<bool> bc{true, false};
    list<bool> bbb{true, true, true};
    list<bool> bccc{true, false, false, false};
    list<bool> bbcc{true, true, false, false};

    /* nat builtin functions */
    register_builtin(name({"nat", "add"}), o_o_o, "lean::nat_add", bb);
    register_builtin(name({"nat", "sub"}), o_o_o, "lean::nat_sub", bb);
    register_builtin(name({"nat", "mul"}), o_o_o, "lean::nat_mul", bb);
    register_builtin(name({"nat", "div"}), o_o_o, "lean::nat_div", bb);
    register_builtin(name({"nat", "mod"}), o_o_o, "lean::nat_mod", bb);
    register_builtin(name({"nat", "dec_eq"}), o_o_u8, "lean::nat_dec_eq", bb);
    register_builtin(name({"nat", "dec_lt"}), o_o_u8, "lean::nat_dec_lt", bb);
    register_builtin(name({"nat", "dec_le"}), o_o_u8, "lean::nat_dec_le", bb);

    /* int builtin functions */
    register_builtin(name({"int", "of_nat"}), o_o, "lean::nat2int", b);
    register_builtin(name({"int", "neg_succ_of_nat"}), o_o, "lean::int_neg_succ_of_nat", b);
    register_builtin(name({"int", "nat_abs"}), o_o, "lean::nat_abs", b);
    register_builtin(name({"int", "neg"}), o_o, "lean::int_neg", b);
    register_builtin(name({"int", "add"}), o_o_o, "lean::int_add", bb);
    register_builtin(name({"int", "sub"}), o_o_o, "lean::int_sub", bb);
    register_builtin(name({"int", "mul"}), o_o_o, "lean::int_mul", bb);
    register_builtin(name({"int", "quot"}), o_o_o, "lean::int_div", bb);
    register_builtin(name({"int", "rem"}), o_o_o, "lean::int_rem", bb);
    register_builtin(name({"int", "dec_eq"}), o_o_u8, "lean::int_dec_eq", bb);
    register_builtin(name({"int", "dec_lt"}), o_o_u8, "lean::int_dec_lt", bb);
    register_builtin(name({"int", "dec_le"}), o_o_u8, "lean::int_dec_le", bb);

    /* string builtin functions */
    register_builtin(name({"string", "mk"}), o_o, "lean::string_mk", c);
    register_builtin(name({"string", "data"}), o_o, "lean::string_data", c);
    register_builtin(name({"string", "length"}), o_o, "lean::string_length", b);
    register_builtin(name({"string", "push"}), o_u32_o, "lean::string_push", cc);
    register_builtin(name({"string", "append"}), o_o_o, "lean::string_append", cb);
    register_builtin(name({"string", "mk_iterator"}), o_o, "lean::string_mk_iterator", c);
    register_builtin(name({"string", "dec_eq"}), o_o_u8, "lean::string_dec_eq", bb);
    register_builtin(name({"string", "dec_lt"}), o_o_u8, "lean::string_dec_lt", bb);
    register_builtin(name({"string", "iterator", "curr"}), o_u32, "lean::string_iterator_curr", b);
    register_builtin(name({"string", "iterator", "set_curr"}), o_u32_o, "lean::string_iterator_set_curr", cc);
    register_builtin(name({"string", "iterator", "next"}), o_o, "lean::string_iterator_next", c);
    register_builtin(name({"string", "iterator", "prev"}), o_o, "lean::string_iterator_prev", c);
    register_builtin(name({"string", "iterator", "has_next"}), o_u8, "lean::string_iterator_has_next", b);
    register_builtin(name({"string", "iterator", "has_prev"}), o_u8, "lean::string_iterator_has_prev", b);
    register_builtin(name({"string", "iterator", "insert"}), o_o_o, "lean::string_iterator_insert", cb);
    register_builtin(name({"string", "iterator", "remove"}), o_o_o, "lean::string_iterator_remove", cb);
    register_builtin(name({"string", "iterator", "remaining"}), o_o, "lean::string_iterator_remaining", b);
    register_builtin(name({"string", "iterator", "offset"}), o_o, "lean::string_iterator_offset", b);
    register_builtin(name({"string", "iterator", "to_string"}), o_o, "lean::string_iterator_to_string", b);
    register_builtin(name({"string", "iterator", "to_end"}), o_o, "lean::string_iterator_to_end", c);
    register_builtin(name({"string", "iterator", "remaining_to_string"}), o_o, "lean::string_iterator_remaining_to_string", b);
    register_builtin(name({"string", "iterator", "prev_to_string"}), o_o, "lean::string_iterator_prev_to_string", b);
    register_builtin(name({"string", "iterator", "extract"}), o_o_o, "lean::string_iterator_extract", bb);
    register_builtin(name({"string", "iterator", "mk"}), o_o_o, "lean::string_iterator_mk", bb);
    register_builtin(name({"string", "iterator", "fst"}), o_o, "lean::string_iterator_fst", b);
    register_builtin(name({"string", "iterator", "snd"}), o_o, "lean::string_iterator_snd", b);

    /* io builtin functions */
    register_builtin(name({"io", "prim", "put_str"}), o_o_o, "lean::io_prim_put_str", bc);
    register_builtin(name({"io", "prim", "get_line"}), o_o, "lean::io_prim_get_line", c);
    register_builtin(name({"io", "prim", "handle", "mk"}), o_u8_u8_o_o, "lean::io_prim_handle_mk", bccc);
    register_builtin(name({"io", "prim", "handle", "is_eof"}), o_o_o, "lean::io_prim_handle_is_eof", bc);
    register_builtin(name({"io", "prim", "handle", "flush"}), o_o_o, "lean::io_prim_handle_flush", bc);
    register_builtin(name({"io", "prim", "handle", "close"}), o_o_o, "lean::io_prim_handle_close", bc);
    register_builtin(name({"io", "prim", "handle", "get_line"}), o_o_o, "lean::io_prim_handle_get_line", bc);

    // interface to old elaborator
    register_builtin(name({"lean", "expr", "local"}), mk_arrow(o, o_o_o_o), "lean_expr_local");
    register_builtin(name({"lean", "environment", "mk_empty"}), o_o, "lean_environment_mk_empty");
    register_builtin(name({"lean", "environment", "contains"}), o_o_o, "lean_environment_contains");
    register_builtin(name({"lean", "elaborator", "elaborate_command"}), o_o_o_o, "lean_elaborator_elaborate_command");

    /* uint8 builtin functions */
    register_builtin(name({"uint8", "of_nat"}), o_u8, "lean::uint8_of_nat", b);
    register_builtin(name({"uint8", "to_nat"}), u8_o, "lean::uint8_to_nat");
    register_builtin(name({"uint8", "add"}), u8_u8_u8, "lean::uint8_add");
    register_builtin(name({"uint8", "sub"}), u8_u8_u8, "lean::uint8_sub");
    register_builtin(name({"uint8", "mul"}), u8_u8_u8, "lean::uint8_mul");
    register_builtin(name({"uint8", "div"}), u8_u8_u8, "lean::uint8_div");
    register_builtin(name({"uint8", "mod"}), u8_u8_u8, "lean::uint8_mod");
    register_builtin(name({"uint8", "modn"}), u8_o_u8, "lean::uint8_modn", cb);
    register_builtin(name({"uint8", "dec_eq"}), u8_u8_u8, "lean::uint8_dec_eq");
    register_builtin(name({"uint8", "dec_lt"}), u8_u8_u8, "lean::uint8_dec_lt");
    register_builtin(name({"uint8", "dec_le"}), u8_u8_u8, "lean::uint8_dec_le");

    /* uint16 builtin functions */
    register_builtin(name({"uint16", "of_nat"}), o_u16, "lean::uint16_of_nat", b);
    register_builtin(name({"uint16", "to_nat"}), u16_o, "lean::uint16_to_nat");
    register_builtin(name({"uint16", "add"}), u16_u16_u16, "lean::uint16_add");
    register_builtin(name({"uint16", "sub"}), u16_u16_u16, "lean::uint16_sub");
    register_builtin(name({"uint16", "mul"}), u16_u16_u16, "lean::uint16_mul");
    register_builtin(name({"uint16", "div"}), u16_u16_u16, "lean::uint16_div");
    register_builtin(name({"uint16", "mod"}), u16_u16_u16, "lean::uint16_mod");
    register_builtin(name({"uint16", "modn"}), u16_o_u16, "lean::uint16_modn", cb);
    register_builtin(name({"uint16", "dec_eq"}), u16_u16_u8, "lean::uint16_dec_eq");
    register_builtin(name({"uint16", "dec_lt"}), u16_u16_u8, "lean::uint16_dec_lt");
    register_builtin(name({"uint16", "dec_le"}), u16_u16_u8, "lean::uint16_dec_le");

    /* uint32 builtin functions */
    register_builtin(name({"uint32", "of_nat"}), o_u32, "lean::uint32_of_nat", b);
    register_builtin(name({"uint32", "to_nat"}), u32_o, "lean::uint32_to_nat");
    register_builtin(name({"uint32", "add"}), u32_u32_u32, "lean::uint32_add");
    register_builtin(name({"uint32", "sub"}), u32_u32_u32, "lean::uint32_sub");
    register_builtin(name({"uint32", "mul"}), u32_u32_u32, "lean::uint32_mul");
    register_builtin(name({"uint32", "div"}), u32_u32_u32, "lean::uint32_div");
    register_builtin(name({"uint32", "mod"}), u32_u32_u32, "lean::uint32_mod");
    register_builtin(name({"uint32", "modn"}), u32_o_u32, "lean::uint32_modn", cb);
    register_builtin(name({"uint32", "dec_eq"}), u32_u32_u8, "lean::uint32_dec_eq");
    register_builtin(name({"uint32", "dec_lt"}), u32_u32_u8, "lean::uint32_dec_lt");
    register_builtin(name({"uint32", "dec_le"}), u32_u32_u8, "lean::uint32_dec_le");

    /* uint64 builtin functions */
    register_builtin(name({"uint64", "of_nat"}), o_u64, "lean::uint64_of_nat", b);
    register_builtin(name({"uint64", "to_nat"}), u64_o, "lean::uint64_to_nat");
    register_builtin(name({"uint64", "add"}), u64_u64_u64, "lean::uint64_add");
    register_builtin(name({"uint64", "sub"}), u64_u64_u64, "lean::uint64_sub");
    register_builtin(name({"uint64", "mul"}), u64_u64_u64, "lean::uint64_mul");
    register_builtin(name({"uint64", "div"}), u64_u64_u64, "lean::uint64_div");
    register_builtin(name({"uint64", "mod"}), u64_u64_u64, "lean::uint64_mod");
    register_builtin(name({"uint64", "modn"}), u64_o_u64, "lean::uint64_modn", cb);
    register_builtin(name({"uint64", "dec_eq"}), u64_u64_u8, "lean::uint64_dec_eq");
    register_builtin(name({"uint64", "dec_lt"}), u64_u64_u8, "lean::uint64_dec_lt");
    register_builtin(name({"uint64", "dec_le"}), u64_u64_u8, "lean::uint64_dec_le");

    /* usize builtin functions */
    register_builtin(name({"usize", "of_nat"}), o_us, "lean::usize_of_nat", b);
    register_builtin(name({"usize", "to_nat"}), us_o, "lean::usize_to_nat");
    register_builtin(name({"usize", "add"}), us_us_us, "lean::usize_add");
    register_builtin(name({"usize", "sub"}), us_us_us, "lean::usize_sub");
    register_builtin(name({"usize", "mul"}), us_us_us, "lean::usize_mul");
    register_builtin(name({"usize", "div"}), us_us_us, "lean::usize_div");
    register_builtin(name({"usize", "mod"}), us_us_us, "lean::usize_mod");
    register_builtin(name({"usize", "modn"}), us_o_us, "lean::usize_modn", cb);
    register_builtin(name({"usize", "dec_eq"}), us_us_u8, "lean::usize_dec_eq");
    register_builtin(name({"usize", "dec_lt"}), us_us_u8, "lean::usize_dec_lt");
    register_builtin(name({"usize", "dec_le"}), us_us_u8, "lean::usize_dec_le");

    /* thunk builtin functions */
    register_builtin(name({"thunk", "mk"}), o_o_o, "lean::mk_thunk", bc);
    register_builtin(name({"thunk", "pure"}), o_o_o, "lean::thunk_pure", bc);
    register_builtin(name({"thunk", "get"}), o_o_o, "lean::thunk_get", bb);
    register_builtin(name({"thunk", "bind"}), o_o_o_o_o, "lean::thunk_get", bb);
    register_builtin(name({"thunk", "map"}), o_o_o_o_o, "lean::thunk_bind", bbcc);

    /* name builtin functions */
    register_builtin(name({"lean", "name", "hash"}), o_us, "lean::name_hash_usize", b);
    register_builtin(name({"lean", "name", "mk_string"}), o_o_o, "lean::name_mk_string");
    register_builtin(name({"lean", "name", "mk_numeral"}), o_o_o, "lean::name_mk_numeral");
    register_builtin(name({"lean", "name", "dec_eq"}), o_o_u8, "lean::name_dec_eq", bb);

    g_ext = new native_decls_reg();
}

void finalize_builtin() {
    delete g_ext;
    delete g_initial_native_decls;
}
}
