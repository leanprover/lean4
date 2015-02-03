/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/kernel_serializer.h"
#include "library/tactic/rewrite_tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
class unfold_info {
    name      m_name;
    location  m_location;
public:
    unfold_info() {}
    unfold_info(name const & n, location const & loc):m_name(n), m_location(loc) {}
    name const & get_name() const { return m_name; }
    location const & get_location() const { return m_location; }
    friend serializer & operator<<(serializer & s, unfold_info const & elem);
    friend deserializer & operator>>(deserializer & d, unfold_info & e);
};

serializer & operator<<(serializer & s, unfold_info const & e) {
    s << e.m_name << e.m_location;
    return s;
}

deserializer & operator>>(deserializer & d, unfold_info & e) {
    d >> e.m_name >> e.m_location;
    return d;
}

class rewrite_info {
    enum multiplicity { Once, AtMostN, ExactlyN, ZeroOrMore, OneOrMore };
    bool                 m_symm;
    multiplicity         m_multiplicity;
    optional<unsigned>   m_num;
    location             m_location;
    rewrite_info(bool symm, multiplicity m, optional<unsigned> const & n,
                 location const & loc):
        m_symm(symm), m_multiplicity(m), m_num(n), m_location(loc) {}
public:
    rewrite_info():m_symm(false), m_multiplicity(Once) {}
    static rewrite_info mk_once(bool symm, location const & loc) {
        return rewrite_info(symm, Once, optional<unsigned>(), loc);
    }

    static rewrite_info mk_at_most_n(unsigned n, bool symm, location const & loc) {
        return rewrite_info(symm, AtMostN, optional<unsigned>(n), loc);
    }

    static rewrite_info mk_exactly_n(unsigned n, bool symm, location const & loc) {
        return rewrite_info(symm, ExactlyN, optional<unsigned>(n), loc);
    }

    static rewrite_info mk_zero_or_more(bool symm, location const & loc) {
        return rewrite_info(symm, ZeroOrMore, optional<unsigned>(), loc);
    }

    static rewrite_info mk_one_or_more(bool symm, location const & loc) {
        return rewrite_info(symm, ZeroOrMore, optional<unsigned>(), loc);
    }

    bool symm() const {
        return m_symm;
    }

    multiplicity get_multiplicity() const {
        return m_multiplicity;
    }

    bool has_num() const {
        return multiplicity() == AtMostN || multiplicity() == ExactlyN;
    }

    unsigned num() const {
        lean_assert(has_num());
        return *m_num;
    }

    location get_location() const { return m_location; }

    friend serializer & operator<<(serializer & s, rewrite_info const & elem);
    friend deserializer & operator>>(deserializer & d, rewrite_info & e);
};

serializer & operator<<(serializer & s, rewrite_info const & e) {
    s << e.m_symm << static_cast<char>(e.m_multiplicity) << e.m_location;
    if (e.has_num())
        s << e.num();
    return s;
}

deserializer & operator>>(deserializer & d, rewrite_info & e) {
    char multp;
    d >> e.m_symm >> multp >> e.m_location;
    e.m_multiplicity = static_cast<rewrite_info::multiplicity>(multp);
    if (e.has_num())
        e.m_num = d.read_unsigned();
    return d;
}

static expr * g_rewrite_tac                   = nullptr;

static name * g_rewrite_elem_name             = nullptr;
static std::string * g_rewrite_elem_opcode    = nullptr;

static name * g_rewrite_unfold_name             = nullptr;
static std::string * g_rewrite_unfold_opcode    = nullptr;

[[ noreturn ]] static void throw_ru_ex() { throw exception("unexpected occurrence of 'rewrite unfold' expression"); }
[[ noreturn ]] static void throw_re_ex() { throw exception("unexpected occurrence of 'rewrite element' expression"); }

class rewrite_unfold_macro_cell : public macro_definition_cell {
    unfold_info m_info;
public:
    rewrite_unfold_macro_cell(unfold_info const & info):m_info(info) {}
    virtual name get_name() const { return *g_rewrite_unfold_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const { throw_ru_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_ru_ex(); }
    virtual void write(serializer & s) const {
        s << *g_rewrite_unfold_opcode << m_info;
    }
    unfold_info const & get_info() const { return m_info; }
};

expr mk_rewrite_unfold(name const & n, location const & loc) {
    macro_definition def(new rewrite_unfold_macro_cell(unfold_info(n, loc)));
    return mk_macro(def);
}

bool is_rewrite_unfold_step(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_rewrite_unfold_name;
}

class rewrite_element_macro_cell : public macro_definition_cell {
    rewrite_info m_info;
public:
    rewrite_element_macro_cell(rewrite_info const & info):m_info(info) {}
    virtual name get_name() const { return *g_rewrite_elem_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const { throw_re_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_re_ex(); }
    virtual void write(serializer & s) const {
        s << *g_rewrite_elem_opcode << m_info;
    }
    rewrite_info const & get_info() const { return m_info; }
};

expr mk_rw_macro(macro_definition const & def, optional<expr> const & pattern, expr const & H) {
    if (pattern) {
        expr args[2] = {H, *pattern};
        return mk_macro(def, 2, args);
    } else {
        return mk_macro(def, 1, &H);
    }
}

expr mk_rewrite_once(optional<expr> const & pattern, expr const & H, bool symm, location const & loc) {
    macro_definition def(new rewrite_element_macro_cell(rewrite_info::mk_once(symm, loc)));
    return mk_rw_macro(def, pattern, H);
}

expr mk_rewrite_zero_or_more(optional<expr> const & pattern, expr const & H, bool symm, location const & loc) {
    macro_definition def(new rewrite_element_macro_cell(rewrite_info::mk_zero_or_more(symm, loc)));
    return mk_rw_macro(def, pattern, H);
}

expr mk_rewrite_one_or_more(optional<expr> const & pattern, expr const & H, bool symm, location const & loc) {
    macro_definition def(new rewrite_element_macro_cell(rewrite_info::mk_one_or_more(symm, loc)));
    return mk_rw_macro(def, pattern, H);
}

expr mk_rewrite_at_most_n(optional<expr> const & pattern, expr const & H, bool symm, unsigned n, location const & loc) {
    macro_definition def(new rewrite_element_macro_cell(rewrite_info::mk_at_most_n(n, symm, loc)));
    return mk_rw_macro(def, pattern, H);
}

expr mk_rewrite_exactly_n(optional<expr> const & pattern, expr const & H, bool symm, unsigned n, location const & loc) {
    macro_definition def(new rewrite_element_macro_cell(rewrite_info::mk_exactly_n(n, symm, loc)));
    return mk_rw_macro(def, pattern, H);
}

bool is_rewrite_step(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_rewrite_elem_name;
}

bool has_rewrite_pattern(expr const & e) {
    lean_assert(is_rewrite_step(e));
    return macro_num_args(e) == 2;
}

expr const & get_rewrite_rule(expr const & e) {
    lean_assert(is_rewrite_step(e));
    return macro_arg(e, 0);
}

expr const & get_rewrite_pattern(expr const & e) {
    lean_assert(has_rewrite_pattern(e));
    return macro_arg(e, 1);
}

expr mk_rewrite_tactic_expr(buffer<expr> const & elems) {
    lean_assert(std::all_of(elems.begin(), elems.end(), [](expr const & e) {
                return is_rewrite_step(e) || is_rewrite_unfold_step(e);
            }));
    return mk_app(*g_rewrite_tac, mk_expr_list(elems.size(), elems.data()));
}

tactic mk_rewrite_tactic(buffer<expr> const & elems) {
    // TODO(Leo)
    std::cout << "rewrite_tactic\n";
    for (auto const & e : elems) {
        if (is_rewrite_step(e))
            std::cout << ">> " << get_rewrite_rule(e) << "\n";
        else
            std::cout << ">> unfold\n";
    }
    return id_tactic();
}

void initialize_rewrite_tactic() {
    name rewrite_tac_name{"tactic", "rewrite_tac"};
    g_rewrite_tac           = new expr(Const(rewrite_tac_name));
    g_rewrite_unfold_name   = new name("rewrite_unfold");
    g_rewrite_unfold_opcode = new std::string("RWU");
    g_rewrite_elem_name     = new name("rewrite_element");
    g_rewrite_elem_opcode   = new std::string("RWE");
    register_macro_deserializer(*g_rewrite_unfold_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    unfold_info info;
                                    d >> info;
                                    macro_definition def(new rewrite_unfold_macro_cell(info));
                                    return mk_macro(def);
                                });
    register_macro_deserializer(*g_rewrite_elem_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1 && num != 2)
                                        throw corrupted_stream_exception();
                                    rewrite_info info;
                                    d >> info;
                                    macro_definition def(new rewrite_element_macro_cell(info));
                                    return mk_macro(def, num, args);
                                });
    register_tac(rewrite_tac_name,
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     buffer<expr> args;
                     get_tactic_expr_list_elements(app_arg(e), args, "invalid 'rewrite' tactic, invalid argument");
                     for (expr const & arg : args) {
                         if (!is_rewrite_step(arg) && !is_rewrite_unfold_step(arg))
                             throw expr_to_tactic_exception(e, "invalid 'rewrite' tactic, invalid argument");
                     }
                     return mk_rewrite_tactic(args);
                 });
}

void finalize_rewrite_tactic() {
    delete g_rewrite_tac;
    delete g_rewrite_unfold_name;
    delete g_rewrite_unfold_opcode;
    delete g_rewrite_elem_name;
    delete g_rewrite_elem_opcode;
}
}
