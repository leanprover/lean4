/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/kernel_serializer.h"
#include "library/tactic/rewrite_tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
rewrite_element::rewrite_element():m_symm(false), m_unfold(true), m_multiplicity(rewrite_multiplicity::Once) {}

rewrite_element::rewrite_element(name const & l, bool symm, bool unfold, rewrite_multiplicity m,
                                 optional<unsigned> const & n):
    m_lemma(l), m_symm(symm), m_unfold(unfold), m_multiplicity(m), m_num(n) {
}

rewrite_element rewrite_element::mk_unfold(name const & l) {
    return rewrite_element(l, false, true, rewrite_multiplicity::Once, optional<unsigned>());
}

rewrite_element rewrite_element::mk_once(name const & l, bool symm) {
    return rewrite_element(l, symm, false, rewrite_multiplicity::Once, optional<unsigned>());
}

rewrite_element rewrite_element::mk_at_most_n(name const & l, unsigned n, bool symm) {
    return rewrite_element(l, symm, false, rewrite_multiplicity::AtMostN, optional<unsigned>(n));
}

rewrite_element rewrite_element::mk_exactly_n(name const & l, unsigned n, bool symm) {
    return rewrite_element(l, symm, false, rewrite_multiplicity::ExactlyN, optional<unsigned>(n));
}

rewrite_element rewrite_element::mk_zero_or_more(name const & l, bool symm) {
    return rewrite_element(l, symm, false, rewrite_multiplicity::ZeroOrMore, optional<unsigned>());
}

rewrite_element rewrite_element::mk_one_or_more(name const & l, bool symm) {
    return rewrite_element(l, symm, false, rewrite_multiplicity::ZeroOrMore, optional<unsigned>());
}

serializer & operator<<(serializer & s, rewrite_element const & e) {
    s << e.m_lemma << e.m_symm << e.m_unfold << static_cast<char>(e.m_multiplicity);
    if (e.has_num())
        s << e.num();
    return s;
}

deserializer & operator>>(deserializer & d, rewrite_element & e) {
    char multp;
    d >> e.m_lemma >> e.m_symm >> e.m_unfold >> multp;
    e.m_multiplicity = static_cast<rewrite_multiplicity>(multp);
    if (e.has_num())
        e.m_num = d.read_unsigned();
    return d;
}

static expr * g_rewrite_tac                    = nullptr;
static name * g_rewrite_elems_name             = nullptr;
static std::string * g_rewrite_elems_opcode    = nullptr;

[[ noreturn ]] static void throw_re_ex() { throw exception("unexpected occurrence of 'rewrite elements' expression"); }

class rewrite_elements_macro_cell : public macro_definition_cell {
    list<rewrite_element> m_elems;
    location              m_loc;
public:
    rewrite_elements_macro_cell(list<rewrite_element> const & elems, location const & loc):m_elems(elems), m_loc(loc) {}
    virtual name get_name() const { return *g_rewrite_elems_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const { throw_re_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_re_ex(); }
    virtual void write(serializer & s) const {
        s << *g_rewrite_elems_opcode << m_loc;
        write_list<rewrite_element>(s, m_elems);

    }
    list<rewrite_element> const & get_elems() const { return m_elems; }
    location const & get_location() const { return m_loc; }
};

/** \brief Create a macro expression to encapsulate a list of rewrite elements */
expr mk_rewrite_elements(list<rewrite_element> const & e, location const & loc) {
    macro_definition def(new rewrite_elements_macro_cell(e, loc));
    return mk_macro(def);
}

expr mk_rewrite_elements(buffer<rewrite_element> const & e, location const & loc) {
    return mk_rewrite_elements(to_list(e), loc);
}

/** \brief Return true iff \c e is a "macro" that encapsulates a list of rewrite_elements */
bool is_rewrite_elements(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_rewrite_elems_name;
}

/** \brief Copy the rewrite_elements stored in \c e into result.
    \pre is_rewrite_elements(e)
*/
void get_rewrite_elements(expr const & e, buffer<rewrite_element> & result) {
    lean_assert(is_rewrite_elements(e));
    list<rewrite_element> const & l = static_cast<rewrite_elements_macro_cell const*>(macro_def(e).raw())->get_elems();
    to_buffer(l, result);
}

location get_rewrite_location(expr const & e) {
    lean_assert(is_rewrite_elements(e));
    return static_cast<rewrite_elements_macro_cell const*>(macro_def(e).raw())->get_location();
}

expr mk_rewrite_tactic_expr(buffer<rewrite_element> const & elems, location const & loc) {
    return mk_app(*g_rewrite_tac, mk_rewrite_elements(elems, loc));
}

tactic mk_rewrite_tactic(buffer<rewrite_element> const & elems, location const & loc) {
    // TODO(Leo)
    for (auto const & e : elems)
        std::cout << ">> " << e.get_name() << "\n";
    std::cout << "include goal >> " << static_cast<bool>(loc.includes_goal()) << "\n";
    return id_tactic();
}

void initialize_rewrite_tactic() {
    name rewrite_tac_name{"tactic", "rewrite_tac"};
    g_rewrite_tac          = new expr(Const(rewrite_tac_name));
    g_rewrite_elems_name   = new name("rewrite_elements");
    g_rewrite_elems_opcode = new std::string("RWE");
    register_macro_deserializer(*g_rewrite_elems_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    location loc;
                                    d >> loc;
                                    list<rewrite_element> elems = read_list<rewrite_element>(d);
                                    return mk_rewrite_elements(elems, loc);
                                });

    register_tac(rewrite_tac_name,
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'rewrite' tactic, invalid argument");
                     expr arg = get_tactic_expr_expr(app_arg(e));
                     if (!is_rewrite_elements(arg))
                         throw expr_to_tactic_exception(e, "invalid 'rewrite' tactic, invalid argument");
                     buffer<rewrite_element> elems;
                     get_rewrite_elements(arg, elems);
                     location loc = get_rewrite_location(arg);
                     return mk_rewrite_tactic(elems, loc);
                 });
}

void finalize_rewrite_tactic() {
    delete g_rewrite_tac;
    delete g_rewrite_elems_name;
    delete g_rewrite_elems_opcode;
}
}
