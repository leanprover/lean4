/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <memory>
#include <string>
#include "util/sstream.h"
#include "library/annotation.h"

namespace lean {
name const & get_annotation_name() {
    static name g_annotation("annotation");
    return g_annotation;
}

std::string const & get_annotation_opcode() {
    static std::string g_annotation_opcode("Annot");
    return g_annotation_opcode;
}

/** \brief We use a macro to mark expressions that denote "let" and "have"-expressions.
    These marks have no real semantic meaning, but are useful for helping Lean's pretty printer.
*/
class annotation_macro_definition_cell : public macro_definition_cell {
    name m_name;
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid '" << m_name << "' annotation, incorrect number of arguments");
    }
public:
    annotation_macro_definition_cell(name const & n):m_name(n) {}
    name const & get_annotation_kind() const { return m_name; }
    virtual name get_name() const { return get_annotation_name(); }
    virtual format pp(formatter const &) const { return format(m_name); }
    virtual void display(std::ostream & out) const { out << m_name; }
    virtual expr get_type(expr const & m, expr const * arg_types, extension_context &) const {
        check_macro(m);
        return arg_types[0];
    }
    virtual optional<expr> expand(expr const & m, extension_context &) const {
        check_macro(m);
        return some_expr(macro_arg(m, 0));
    }
    virtual void write(serializer & s) const {
        s.write_string(get_annotation_opcode());
        s << m_name;
    }
};

typedef std::unordered_map<name, macro_definition, name_hash, name_eq> annotation_macros;
annotation_macros & get_annotation_macros() {
    static std::unique_ptr<annotation_macros> g_annotation_macros;
    if (!g_annotation_macros) g_annotation_macros.reset(new annotation_macros());
    return *(g_annotation_macros.get());
}

void register_annotation(name const & n) {
     annotation_macros & ms = get_annotation_macros();
    lean_assert(ms.find(n) == ms.end());
    ms.insert(mk_pair(n, macro_definition(new annotation_macro_definition_cell(n))));
}

expr mk_annotation(name const & kind, expr const & e) {
    annotation_macros & ms = get_annotation_macros();
    auto it = ms.find(kind);
    if (it != ms.end()) {
        return mk_macro(it->second, 1, &e);
    } else {
        throw exception(sstream() << "unknown annotation kind '" << kind << "'");
    }
}

bool is_annotation(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == get_annotation_name();
}

name const & get_annotation_kind(expr const & e) {
    lean_assert(is_annotation(e));
    return static_cast<annotation_macro_definition_cell const*>(macro_def(e).raw())->get_annotation_kind();
}

bool is_annotation(expr const & e, name const & kind) {
    return is_annotation(e) && get_annotation_kind(e) == kind;
}

expr const & get_annotation_arg(expr const & e) {
    lean_assert(is_annotation(e));
    return macro_arg(e, 0);
}

bool is_nested_annotation(expr const & e, name const & kind) {
    expr const * it = &e;
    while (is_annotation(*it)) {
        if (get_annotation_kind(*it) == kind)
            return true;
        it = &get_annotation_arg(*it);
    }
    return false;
}

expr const & get_nested_annotation_arg(expr const & e) {
    expr const * it = &e;
    while (is_annotation(*it))
        it = &get_annotation_arg(*it);
    return *it;
}

expr copy_annotations(expr const & from, expr const & to) {
    buffer<expr> trace;
    expr const * it = &from;
    while (is_annotation(*it)) {
        trace.push_back(*it);
        it = &get_annotation_arg(*it);
    }
    expr r     = to;
    unsigned i = trace.size();
    while (i > 0) {
        --i;
        r = copy_tag(trace[i], mk_annotation(get_annotation_kind(trace[i]), r));
    }
    return r;
}

name const & get_have_name() {
    static name g_have("have");
    static register_annotation_fn g_have_annotation(g_have);
    return g_have;
}

name const & get_show_name() {
    static name g_show("show");
    static register_annotation_fn g_show_annotation(g_show);
    return g_show;
}

name const & get_proof_qed_name() {
    static name g_proof_qed("proof-qed");
    static register_annotation_fn g_proof_qed_annotation(g_proof_qed);
    return g_proof_qed;
}

static name g_have_name = get_have_name(); // force 'have' annotation to be registered
static name g_show_name = get_show_name(); // force 'show' annotation to be registered
static name g_proof_qed_name = get_proof_qed_name(); // force 'proof-qed' annotation to be registered

expr mk_have_annotation(expr const & e) { return mk_annotation(get_have_name(), e); }
expr mk_show_annotation(expr const & e) { return mk_annotation(get_show_name(), e); }
expr mk_proof_qed_annotation(expr const & e) { return mk_annotation(get_proof_qed_name(), e); }
bool is_have_annotation(expr const & e) { return is_annotation(e, get_have_name()); }
bool is_show_annotation(expr const & e) { return is_annotation(e, get_show_name()); }
bool is_proof_qed_annotation(expr const & e) { return is_annotation(e, get_proof_qed_name()); }
}
