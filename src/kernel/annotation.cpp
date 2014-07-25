/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <memory>
#include <string>
#include "util/sstream.h"
#include "kernel/annotation.h"

namespace lean {
static name g_annotation("annotation");

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
    name get_annotation_kind() const { return m_name; }
    virtual name get_name() const { return g_annotation; }
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
static std::unique_ptr<annotation_macros> g_annotation_macros;
annotation_macros & get_annotation_macros() {
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
    return is_macro(e) && macro_def(e).get_name() == g_annotation;
}

bool is_annotation(expr const & e, name const & kind) {
    return is_annotation(e) && static_cast<annotation_macro_definition_cell const*>(macro_def(e).raw())->get_annotation_kind() == kind;
}

expr get_annotation_arg(expr const & e) {
    lean_assert(is_annotation(e));
    return macro_arg(e, 0);
}

static name g_let("let");
static name g_have("have");
register_annotation_fn g_let_annotation(g_let);
register_annotation_fn g_have_annotation(g_have);
expr mk_let_annotation(expr const & e) { return mk_annotation(g_let, e); }
expr mk_have_annotation(expr const & e) { return mk_annotation(g_have, e); }
bool is_let_annotation(expr const & e) { return is_annotation(e, g_let); }
bool is_have_annotation(expr const & e) { return is_annotation(e, g_have); }
}
