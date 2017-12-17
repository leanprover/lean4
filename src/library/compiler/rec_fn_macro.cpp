/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "library/kernel_serializer.h"
#include "library/compiler/rec_fn_macro.h"
#include "kernel/abstract_type_context.h"

namespace lean {
static name * g_rec_fn_macro_id = nullptr;
static std::string * g_rec_fn_opcode = nullptr;

name const & get_rec_fn_macro_id() { return *g_rec_fn_macro_id; }
std::string const & get_rec_fn_opcode() { return *g_rec_fn_opcode; }

/** \brief We use a macro to mark recursive function calls. */
class rec_fn_macro_definition_cell : public macro_definition_cell {
    name m_name;

    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid recursive function '" << m_name << "' macro, incorrect number of arguments");
    }

public:
    rec_fn_macro_definition_cell(name const & n):m_name(n) {}

    name const & get_rec_fn_name() const { return m_name; }
    virtual name get_name() const override { return get_rec_fn_macro_id(); }

    virtual void display(std::ostream & out) const override { out << m_name; }

    virtual expr check_type(expr const & m, abstract_type_context & tc, bool) const override {
        if (tc.is_trusted_only()) {
            throw exception("rec_fn_macro only allowed in meta definitions");
        }
        check_macro(m);
        return macro_arg(m, 0);
    }

    virtual optional<expr> expand(expr const &, abstract_type_context &) const override {
        return none_expr();
    }

    virtual void write(serializer & s) const override {
        s.write_string(get_rec_fn_opcode());
        s << m_name;
    }

    virtual bool operator==(macro_definition_cell const & other) const override {
        if (auto other_ptr = dynamic_cast<rec_fn_macro_definition_cell const *>(&other)) {
            return m_name == other_ptr->m_name;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const override {
        return ::lean::hash(m_name.hash(), get_rec_fn_macro_id().hash());
    }
};

expr mk_rec_fn_macro(name const & fn_name, expr const & type) {
    macro_definition def(new rec_fn_macro_definition_cell(fn_name));
    return mk_macro(def, 1, &type);
}

bool is_rec_fn_macro(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == get_rec_fn_macro_id();
}

name const & get_rec_fn_name(expr const & e) {
    lean_assert(is_rec_fn_macro(e));
    return static_cast<rec_fn_macro_definition_cell const*>(macro_def(e).raw())->get_rec_fn_name();
}

expr const & get_rec_fn_type(expr const & e) {
    lean_assert(is_rec_fn_macro(e));
    return macro_arg(e, 0);
}

void initialize_rec_fn_macro() {
    g_rec_fn_macro_id = new name("rec_fn");
    g_rec_fn_opcode   = new std::string("RecFn");

    register_macro_deserializer(get_rec_fn_opcode(),
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    name fn;
                                    d >> fn;
                                    return mk_rec_fn_macro(fn, args[0]);
                                });
}

void finalize_rec_fn_macro() {
    delete g_rec_fn_opcode;
    delete g_rec_fn_macro_id;
}
}
