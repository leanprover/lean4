/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/sorry.h"
#include <string>
#include <kernel/find_fn.h>
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include "library/module.h"
#include "kernel/for_each_fn.h"
#include "library/kernel_serializer.h"

namespace lean {
static name * g_sorry_name = nullptr;
static std::string * g_sorry_opcode = nullptr;

class sorry_macro_cell : public macro_definition_cell {
    bool m_synthetic;

public:
    sorry_macro_cell(bool synthetic) : m_synthetic(synthetic) {}

    bool is_synthetic() const { return m_synthetic; }

    virtual name get_name() const override { return *g_sorry_name; }

    unsigned int trust_level() const override { return 1; }

    virtual expr check_type(expr const & sry, abstract_type_context & ctx, bool infer_only) const override {
        if (!is_sorry(sry)) throw exception("invalid sorry macro");
        auto sort = ctx.whnf(ctx.check(sorry_type(sry), infer_only));
        if (!is_sort(sort)) throw exception("type of sorry macro is not a sort");
        return sorry_type(sry);
    }

    virtual optional<expr> expand(expr const &, abstract_type_context &) const override {
        return {};
    }

    virtual void write(serializer & s) const override {
        s.write_string(*g_sorry_opcode);
        s.write_bool(m_synthetic);
    }
};

void initialize_sorry() {
    g_sorry_name = new name{"sorry"};
    g_sorry_opcode = new std::string("Sorry");

    register_macro_deserializer(*g_sorry_opcode,
        [] (deserializer & d, unsigned num, expr const * args) {
            if (num != 1) throw corrupted_stream_exception();
            bool synthetic = d.read_bool();
            return mk_sorry(args[0], synthetic);
        });
}

void finalize_sorry() {
    delete g_sorry_opcode;
    delete g_sorry_name;
}

expr mk_sorry(expr const & ty, bool synthetic) {
    return mk_macro(macro_definition(new sorry_macro_cell(synthetic)), 1, &ty);
}
bool is_sorry(expr const & e) {
    return is_macro(e) && macro_num_args(e) == 1 && dynamic_cast<sorry_macro_cell const *>(macro_def(e).raw());
}
bool is_synthetic_sorry(expr const & e) {
    return is_sorry(e) && static_cast<sorry_macro_cell const *>(macro_def(e).raw())->is_synthetic();
}

bool has_synthetic_sorry(expr const & ex) {
    return !!find(ex, [] (expr const & e, unsigned) { return is_synthetic_sorry(e); });
}

bool has_sorry(expr const & ex) {
    return !!find(ex, [] (expr const & e, unsigned) { return is_sorry(e); });
}

bool has_sorry(declaration const & decl) {
    return has_sorry(decl.get_type()) || (decl.is_definition() && has_sorry(decl.get_value()));
}

expr const & sorry_type(expr const & sry) {
    return macro_arg(sry, 0);
}

bool has_sorry(environment const & env) {
    bool found_sorry = false;
    env.for_each_declaration([&] (declaration const & decl) {
        if (!found_sorry && has_sorry(decl)) found_sorry = true;
    });
    return found_sorry;
}
}
