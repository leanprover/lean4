/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/sstream.h"
#include "util/list_fn.h"
#include "util/fresh_name.h"
#include "kernel/expr.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "library/exception.h"
#include "library/kernel_serializer.h"
#include "library/io_state_stream.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/locals.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/pp_options.h"
#include "library/equations_compiler/equations.h"

namespace lean {
static name * g_equations_name                 = nullptr;
static name * g_equation_name                  = nullptr;
static name * g_no_equation_name               = nullptr;
static name * g_inaccessible_name              = nullptr;
static name * g_equations_result_name          = nullptr;
static name * g_as_pattern_name                = nullptr;
static std::string * g_equations_opcode        = nullptr;
static std::string * g_equation_opcode         = nullptr;
static std::string * g_no_equation_opcode      = nullptr;
static std::string * g_equations_result_opcode = nullptr;
static std::string * g_as_pattern_opcode       = nullptr;

[[ noreturn ]] static void throw_asp_ex() { throw exception("unexpected occurrence of 'equations' expression"); }

class as_pattern_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const override { return *g_as_pattern_name; }
    virtual expr check_type(expr const &, abstract_type_context &, bool) const override { throw_asp_ex(); }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override { throw_asp_ex(); }
    virtual void write(serializer & s) const override { s << *g_as_pattern_opcode; }
};

bool operator==(equations_header const & h1, equations_header const & h2) {
    return
        h1.m_num_fns == h2.m_num_fns &&
        h1.m_fn_names == h2.m_fn_names &&
        h1.m_fn_actual_names == h2.m_fn_actual_names &&
        h1.m_is_private == h2.m_is_private &&
        h1.m_is_lemma == h2.m_is_lemma &&
        h1.m_is_meta == h2.m_is_meta &&
        h1.m_is_noncomputable == h2.m_is_noncomputable &&
        h1.m_aux_lemmas == h2.m_aux_lemmas &&
        h1.m_prev_errors == h2.m_prev_errors &&
        h1.m_gen_code == h2.m_gen_code;
}

[[ noreturn ]] static void throw_eqs_ex() { throw exception("unexpected occurrence of 'equations' expression"); }

class equations_macro_cell : public macro_definition_cell {
    equations_header m_header;
public:
    equations_macro_cell(equations_header const & h):m_header(h) {}
    virtual name get_name() const override { return *g_equations_name; }
    virtual expr check_type(expr const &, abstract_type_context &, bool) const override { throw_eqs_ex(); }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override { throw_eqs_ex(); }
    virtual void write(serializer & s) const override {
        s << *g_equations_opcode << m_header.m_num_fns << m_header.m_is_private << m_header.m_is_meta
          << m_header.m_is_noncomputable << m_header.m_is_lemma << m_header.m_aux_lemmas << m_header.m_prev_errors << m_header.m_gen_code;
        write_list(s, m_header.m_fn_names);
        write_list(s, m_header.m_fn_actual_names);
    }
    virtual bool operator==(macro_definition_cell const & other) const override {
        if (auto other_ptr = dynamic_cast<equations_macro_cell const *>(&other)) {
            return m_header == other_ptr->m_header;
        } else {
            return false;
        }
    }
    equations_header const & get_header() const { return m_header; }
};

class equation_base_macro_cell :
public macro_definition_cell {
public:
    virtual expr check_type(expr const &, abstract_type_context &, bool) const override {
        expr dummy = mk_Prop();
        return dummy;
    }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override {
        expr dummy = mk_Type();
        return some_expr(dummy);
    }
};

class equation_macro_cell : public equation_base_macro_cell {
    bool m_ignore_if_unused;
public:
    equation_macro_cell(bool ignore_if_unused):m_ignore_if_unused(ignore_if_unused) {}
    virtual name get_name() const override { return *g_equation_name; }
    virtual void write(serializer & s) const override {
        s.write_string(*g_equation_opcode);
        s.write_bool(m_ignore_if_unused);
    }
    virtual bool operator==(macro_definition_cell const & other) const override {
        if (auto other_ptr = dynamic_cast<equation_macro_cell const *>(&other)) {
            return m_ignore_if_unused == other_ptr->m_ignore_if_unused;
        } else {
            return false;
        }
    }
    bool ignore_if_unused() const { return m_ignore_if_unused; }
};

// This is just a placeholder to indicate no equations were provided
class no_equation_macro_cell : public equation_base_macro_cell {
public:
    virtual name get_name() const override { return *g_no_equation_name; }
    virtual void write(serializer & s) const override { s.write_string(*g_no_equation_opcode); }
};

static macro_definition * g_as_pattern                = nullptr;
static macro_definition * g_equation                  = nullptr;
static macro_definition * g_equation_ignore_if_unused = nullptr;
static macro_definition * g_no_equation               = nullptr;

bool is_equation(expr const & e) {
    return is_macro(e) && dynamic_cast<equation_macro_cell const *>(macro_def(e).raw());
}

bool ignore_equation_if_unused(expr const & e) {
    lean_assert(is_equation(e));
    return static_cast<equation_macro_cell const *>(macro_def(e).raw())->ignore_if_unused();
}

bool is_lambda_equation(expr const & e) {
    if (is_lambda(e))
        return is_lambda_equation(binding_body(e));
    else
        return is_equation(e);
}

expr const & equation_lhs(expr const & e) { lean_assert(is_equation(e)); return macro_arg(e, 0); }
expr const & equation_rhs(expr const & e) { lean_assert(is_equation(e)); return macro_arg(e, 1); }
expr mk_equation(expr const & lhs, expr const & rhs, bool ignore_if_unused) {
    expr args[2] = { lhs, rhs };
    if (ignore_if_unused)
        return mk_macro(*g_equation_ignore_if_unused, 2, args);
    else
        return mk_macro(*g_equation, 2, args);
}
expr mk_no_equation() { return mk_macro(*g_no_equation); }
bool is_no_equation(expr const & e) { return is_macro(e) && macro_def(e) == *g_no_equation; }

bool is_lambda_no_equation(expr const & e) {
    if (is_lambda(e))
        return is_lambda_no_equation(binding_body(e));
    else
        return is_no_equation(e);
}

expr mk_inaccessible(expr const & e) { return mk_annotation(*g_inaccessible_name, e); }
bool is_inaccessible(expr const & e) { return is_annotation(e, *g_inaccessible_name); }

expr mk_as_pattern(expr const & lhs, expr const & rhs) {
    expr args[2] = {lhs, rhs};
    return mk_macro(*g_as_pattern, 2, args);
}
bool is_as_pattern(expr const & e) {
    return is_macro(e) && macro_def(e) == *g_as_pattern;
}
expr get_as_pattern_lhs(expr const & e) {
    lean_assert(is_as_pattern(e));
    return macro_arg(e, 0);
}
expr get_as_pattern_rhs(expr const & e) {
    lean_assert(is_as_pattern(e));
    return macro_arg(e, 1);
}

bool is_equations(expr const & e) { return is_macro(e) && macro_def(e).get_name() == *g_equations_name; }
bool is_wf_equations_core(expr const & e) {
    lean_assert(is_equations(e));
    return macro_num_args(e) >= 2 && !is_lambda_equation(macro_arg(e, macro_num_args(e) - 1));
}
bool is_wf_equations(expr const & e) { return is_equations(e) && is_wf_equations_core(e); }
unsigned equations_size(expr const & e) {
    lean_assert(is_equations(e));
    if (is_wf_equations_core(e))
        return macro_num_args(e) - 1;
    else
        return macro_num_args(e);
}
equations_header const & get_equations_header(expr const & e) {
    lean_assert(is_equations(e));
    return static_cast<equations_macro_cell const*>(macro_def(e).raw())->get_header();
}
unsigned equations_num_fns(expr const & e) {
    return get_equations_header(e).m_num_fns;
}
expr const & equations_wf_tactics(expr const & e) {
    lean_assert(is_wf_equations(e));
    return macro_arg(e, macro_num_args(e) - 1);
}

void to_equations(expr const & e, buffer<expr> & eqns) {
    lean_assert(is_equations(e));
    unsigned sz = equations_size(e);
    for (unsigned i = 0; i < sz; i++)
        eqns.push_back(macro_arg(e, i));
}
expr mk_equations(equations_header const & h, unsigned num_eqs, expr const * eqs) {
    lean_assert(h.m_num_fns > 0);
    lean_assert(num_eqs > 0);
    lean_assert(std::all_of(eqs, eqs+num_eqs, [](expr const & e) {
                return is_lambda_equation(e) || is_lambda_no_equation(e);
            }));
    macro_definition def(new equations_macro_cell(h));
    return mk_macro(def, num_eqs, eqs);
}
expr mk_equations(equations_header const & h, unsigned num_eqs, expr const * eqs, expr const & tacs) {
    lean_assert(h.m_num_fns > 0);
    lean_assert(num_eqs > 0);
    lean_assert(std::all_of(eqs, eqs+num_eqs, is_lambda_equation));
    buffer<expr> args;
    args.append(num_eqs, eqs);
    args.push_back(tacs);
    macro_definition def(new equations_macro_cell(h));
    return mk_macro(def, args.size(), args.data());
}
expr update_equations(expr const & eqns, buffer<expr> const & new_eqs) {
    lean_assert(is_equations(eqns));
    lean_assert(!new_eqs.empty());
    if (is_wf_equations(eqns)) {
        return copy_tag(eqns, mk_equations(get_equations_header(eqns), new_eqs.size(), new_eqs.data(),
                                           equations_wf_tactics(eqns)));
    } else {
        return copy_tag(eqns, mk_equations(get_equations_header(eqns), new_eqs.size(), new_eqs.data()));
    }
}

expr update_equations(expr const & eqns, equations_header const & header) {
    buffer<expr> eqs;
    to_equations(eqns, eqs);
    if (is_wf_equations(eqns)) {
        return copy_tag(eqns, mk_equations(header, eqs.size(), eqs.data(),
                                           equations_wf_tactics(eqns)));
    } else {
        return copy_tag(eqns, mk_equations(header, eqs.size(), eqs.data()));
    }
}

expr remove_wf_annotation_from_equations(expr const & eqns) {
    if (is_wf_equations(eqns)) {
        buffer<expr> eqs;
        to_equations(eqns, eqs);
        return copy_tag(eqns, mk_equations(get_equations_header(eqns), eqs.size(), eqs.data()));
    } else {
        return eqns;
    }
}

// Auxiliary macro used to store the result of a set of equations defining a mutually recursive
// definition.
class equations_result_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_equations_result_name; }
    virtual expr check_type(expr const & m, abstract_type_context & ctx, bool infer_only) const {
        return ctx.check(macro_arg(m, 0), infer_only);
    }
    virtual optional<expr> expand(expr const & m, abstract_type_context &) const {
        return some_expr(macro_arg(m, 0));
    }
    virtual void write(serializer & s) const { s << *g_equations_result_opcode; }
};

static macro_definition * g_equations_result = nullptr;

expr mk_equations_result(unsigned n, expr const * rs) {
    return mk_macro(*g_equations_result, n, rs);
}

bool is_equations_result(expr const & e) { return is_macro(e) && macro_def(e) == *g_equations_result; }
unsigned get_equations_result_size(expr const & e) { return macro_num_args(e); }
expr const & get_equations_result(expr const & e, unsigned i) { return macro_arg(e, i); }

void initialize_equations() {
    g_equations_name            = new name("equations");
    g_equation_name             = new name("equation");
    g_no_equation_name          = new name("no_equation");
    g_inaccessible_name         = new name("innaccessible");
    g_equations_result_name     = new name("equations_result");
    g_as_pattern_name           = new name("as_pattern");
    g_equation                  = new macro_definition(new equation_macro_cell(false));
    g_equation_ignore_if_unused = new macro_definition(new equation_macro_cell(true));
    g_no_equation               = new macro_definition(new no_equation_macro_cell());
    g_equations_result          = new macro_definition(new equations_result_macro_cell());
    g_as_pattern                = new macro_definition(new as_pattern_macro_cell());
    g_equations_opcode          = new std::string("Eqns");
    g_equation_opcode           = new std::string("Eqn");
    g_no_equation_opcode        = new std::string("NEqn");
    g_equations_result_opcode   = new std::string("EqnR");
    g_as_pattern_opcode         = new std::string("AsPat");
    register_annotation(*g_inaccessible_name);
    register_macro_deserializer(*g_equations_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    equations_header h;
                                    d >> h.m_num_fns >> h.m_is_private >> h.m_is_meta >> h.m_is_noncomputable
                                      >> h.m_is_lemma >> h.m_aux_lemmas >> h.m_prev_errors >> h.m_gen_code;
                                    h.m_fn_names = read_list<name>(d);
                                    h.m_fn_actual_names = read_list<name>(d);
                                    if (num == 0 || h.m_num_fns == 0)
                                        throw corrupted_stream_exception();
                                    if (!is_lambda_equation(args[num-1]) && !is_lambda_no_equation(args[num-1])) {
                                        if (num <= 1)
                                            throw corrupted_stream_exception();
                                        return mk_equations(h, num-1, args, args[num-1]);
                                    } else {
                                        return mk_equations(h, num, args);
                                    }
                                });
    register_macro_deserializer(*g_equation_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    bool ignore_if_unused;
                                    d >> ignore_if_unused;
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    return mk_equation(args[0], args[1], ignore_if_unused);
                                });
    register_macro_deserializer(*g_no_equation_opcode,
                                [](deserializer &, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    return mk_no_equation();
                                });
    register_macro_deserializer(*g_equations_result_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    return mk_equations_result(num, args);
                                });
    register_macro_deserializer(*g_as_pattern_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    return mk_as_pattern(args[0], args[1]);
                                });
}

void finalize_equations() {
    delete g_as_pattern_opcode;
    delete g_equations_result_opcode;
    delete g_equation_opcode;
    delete g_no_equation_opcode;
    delete g_equations_opcode;
    delete g_as_pattern;
    delete g_equations_result;
    delete g_equation;
    delete g_equation_ignore_if_unused;
    delete g_no_equation;
    delete g_as_pattern_name;
    delete g_equations_result_name;
    delete g_equations_name;
    delete g_equation_name;
    delete g_no_equation_name;
    delete g_inaccessible_name;
}
}
