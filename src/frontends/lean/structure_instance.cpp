/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "library/kernel_serializer.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"

namespace lean {
static name * g_structure_instance_name          = nullptr;
static std::string * g_structure_instance_opcode = nullptr;

[[ noreturn ]] static void throw_se_ex() { throw exception("unexpected occurrence of 'structure instance' expression"); }

/*
  We encode a 'structure instance' expression using a macro.
  This is a trick to avoid creating a new kind of expression.
  'Structure instance' expressions are temporary objects used by the elaborator.
  Example: Given
     structure point (A B : Type) := (x : A) (y : B)
  the structure instance
     { point, x := 10, y := 20 }
  is compiled into
     point.mk 10 20
*/
class structure_instance_macro_cell : public macro_definition_cell {
    name       m_struct;
    list<name> m_fields;
public:
    structure_instance_macro_cell(name const & s, list<name> const & fs):
        m_struct(s), m_fields(fs) {}
    virtual name get_name() const override { return *g_structure_instance_name; }
    virtual expr check_type(expr const &, abstract_type_context &, bool) const override { throw_se_ex(); }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override { throw_se_ex(); }
    virtual void write(serializer & s) const override {
        s << *g_structure_instance_opcode << m_struct;
        write_list(s, m_fields);
    }
    name const & get_struct() const { return m_struct; }
    list<name> const & get_field_names() const { return m_fields; }
    virtual bool operator==(macro_definition_cell const & other) const override {
        if (auto other_ptr = dynamic_cast<structure_instance_macro_cell const *>(&other)) {
            return m_struct == other_ptr->m_struct && m_fields == other_ptr->m_fields;
        } else {
            return false;
        }
    }
};

static expr mk_structure_instance_core(name const & s, list<name> const & fs, unsigned num, expr const * args) {
    lean_assert(num == length(fs) || num == length(fs) + 1);
    macro_definition def(new structure_instance_macro_cell(s, fs));
    return mk_macro(def, num, args);
}

expr mk_structure_instance(name const & s, buffer<name> const & fns, buffer<expr> const & fvs) {
    lean_assert(fns.size() == fvs.size());
    return mk_structure_instance_core(s, to_list(fns), fvs.size(), fvs.data());
}

expr mk_structure_instance(expr const & src, buffer<name> const & fns, buffer<expr> const & fvs) {
    buffer<expr> aux;
    aux.append(fvs);
    aux.push_back(src);
    return mk_structure_instance_core(name(), to_list(fns), aux.size(), aux.data());
}

bool is_structure_instance(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_structure_instance_name;
}

void get_structure_instance_info(expr const & e,
                                 name & struct_name,
                                 optional<expr> & source,
                                 buffer<name> & field_names,
                                 buffer<expr> & field_values) {
    lean_assert(is_structure_instance(e));
    struct_name = static_cast<structure_instance_macro_cell const*>(macro_def(e).raw())->get_struct();
    list<name> const & fns = static_cast<structure_instance_macro_cell const*>(macro_def(e).raw())->get_field_names();
    to_buffer(fns, field_names);
    unsigned num_fields = field_names.size();
    lean_assert(macro_num_args(e) == num_fields || macro_num_args(e) == num_fields+1);
    if (num_fields < macro_num_args(e))
        source = macro_arg(e, num_fields);
    for (unsigned i = 0; i < num_fields; i++)
        field_values.push_back(macro_arg(e, i));
}

void initialize_structure_instance() {
    g_structure_instance_name   = new name("structure instance");
    g_structure_instance_opcode = new std::string("STI");
    register_macro_deserializer(*g_structure_instance_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    list<name> fns;
                                    name s;
                                    d >> s;
                                    fns = read_list<name>(d);
                                    unsigned len = length(fns);
                                    if (num != len + 1 && num != len)
                                        throw corrupted_stream_exception();
                                    return mk_structure_instance_core(s, fns, num, args);
                                });
}

void finalize_structure_instance() {
    delete g_structure_instance_opcode;
    delete g_structure_instance_name;
}
}
