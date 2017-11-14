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
#include "frontends/lean/structure_instance.h"

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
     { point . x := 10, y := 20 }
  is compiled into
     point.mk 10 20
*/
class structure_instance_macro_cell : public macro_definition_cell {
    name       m_struct;
    bool       m_catchall;
    list<name> m_fields;
public:
    structure_instance_macro_cell(name const & s, bool ca, list<name> const & fs):
        m_struct(s), m_catchall(ca), m_fields(fs) {}
    virtual name get_name() const override { return *g_structure_instance_name; }
    virtual expr check_type(expr const &, abstract_type_context &, bool) const override { throw_se_ex(); }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override { throw_se_ex(); }
    virtual void write(serializer & s) const override {
        s << *g_structure_instance_opcode << m_struct << m_catchall;
        write_list(s, m_fields);
    }
    name const & get_struct() const { return m_struct; }
    bool get_catchall() const { return m_catchall; }
    list<name> const & get_field_names() const { return m_fields; }
    virtual bool operator==(macro_definition_cell const & other) const override {
        if (auto other_ptr = dynamic_cast<structure_instance_macro_cell const *>(&other)) {
            return m_struct == other_ptr->m_struct && m_catchall == other_ptr->m_catchall && m_fields == other_ptr->m_fields;
        } else {
            return false;
        }
    }
};

static expr mk_structure_instance_core(name const & s, bool ca, list<name> const & fs, unsigned num, expr const * args) {
    lean_assert(num >= length(fs));
    macro_definition def(new structure_instance_macro_cell(s, ca, fs));
    return mk_macro(def, num, args);
}

expr mk_structure_instance(name const & s, buffer<name> const & fns, buffer<expr> const & fvs,
                           buffer<expr> const & sources, bool catchall) {
    lean_assert(fns.size() == fvs.size());
    buffer<expr> aux;
    aux.append(fvs);
    aux.append(sources);
    return mk_structure_instance_core(s, catchall, to_list(fns), aux.size(), aux.data());
}

expr mk_structure_instance(structure_instance_info const & info) {
    return mk_structure_instance(info.m_struct_name, info.m_field_names, info.m_field_values, info.m_sources,
                                 info.m_catchall);
}

bool is_structure_instance(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_structure_instance_name;
}

structure_instance_info get_structure_instance_info(expr const & e) {
    lean_assert(is_structure_instance(e));
    structure_instance_info info;
    auto m = static_cast<structure_instance_macro_cell const*>(macro_def(e).raw());
    info.m_struct_name = m->get_struct();
    to_buffer(m->get_field_names(), info.m_field_names);
    unsigned num_fields = info.m_field_names.size();
    for (unsigned i = 0; i < num_fields; i++)
        info.m_field_values.push_back(macro_arg(e, i));
    for (unsigned i = num_fields; i < macro_num_args(e); i++)
        info.m_sources.push_back(macro_arg(e, i));
    info.m_catchall = m->get_catchall();
    return info;
}

void initialize_structure_instance() {
    g_structure_instance_name   = new name("structure instance");
    g_structure_instance_opcode = new std::string("STI");
    register_macro_deserializer(*g_structure_instance_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    list<name> fns;
                                    name s;
                                    bool ca;
                                    d >> s >> ca;
                                    fns = read_list<name>(d);
                                    unsigned len = length(fns);
                                    if (num < len)
                                        throw corrupted_stream_exception();
                                    return mk_structure_instance_core(s, ca, fns, num, args);
                                });
}

void finalize_structure_instance() {
    delete g_structure_instance_opcode;
    delete g_structure_instance_name;
}
}
