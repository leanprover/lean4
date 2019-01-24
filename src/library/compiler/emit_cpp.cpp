/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <fstream>
#include "runtime/utf8.h"
#include "library/attribute_manager.h"
#include "library/module.h"
#include "library/compiler/emit_cpp.h"

namespace lean {
struct cppname_attr_data : public attr_data {
    name m_id;
    cppname_attr_data(name const & id): m_id(id) {}
    cppname_attr_data() {}

    virtual unsigned hash() const override { return m_id.hash(); }
    virtual void parse(abstract_parser & p) override { m_id = p.parse_name(); }
    virtual void print(std::ostream & out) override { out << " " << m_id; }
    void write(serializer & s) const { s << m_id; }
    void read(deserializer & d) { m_id = read_name(d); }
};

typedef typed_attribute<cppname_attr_data> cppname_attr;

static cppname_attr const & get_cppname_attr() {
    return static_cast<cppname_attr const &>(get_system_attribute("cppname"));
}

optional<name> get_cppname_for(environment const & env, name const & n) {
    if (auto const & data = get_cppname_attr().get(env, n)) {
        return optional<name>(data->m_id);
    } else {
        return optional<name>();
    }
}

struct emit_cpp_ext : public environment_extension {
    name_map<expr> m_code;
};

struct emit_cpp_ext_reg {
    unsigned m_ext_id;
    emit_cpp_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<emit_cpp_ext>()); }
};

static emit_cpp_ext_reg * g_ext = nullptr;
static emit_cpp_ext const & get_extension(environment const & env) {
    return static_cast<emit_cpp_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, emit_cpp_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<emit_cpp_ext>(ext));
}

environment emit_cpp(environment const & env, comp_decls const & ds) {
    /* Remark: we don't generate C++ code here, but at `print_cpp_code`. In this function
       we simply save the LLNF expression in the emit_cpp_ext.
       Reason: the attributes for `ds` are only applied after the compiler is executed,
       and we need to be able to access the `[cppname]` attribute. */
    emit_cpp_ext ext = get_extension(env);
    for (comp_decl const & d : ds) {
        ext.m_code.insert(d.fst(), d.snd());
    }
   return update(env, ext);
}

void print_cpp_code(std::ofstream & out, environment const & env, module_name const & m, list<module_name> const & deps) {
    out << "// Lean compiler output\n";
    out << "// Module: " << m << "\n";
    out << "// Imports:"; for (module_name const & d : deps) out << " " << d; out << "\n";
    name_map<expr> code = get_extension(env).m_code;
    // TODO(Leo)
    for_each(code, [&](name const & n, expr const &) {
            out << "// " << n;
            if (optional<name> c = get_cppname_for(env, n)) out << " ==> " << *c;
            out << "\n";
        });
}

void initialize_emit_cpp() {
    g_ext = new emit_cpp_ext_reg();
    register_system_attribute(cppname_attr("cppname", "name to be used by C++ code generator",
                                           [](environment const & env, io_state const &, name const &, unsigned, bool persistent) {
                                               if (!persistent) throw exception("invalid [cppname] attribute, must be persistent");
                                               return env;
                                           }));
}

void finalize_emit_cpp() {
    delete g_ext;
}
}
