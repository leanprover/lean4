/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/attribute_manager.h"
#include "library/constants.h"
#include "library/util.h"

namespace lean {
struct implemented_by_attr_data : public attr_data {
    name m_id;
    implemented_by_attr_data(name const & id): m_id(id) {}
    implemented_by_attr_data() {}

    virtual unsigned hash() const override { return m_id.hash(); }
    virtual void parse(expr const & e) override {
        buffer<expr> args; get_app_args(e, args);
        if (args.size() != 1 || !is_const(extract_mdata(args[0])))
            throw parser_error("constant expected", get_pos_info_provider()->get_pos_info_or_some(e));
        m_id = const_name(extract_mdata(args[0]));
    }
    virtual void print(std::ostream & out) override { out << " " << m_id; }
    void write(serializer & s) const { s << m_id; }
    void read(deserializer & d) { m_id = read_name(d); }
};

typedef typed_attribute<implemented_by_attr_data> implemented_by_attr;

static implemented_by_attr const & get_implemented_by_attr() {
    return static_cast<implemented_by_attr const &>(get_system_attribute("implementedBy"));
}

optional<name> get_implemented_by_attribute(environment const & env, name const & n) {
    if (auto const & data = get_implemented_by_attr().get(env, n)) {
        return optional<name>(data->m_id);
    } else {
        return optional<name>();
    }
}

void initialize_implemented_by_attribute() {
    register_system_attribute(implemented_by_attr("implementedBy", "name of the Lean (probably unsafe) function that implements opaque constant",
                                          [](environment const & env, io_state const &, name const & n, unsigned, bool persistent) {
                                              if (!persistent) throw exception("invalid [implementedBy] attribute, must be persistent");
                                              auto const & data = *get_implemented_by_attr().get(env, n);
                                              name impl = data.m_id;
                                              if (impl.is_anonymous()) throw exception("invalid [implementedBy] attribute, argument is missing");
                                              optional<constant_info> cinfo_impl = env.find(impl);
                                              if (!cinfo_impl) throw exception("invalid [implementedBy] attribute, unknown function");
                                              constant_info cinfo = env.get(n);
                                              if (!cinfo.is_opaque())
                                                  throw exception("invalid '[implementedBy]' use, only opaque constants may use this attribute");
                                              /* Remark: the following checks can be improved:
                                                 1- We can use definitional equality instead of structural equality.
                                                 2- We can abstract actual universe parameter names.

                                                 That being said, the current check seems to be good enough for now.
                                              */
                                              if (cinfo_impl->get_type() != cinfo.get_type())
                                                  throw exception("invalid '[implementedBy]' use, type mismatch");
                                              if (cinfo_impl->get_lparams() != cinfo.get_lparams())
                                                  throw exception("invalid '[implementedBy]' use, universe parameters mismatch");
                                              return env;
                                          }));
}

void finalize_implemented_by_attribute() {
}
}
