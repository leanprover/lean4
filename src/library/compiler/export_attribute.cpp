/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/attribute_manager.h"
#include "library/constants.h"

namespace lean {
struct export_attr_data : public attr_data {
    name m_id;
    export_attr_data(name const & id): m_id(id) {}
    export_attr_data() {}

    virtual unsigned hash() const override { return m_id.hash(); }
    virtual void parse(abstract_parser & p) override { m_id = p.parse_name(); }
    virtual void print(std::ostream & out) override { out << " " << m_id; }
    void write(serializer & s) const { s << m_id; }
    void read(deserializer & d) { m_id = read_name(d); }
};

typedef typed_attribute<export_attr_data> export_attr;

static export_attr const & get_export_attr() {
    return static_cast<export_attr const &>(get_system_attribute("export"));
}

optional<name> get_export_name_for(environment const & env, name const & n) {
    if (auto const & data = get_export_attr().get(env, n)) {
        return optional<name>(data->m_id);
    } else {
        return optional<name>();
    }
}

void initialize_export_attribute() {
    register_system_attribute(export_attr("export", "name to be used by code generators",
                                          [](environment const & env, io_state const &, name const & n, unsigned, bool persistent) {
                                              if (!persistent) throw exception("invalid [export] attribute, must be persistent");
                                              auto const & data = *get_export_attr().get(env, n);
                                              name it = data.m_id;
                                              if (it.is_anonymous()) throw exception("invalid [export] attribute, argument is missing");
                                              while (!it.is_anonymous()) {
                                                  if (!it.is_string()) throw exception("invalid [export] attribute, identifier cannot be numeric");
                                                  it = it.get_prefix();
                                              }
                                              constant_info cinfo = env.get(n);
                                              if (!cinfo.is_definition())
                                                  throw exception("invalid '[export]' use, only definitions can be exported");
                                              return env;
                                          }));
}

void finalize_export_attribute() {
}
}
