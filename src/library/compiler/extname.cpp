/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/attribute_manager.h"
#include "library/constants.h"

namespace lean {
struct extname_attr_data : public attr_data {
    name m_id;
    extname_attr_data(name const & id): m_id(id) {}
    extname_attr_data() {}

    virtual unsigned hash() const override { return m_id.hash(); }
    virtual void parse(abstract_parser & p) override { m_id = p.parse_name(); }
    virtual void print(std::ostream & out) override { out << " " << m_id; }
    void write(serializer & s) const { s << m_id; }
    void read(deserializer & d) { m_id = read_name(d); }
};

typedef typed_attribute<extname_attr_data> extname_attr;

static extname_attr const & get_extname_attr() {
    return static_cast<extname_attr const &>(get_system_attribute("extname"));
}

optional<name> get_extname_for(environment const & env, name const & n) {
    if (auto const & data = get_extname_attr().get(env, n)) {
        return optional<name>(data->m_id);
    } else {
        return optional<name>();
    }
}

void initialize_extname() {
    register_system_attribute(extname_attr("extname", "name to be used by code generators",
                                           [](environment const & env, io_state const &, name const & n, unsigned, bool persistent) {
                                               if (!persistent) throw exception("invalid [extname] attribute, must be persistent");
                                               auto const & data = *get_extname_attr().get(env, n);
                                               name it = data.m_id;
                                               if (it.is_anonymous()) throw exception("invalid [extname] attribute, argument is missing");
                                               while (!it.is_anonymous()) {
                                                   if (!it.is_string()) throw exception("invalid [extname] attribute, identifier cannot be numeric");
                                                   it = it.get_prefix();
                                               }
                                               constant_info cinfo = env.get(n);
                                               if (!cinfo.is_definition()) {
                                                   throw exception("invalid '[extname]' use, only definitions can be use this attribute");
                                               }
                                               return env;
                                           }));
}

void finalize_extname() {
}
}
