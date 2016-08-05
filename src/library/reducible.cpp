/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "library/kernel_serializer.h"
#include "library/scoped_ext.h"
#include "library/reducible.h"
#include "library/attribute_manager.h"

namespace lean {
struct reducibility_attribute_data : public attr_data {
    reducible_status m_status;
    reducibility_attribute_data() {}
    reducibility_attribute_data(reducible_status status) : m_status(status) {}

    virtual unsigned hash() const override {
        return static_cast<unsigned>(m_status);
    }
    void write(serializer & s) const {
        s << static_cast<char>(m_status);
    }
    void read(deserializer & d) {
        char c;
        d >> c;
        m_status = static_cast<reducible_status>(c);
    }
};

template class typed_attribute<reducibility_attribute_data>;
typedef typed_attribute<reducibility_attribute_data> reducibility_attribute;

static reducibility_attribute const & get_reducibility_attribute() {
    return static_cast<reducibility_attribute const &>(get_attribute("reducibility"));
}

class proxy_attribute : public basic_attribute {
private:
    reducible_status m_status;
public:
    proxy_attribute(char const * id, char const * descr, reducible_status m_status) : basic_attribute(id, descr),
                                                                                      m_status(m_status) {}

    virtual attr_data_ptr get(environment const & env, name const & n) const override {
        if (auto data = get_reducibility_attribute().get_data(env, n)) {
            if (data->m_status == m_status)
                return attr_data_ptr(new attr_data);
        }
        return {};
    }
    virtual environment set(environment const & env, io_state const & ios, name const & n, bool persistent) const override {
        declaration const & d = env.get(n);
        if (!d.is_definition())
            throw exception(sstream() << "invalid reducible command, '" << n << "' is not a definition");
        return get_reducibility_attribute().set(env, ios, n, { m_status }, persistent);
    }

    virtual void get_instances(environment const & env, buffer<name> & r) const override {
        buffer<name> tmp;
        get_reducibility_attribute().get_instances(env, tmp);
        for (name const & n : tmp)
            if (get(env, n))
                r.push_back(n);
    }
};

void initialize_reducible() {
    register_attribute(reducibility_attribute("reducibility", "internal attribute for storing reducibility"));

    register_attribute(proxy_attribute("reducible", "reducible", reducible_status::Reducible));
    register_attribute(proxy_attribute("semireducible", "semireducible", reducible_status::Semireducible));
    register_attribute(proxy_attribute("irreducible", "irreducible", reducible_status::Irreducible));

    register_incompatible("reducible", "semireducible");
    register_incompatible("reducible", "irreducible");
    register_incompatible("semireducible", "irreducible");
}

void finalize_reducible() {
}

environment set_reducible(environment const & env, name const & n, reducible_status s, bool persistent) {
    return get_reducibility_attribute().set(env, get_dummy_ios(), n, { s }, persistent);
}

reducible_status get_reducible_status(environment const & env, name const & n) {
    auto data = get_reducibility_attribute().get_data(env, n);
    if (data)
        return data->m_status;
    return reducible_status::Semireducible;
}

name_predicate mk_not_reducible_pred(environment const & env) {
    return [=](name const & n) { // NOLINT
        return !has_attribute(env, "reducible", n);
    };
}

name_predicate mk_irreducible_pred(environment const & env) {
    return [=](name const & n) { // NOLINT
        return has_attribute(env, "irreducible", n);
    };
}

old_type_checker_ptr mk_type_checker(environment const & env, reducible_behavior rb) {
    switch (rb) {
    case UnfoldReducible:
        return mk_type_checker(env, mk_not_reducible_pred(env));
    case UnfoldSemireducible:
        return mk_type_checker(env, mk_irreducible_pred(env));
    }
    lean_unreachable();
}

old_type_checker_ptr mk_opaque_type_checker(environment const & env) {
    return mk_type_checker(env, [](name const &) { return true; });
}
}
