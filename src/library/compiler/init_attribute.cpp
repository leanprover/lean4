/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#include "runtime/sstream.h"
#include "library/constants.h"
#include "library/attribute_manager.h"
#include "library/util.h"

namespace lean {
struct init_attr_data : public attr_data {
    name m_init_fn;
    init_attr_data(name const & id): m_init_fn(id) {}
    init_attr_data() {}

    virtual unsigned hash() const override { return m_init_fn.hash(); }
    virtual void parse(expr const & e) override {
        buffer<expr> args; get_app_args(e, args);
        if (args.size() != 1 || !is_const(extract_mdata(args[0])))
            throw parser_error("constant expected", get_pos_info_provider()->get_pos_info_or_some(e));
        m_init_fn = const_name(extract_mdata(args[0]));
    }
    virtual void print(std::ostream & out) override { out << " " << m_init_fn; }
    void write(serializer & s) const { s << m_init_fn; }
    void read(deserializer & d) { m_init_fn = read_name(d); }
};

typedef typed_attribute<init_attr_data> init_attr;

static init_attr const & get_init_attr() {
    return static_cast<init_attr const &>(get_system_attribute("init"));
}

optional<name> get_init_fn_name_for(environment const & env, name const & n) {
    if (auto const & data = get_init_attr().get(env, n)) {
        return optional<name>(data->m_init_fn);
    } else {
        return optional<name>();
    }
}

static optional<expr> get_io_type_arg(expr const & t) {
    if (!is_app(t)) return none_expr();
    if (!is_constant(app_fn(t), get_io_name())) return none_expr();
    return some_expr(app_arg(t));
}

void initialize_init_attribute() {
    register_system_attribute(init_attr("init", "initialization procedure for global references",
                                        [](environment const & env, io_state const &, name const & n, unsigned, bool persistent) {
                                            if (!persistent) throw exception("invalid [init] attribute, it must be persistent");
                                            auto const & data = *get_init_attr().get(env, n);
                                            name init_fn = data.m_init_fn;
                                            optional<constant_info> init_fn_info = env.find(init_fn);
                                            if (!init_fn_info) throw exception(sstream() << "invalid [init] attribute, initialization function '" << init_fn << "' not found");
                                            constant_info n_info = env.get(n);
                                            if (!n_info.is_opaque()) throw exception(sstream() << "invalid [init] attribute, '" << n << "' must be a constant");
                                            expr type = n_info.get_type();
                                            expr init_fn_type = init_fn_info->get_type();
                                            optional<expr> io_arg_type = get_io_type_arg(init_fn_type);
                                            if (!io_arg_type) throw exception(sstream() << "invalid [init] attribute, initialization function '" << init_fn << "' must have type of the form 'io <type>'");
                                            if (type != *io_arg_type) throw exception(sstream() << "invalid [init] attribute, initialization function '" << init_fn << "' must have type of the form 'io <type>' "
                                                                                           << "where '<type>' is the type of '" << n << "'");
                                            /* During code generation, we check whether constants tagged with the `[init]` attribute have arity 0.
                                               We cannot perform this check here because attributes are registered before code generation. */
                                            return env;
                                        }));
}

void finalize_init_attribute() {
}
}
