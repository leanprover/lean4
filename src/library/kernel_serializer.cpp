/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/object_serializer.h"
#include "kernel/expr.h"
#include "kernel/definition.h"
#include "kernel/max_sharing.h"
#include "library/kernel_serializer.h"

// Procedures for serializing and deserializing kernel objects (levels, exprs, definitions)
namespace lean {
// Universe level serialization
class level_serializer : public object_serializer<level, level::ptr_hash, level::ptr_eq> {
    typedef object_serializer<level, level::ptr_hash, level::ptr_eq> super;
public:
    void write(level const & l) {
        super::write(l, [&]() {
                serializer & s = get_owner();
                auto k = kind(l);
                s << static_cast<char>(k);
                switch (k) {
                case level_kind::Zero:     break;
                case level_kind::Param:    s << param_id(l);   break;
                case level_kind::Global:   s << global_id(l);  break;
                case level_kind::Meta:     s << meta_id(l);    break;
                case level_kind::Max:      write(max_lhs(l));  write(max_rhs(l)); break;
                case level_kind::IMax:     write(imax_lhs(l)); write(imax_rhs(l)); break;
                case level_kind::Succ:     write(succ_of(l));  break;
                }
            });
    }
};

class level_deserializer : public object_deserializer<level> {
    typedef object_deserializer<level> super;
public:
    level read() {
        return super::read([&]() -> level {
                deserializer & d = get_owner();
                auto k = static_cast<level_kind>(d.read_char());
                switch (k) {
                case level_kind::Zero:
                    return mk_level_zero();
                case level_kind::Param:
                    return mk_param_univ(read_name(d));
                case level_kind::Global:
                    return mk_global_univ(read_name(d));
                case level_kind::Meta:
                    return mk_meta_univ(read_name(d));
                case level_kind::Max: {
                    level lhs = read();
                    return mk_max(lhs, read());
                }
                case level_kind::IMax: {
                    level lhs = read();
                    return mk_imax(lhs, read());
                }
                case level_kind::Succ:
                    return mk_succ(read());
                }
                throw_corrupted_file();
            });
    }
};

struct level_sd {
    unsigned m_s_extid;
    unsigned m_d_extid;
    level_sd() {
        m_s_extid = serializer::register_extension([](){
                return std::unique_ptr<serializer::extension>(new level_serializer());
            });
        m_d_extid = deserializer::register_extension([](){
                return std::unique_ptr<deserializer::extension>(new level_deserializer());
            });
    }
};

static level_sd g_level_sd;

serializer & operator<<(serializer & s, level const & n) {
    s.get_extension<level_serializer>(g_level_sd.m_s_extid).write(n);
    return s;
}

level read_level(deserializer & d) { return d.get_extension<level_deserializer>(g_level_sd.m_d_extid).read(); }

serializer & operator<<(serializer & s, levels const & ls) { return write_list<level>(s, ls); }

levels read_levels(deserializer & d) { return read_list<level>(d, read_level); }

// Expression serialization
typedef std::unordered_map<std::string, macro_definition_cell::reader> macro_readers;
static std::unique_ptr<macro_readers> g_macro_readers;
macro_readers & get_macro_readers() {
    if (!g_macro_readers)
        g_macro_readers.reset(new macro_readers());
    return *(g_macro_readers.get());
}

void register_macro_deserializer(std::string const & k, macro_definition_cell::reader rd) {
    macro_readers & readers = get_macro_readers();
    lean_assert(readers.find(k) == readers.end());
    readers[k] = rd;
}

static expr read_macro_definition(deserializer & d, unsigned num, expr const * args) {
    auto k  = d.read_string();
    macro_readers & readers = get_macro_readers();
    auto it = readers.find(k);
    lean_assert(it != readers.end());
    return it->second(d, num, args);
}

serializer & operator<<(serializer & s, expr_binder_info const & i) {
    s.write_bool(i.is_implicit());
    s.write_bool(i.is_cast());
    return s;
}

static expr_binder_info read_expr_binder_info(deserializer & d) {
    bool imp = d.read_bool();
    bool cast = d.read_bool();
    return expr_binder_info(imp, cast);
}

class expr_serializer : public object_serializer<expr, expr_hash_alloc, expr_eqp> {
    typedef object_serializer<expr, expr_hash_alloc, expr_eqp> super;
    max_sharing_fn m_max_sharing_fn;

    void write_core(expr const & a) {
        auto k = a.kind();
        super::write_core(a, static_cast<char>(k), [&]() {
                serializer & s = get_owner();
                switch (k) {
                case expr_kind::Var:
                    s << var_idx(a);
                    break;
                case expr_kind::Constant:
                    s << const_name(a) << const_level_params(a);
                    break;
                case expr_kind::Sort:
                    s << sort_level(a);
                    break;
                case expr_kind::Macro:
                    s << macro_num_args(a);
                    for (unsigned i = 0; i < macro_num_args(a); i++) {
                        write_core(macro_arg(a, i));
                    }
                    macro_def(a).write(s);
                    break;
                case expr_kind::App:
                    write_core(app_fn(a)); write_core(app_arg(a));
                    break;
                case expr_kind::Lambda: case expr_kind::Pi:
                    s << binder_name(a) << binder_info(a); write_core(binder_domain(a)); write_core(binder_body(a));
                    break;
                case expr_kind::Let:
                    s << let_name(a); write_core(let_type(a)); write_core(let_value(a)); write_core(let_body(a));
                    break;
                case expr_kind::Meta: case expr_kind::Local:
                    s << mlocal_name(a); write_core(mlocal_type(a));
                    break;
                }
            });
    }
public:
    void write(expr const & a) {
        write_core(m_max_sharing_fn(a));
    }
};

class expr_deserializer : public object_deserializer<expr> {
    typedef object_deserializer<expr> super;
public:
    expr read_binder(expr_kind k) {
        deserializer & d = get_owner();
        name n             = read_name(d);
        expr_binder_info i = read_expr_binder_info(d);
        expr t             = read();
        return mk_binder(k, n, t, read(), i);
    }

    expr read() {
        return super::read_core([&](char c) {
                deserializer & d = get_owner();
                auto k = static_cast<expr_kind>(c);
                switch (k) {
                case expr_kind::Var:
                    return mk_var(d.read_unsigned());
                case expr_kind::Constant: {
                    auto n = read_name(d);
                    return mk_constant(n, read_levels(d));
                }
                case expr_kind::Sort:
                    return mk_sort(read_level(d));
                case expr_kind::Macro: {
                    unsigned n = d.read_unsigned();
                    buffer<expr> args;
                    for (unsigned i = 0; i < n; i++) {
                        args.push_back(read());
                    }
                    return read_macro_definition(d, args.size(), args.data());
                }
                case expr_kind::App: {
                    expr f = read();
                    return mk_app(f, read());
                }
                case expr_kind::Lambda: case expr_kind::Pi:
                    return read_binder(k);
                case expr_kind::Let: {
                    name n = read_name(d);
                    expr t = read();
                    expr v = read();
                    return mk_let(n, t, v, read());
                }
                case expr_kind::Meta: {
                    name n = read_name(d);
                    return mk_metavar(n, read());
                }
                case expr_kind::Local: {
                    name n = read_name(d);
                    return mk_local(n, read());
                }}
                throw_corrupted_file(); // LCOV_EXCL_LINE
            });
    }
};

struct expr_sd {
    unsigned m_s_extid;
    unsigned m_d_extid;
    expr_sd() {
        m_s_extid = serializer::register_extension([](){ return std::unique_ptr<serializer::extension>(new expr_serializer()); });
        m_d_extid = deserializer::register_extension([](){ return std::unique_ptr<deserializer::extension>(new expr_deserializer()); });
    }
};
static expr_sd g_expr_sd;

serializer & operator<<(serializer & s, expr const & n) {
    s.get_extension<expr_serializer>(g_expr_sd.m_s_extid).write(n);
    return s;
}

expr read_expr(deserializer & d) {
    return d.get_extension<expr_deserializer>(g_expr_sd.m_d_extid).read();
}

// Definition serialization
static serializer & operator<<(serializer & s, param_names const & ps) { return write_list<name>(s, ps); }
static param_names read_params(deserializer & d) { return read_list<name>(d); }
serializer & operator<<(serializer & s, definition const & d) {
    char k = 0;
    if (d.is_definition()) {
        k |= 1;
        if (d.is_opaque())
            k |= 2;
        if (d.use_conv_opt())
            k |= 4;
    }
    if (d.is_theorem())
        k |= 8;
    s << k << d.get_name() << d.get_params() << d.get_type();
    if (d.is_definition()) {
        s << d.get_value();
        if (!d.is_theorem())
            s << d.get_weight();
    }
    return s;
}

definition read_definition(deserializer & d, unsigned module_idx) {
    char k = d.read_char();
    bool has_value  = (k & 1) != 0;
    bool is_theorem = (k & 8) != 0;
    name n          = read_name(d);
    param_names ps  = read_params(d);
    expr t          = read_expr(d);
    if (has_value) {
        expr v      = read_expr(d);
        if (is_theorem) {
            return mk_theorem(n, ps, t, v);
        } else {
            unsigned w        = d.read_unsigned();
            bool is_opaque    = (k & 2) != 0;
            bool use_conv_opt = (k & 4) != 0;
            return mk_definition(n, ps, t, v, is_opaque, w, module_idx, use_conv_opt);
        }
    } else {
        if (is_theorem)
            return mk_axiom(n, ps, t);
        else
            return mk_var_decl(n, ps, t);
    }
}
}
