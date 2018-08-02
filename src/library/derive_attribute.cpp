/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include <kernel/instantiate.h>
#include "runtime/sstream.h"
#include "kernel/find_fn.h"
#include "kernel/old_type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/user_recursors.h"
#include "library/aux_recursors.h"
#include "library/attribute_manager.h"
#include "library/type_context.h"
#include "library/app_builder.h"
#include "library/class.h"
#include "library/protected.h"

namespace lean {
struct exprs_attribute_data : public attr_data {
    exprs m_args;
    exprs_attribute_data(list_ref<expr> const & args) : m_args(args) {}
    exprs_attribute_data() {}

    virtual unsigned hash() const override {
        unsigned h = 0;
        for (auto const & arg : m_args) {
            h = ::lean::hash(h, ::lean::hash(arg));
        }
        return h;
    }
    void write(serializer & s) const {
        s << m_args;
    }
    void read(deserializer & d) {
        m_args = read_exprs(d);
    }
    void parse(abstract_parser & p) override {
        while (!p.curr_is_token("]")) {
            m_args = cons(p.parse_expr(10000), m_args);
        }
    }
    virtual void print(std::ostream & out) override {
        out << "<>";
    }
};

typedef typed_attribute<exprs_attribute_data> exprs_attribute;

static exprs_attribute const & get_derive_attribute() {
    return static_cast<exprs_attribute const &>(get_system_attribute("derive"));
}

static environment derive(environment env, name const & n, exprs const & clss) {
    for (auto const & cls : clss) {
        auto const & d = env.get(n);
        if (!is_constant(cls) || !d.is_definition())
            throw exception("don't know how to derive this");
        auto const & cls_d = env.get(const_name(cls));
        type_context_old ctx(env);
        auto ls = param_names_to_levels(d.get_univ_params());
        auto tgt = mk_const(n, ls);
        auto real_tgt = instantiate_univ_params(d.get_value(), d.get_univ_params(), ls);
        auto tgt_ty = instantiate_univ_params(d.get_type(), d.get_univ_params(), ls);
        auto cls_ty = env.get(const_name(cls)).get_type();
        levels new_meta_ls;
        for (unsigned i = 0; i < length(cls_d.get_univ_params()); i++)
            new_meta_ls = cons(ctx.mk_univ_metavar_decl(), new_meta_ls);
        cls_ty = instantiate_univ_params(cls_ty, cls_d.get_univ_params(), new_meta_ls);
        if (!is_pi(cls_ty))
            throw exception("don't know how to derive this");
        auto expected_tgt_ty = cls_ty;
        while (is_pi(expected_tgt_ty) && is_class_out_param(binding_domain(expected_tgt_ty))) {
            expected_tgt_ty = binding_body(expected_tgt_ty);
        }
        expected_tgt_ty = binding_domain(expected_tgt_ty);
        auto tgt_num_args = get_expect_num_args(ctx, tgt_ty);
        auto expected_tgt_num_args = get_expect_num_args(ctx, expected_tgt_ty);
        buffer<expr> n_params;
        // use lower arity for instance like `monad` where the class expects a partially applied argument
        for (unsigned i = 0; i < tgt_num_args - expected_tgt_num_args; i++) {
            auto param = ctx.push_local_from_binding(tgt_ty);
            tgt = mk_app(tgt, param);
            real_tgt = mk_app(real_tgt, param);
            n_params.push_back(param);
            tgt_ty = instantiate(binding_body(tgt_ty), param);
        }
        ctx.unify(tgt_ty, expected_tgt_ty);
        buffer<expr> params;
        while (is_pi(cls_ty) && is_class_out_param(binding_domain(cls_ty))) {
            params.push_back(ctx.mk_metavar_decl(ctx.lctx(), binding_domain(cls_ty)));
            cls_ty = binding_body(cls_ty);
        }
        params.push_back(tgt);
        tgt = mk_app(ctx, const_name(cls), params.size(), &params[0]);
        params.pop_back();
        params.push_back(real_tgt);
        real_tgt = mk_app(ctx, const_name(cls), params.size(), &params[0]);
        auto inst = ctx.mk_class_instance(real_tgt);
        if (!inst)
            throw exception(sstream() << "failed to derive " << tgt);
        tgt = ctx.mk_pi(n_params, tgt);
        auto inst2 = ctx.mk_lambda(n_params, inst.value());
        auto new_n = n + const_name(cls);
        auto def = mk_definition(env, new_n, d.get_univ_params(),
                                 ctx.instantiate_mvars(tgt), inst2, d.is_meta());
        auto cdef = check(env, def);
        env = module::add(env, cdef);
        env = add_instance(env, new_n, LEAN_DEFAULT_PRIORITY, true);
        env = add_protected(env, new_n);
    }
    return env;
}

void initialize_derive_attribute() {
    register_system_attribute(exprs_attribute("derive", "auto-derive type classes",
                                                [](environment const & env, io_state const &, name const & n, unsigned,
                                                   bool persistent) {
                                                    if (!persistent)
                                                        throw exception("invalid [derive] attribute, must be persistent");
                                                    auto const & data = *get_derive_attribute().get(env, n);
                                                    return derive(env, n, data.m_args);
                                                }));
}

void finalize_derive_attribute() {
}
}
