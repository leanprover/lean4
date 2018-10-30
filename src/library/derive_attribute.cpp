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
#include "library/util.h"
#include "library/attribute_manager.h"
#include "library/type_context.h"
#include "library/app_builder.h"
#include "library/class.h"
#include "library/module.h"
#include "library/protected.h"
#include "library/sorry.h"
#include "library/compiler/compiler.h"

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
            expr e = p.parse_expr(10000);
            if (has_sorry(e))
                break;
            m_args = cons(e, m_args);
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

static environment derive(environment env, options const & opts, name const & n, exprs const & clss) {
    for (auto cls : clss) {
        cls = unwrap_pos(cls);
        auto const & d = env.get(n);
        if (!is_constant(cls) || !d.is_definition())
            throw exception("don't know how to derive this");
        auto const & cls_d = env.get(const_name(cls));
        type_context_old ctx(env, opts);
        auto ls = lparams_to_levels(d.get_lparams());
        auto tgt = mk_const(n, ls);
        auto real_tgt = instantiate_lparams(d.get_value(), d.get_lparams(), ls);
        auto tgt_ty = instantiate_lparams(d.get_type(), d.get_lparams(), ls);
        auto cls_ty = env.get(const_name(cls)).get_type();
        levels new_meta_ls;
        for (unsigned i = 0; i < length(cls_d.get_lparams()); i++)
            new_meta_ls = cons(ctx.mk_univ_metavar_decl(), new_meta_ls);
        cls_ty = instantiate_lparams(cls_ty, cls_d.get_lparams(), new_meta_ls);
        if (!is_pi(cls_ty))
            throw exception("don't know how to derive this");
        auto expected_tgt_ty = cls_ty;
        while (is_pi(expected_tgt_ty) &&
                (is_class_out_param(binding_domain(expected_tgt_ty)) || is_implicit(binding_info(expected_tgt_ty)))) {
            expected_tgt_ty = instantiate(binding_body(expected_tgt_ty), ctx.push_local_from_binding(expected_tgt_ty));
        }
        expected_tgt_ty = binding_domain(expected_tgt_ty);
        auto tgt_num_args = get_expect_num_args(ctx, tgt_ty);
        auto expected_tgt_num_args = get_expect_num_args(ctx, expected_tgt_ty);
        buffer<expr> params;
        // use lower arity for instance like `monad` where the class expects a partially applied argument
        for (unsigned i = 0; i < tgt_num_args - expected_tgt_num_args && is_binding(tgt_ty); i++) {
            auto param = ctx.push_local_from_binding(tgt_ty);
            tgt = mk_app(tgt, param);
            real_tgt = beta_reduce(mk_app(real_tgt, param));
            params.push_back(param);
            tgt_ty = instantiate(binding_body(tgt_ty), param);
        }
        ctx.unify(tgt_ty, expected_tgt_ty);
        buffer<expr> cls_args, more_cls_args;
        while (is_pi(cls_ty)) {
            if (is_class_out_param(binding_domain(cls_ty))) {
                cls_args.push_back(ctx.mk_metavar_decl(ctx.lctx(), binding_domain(cls_ty)));
                cls_ty = binding_body(cls_ty);
            } else if (is_implicit(binding_info(cls_ty))) {
                auto param = ctx.push_local_from_binding(cls_ty);
                if (has_fvar(binding_body(cls_ty)))
                    params.push_back(param);
                cls_ty = instantiate(binding_body(cls_ty), param);
            } else {
                break;
            }
        }
        if (is_pi(cls_ty))
            cls_ty = binding_body(cls_ty);
        while (is_pi(cls_ty) && is_class_out_param(binding_domain(cls_ty))) {
            more_cls_args.push_back(ctx.mk_metavar_decl(ctx.lctx(), binding_domain(cls_ty)));
            cls_ty = binding_body(cls_ty);
        }
        auto apply_target = [&](expr const & tgt) {
            buffer<expr> b;
            b.append(cls_args);
            b.push_back(tgt);
            b.append(more_cls_args);
            return mk_app(ctx, const_name(cls), b.size(), &b[0]);
        };
        tgt = apply_target(tgt);
        real_tgt = apply_target(real_tgt);
        auto inst = ctx.mk_class_instance(real_tgt);
        if (!inst)
            throw exception(sstream() << "failed to derive " << real_tgt);
        tgt = ctx.mk_pi(params, tgt);
        auto inst2 = ctx.mk_lambda(params, inst.value());
        auto new_n = n + const_name(cls);
        env = module::add(env, mk_definition(env, new_n, d.get_lparams(),
                                             ctx.instantiate_mvars(tgt), inst2, d.is_meta()));
        env = add_instance(env, new_n, LEAN_DEFAULT_PRIORITY, true);
        env = add_protected(env, new_n);
        env = compile(env, opts, new_n);
    }
    return env;
}

void initialize_derive_attribute() {
    register_system_attribute(exprs_attribute("derive", "auto-derive type classes",
                                                [](environment const & env, io_state const & ios, name const & n, unsigned,
                                                   bool persistent) {
                                                    if (!persistent)
                                                        throw exception("invalid [derive] attribute, must be persistent");
                                                    auto const & data = *get_derive_attribute().get(env, n);
                                                    return derive(env, ios.get_options(), n, data.m_args);
                                                }));
}

void finalize_derive_attribute() {
}
}
