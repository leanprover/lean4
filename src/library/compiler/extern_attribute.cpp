/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#include <string>
#include "runtime/sstream.h"
#include "util/object_ref.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/util.h"
#include "library/projection.h"
#include "library/attribute_manager.h"
#include "library/compiler/borrowed_annotation.h"
#include "library/compiler/util.h"
#include "library/compiler/ir.h"
#include "library/compiler/extern_attribute.h"

namespace lean {
object* get_extern_attr_data_core(object* env, object* n);

optional<extern_attr_data_value> get_extern_attr_data(environment const & env, name const & fn) {
    return to_optional<extern_attr_data_value>(get_extern_attr_data_core(env.to_obj_arg(), fn.to_obj_arg()));
}

bool is_extern_constant(environment const & env, name const & c) {
    return static_cast<bool>(get_extern_attr_data(env, c));
}

static optional<unsigned> get_given_arity(environment const & env, name const & c) {
    optional<extern_attr_data_value> v = get_extern_attr_data(env, c);
    lean_assert(v);
    object * arity = cnstr_get(v->raw(), 0);
    if (is_scalar(arity)) return optional<unsigned>(); // none
    // arity is (some v)
    arity = cnstr_get(arity, 0);
    if (is_scalar(arity)) return optional<unsigned>(unbox(arity));
    return optional<unsigned>(); // ignore big nums
}

optional<unsigned> get_extern_constant_arity(environment const & env, name const & c) {
    if (is_extern_constant(env, c)) {
        if (optional<unsigned> given_arity = get_given_arity(env, c)) {
            return given_arity;
        }
        /* Infer arity from type */
        return optional<unsigned>(get_arity(env.get(c).get_type()));
    }
    return optional<unsigned>();
}

bool get_extern_borrowed_info(environment const & env, name const & c, buffer<bool> & borrowed_args, bool & borrowed_res) {
    if (is_extern_constant(env, c)) {
        /* Extract borrowed info from type */
        expr type = env.get(c).get_type();
        unsigned arity = 0;
        while (is_pi(type)) {
            arity++;
            expr d = binding_domain(type);
            borrowed_args.push_back(is_borrowed(d));
            type = binding_body(type);
        }
        borrowed_res = false;
        if (optional<unsigned> given_arity = get_given_arity(env, c)) {
            if (*given_arity < arity) {
                borrowed_args.shrink(*given_arity);
                return true;
            } else if (*given_arity > arity) {
                borrowed_args.resize(*given_arity, false);
                return true;
            }
        }
        borrowed_res = is_borrowed(type);
        return true;
    }
    return false;
}

optional<expr> get_extern_constant_ll_type(environment const & env, name const & c) {
    if (is_extern_constant(env, c)) {
        unsigned arity = 0;
        expr type = env.get(c).get_type();
        type_checker::state st(env);
        local_ctx lctx;
        name_generator ngen;
        buffer<expr> arg_ll_types;
        buffer<expr> locals;
        while (is_pi(type)) {
            arity++;
            expr arg_type = instantiate_rev(binding_domain(type), locals.size(), locals.data());
            expr arg_ll_type = mk_runtime_type(st, lctx, arg_type);
            arg_ll_types.push_back(arg_ll_type);
            expr local = lctx.mk_local_decl(ngen, binding_name(type), arg_type);
            locals.push_back(local);
            type = binding_body(type);
        }
        type = instantiate_rev(type, locals.size(), locals.data());
        expr ll_type;
        if (optional<unsigned> given_arity = get_given_arity(env, c)) {
            if (arity < *given_arity) {
                /* Fill with `_obj` */
                arg_ll_types.resize(*given_arity, mk_enf_object_type());
                ll_type = mk_enf_object_type();
            } else if (arity > *given_arity) {
                arg_ll_types.shrink(*given_arity);
                ll_type = mk_enf_object_type(); /* Result is a closure */
            } else {
                ll_type = mk_runtime_type(st, lctx, type);
            }
        } else {
            ll_type = mk_runtime_type(st, lctx, type);
        }
        unsigned i = arg_ll_types.size();
        while (i > 0) {
            --i;
            ll_type = mk_arrow(arg_ll_types[i], ll_type);
        }
        return some_expr(ll_type);
    }
    return none_expr();
}
}
