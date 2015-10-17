/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/environment.h"
#include "library/io_state.h"

namespace lean {
class ci_type_inference {
public:
    virtual ~ci_type_inference() {}
    virtual expr whnf(expr const & e) = 0;
    virtual expr infer_type(expr const & e) = 0;
};

class ci_type_inference_factory {
public:
    virtual ~ci_type_inference_factory();
    virtual std::shared_ptr<ci_type_inference> operator()(environment const & env) const;
};

class ci_type_inference_factory_scope {
    ci_type_inference_factory * m_old;
public:
    ci_type_inference_factory_scope(ci_type_inference_factory & factory);
    ~ci_type_inference_factory_scope();
};

optional<expr> mk_class_instance(environment const & env, io_state const & ios, list<expr> const & ctx, expr const & e, pos_info_provider const * pip = nullptr);
optional<expr> mk_class_instance(environment const & env, list<expr> const & ctx, expr const & e, pos_info_provider const * pip = nullptr);
void initialize_class_instance_resolution();
void finalize_class_instance_resolution();
}
