/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/local_context.h"

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

// Old API

/** \brief Create a metavariable, and attach choice constraint for generating
    solutions using class-instances.

    \param ctx Local context where placeholder is located
    \param prefix Prefix for metavariables that will be created by this procedure
    \param suffix If provided, then it is added to the main metavariable created by this procedure.
    \param use_local_instances If instances in the local context should be used
                               in the class-instance resolution
    \param is_strict True if constraint should fail if not solution is found,
                     False if empty solution should be returned if there is no solution
    \param type Expected type for the placeholder (if known)
    \param tag  To be associated with new metavariables and expressions (for error localization).
*/
pair<expr, constraint> mk_class_instance_elaborator(
    environment const & env, io_state const & ios, local_context const & ctx,
    name const & prefix, optional<name> const & suffix, bool use_local_instances,
    bool is_strict, optional<expr> const & type, tag g, pos_info_provider const * pip);

optional<expr> mk_class_instance(environment const & env, io_state const & ios, local_context const & ctx, expr const & type, bool use_local_instances);
optional<expr> mk_class_instance(environment const & env, local_context const & ctx, expr const & type);
optional<expr> mk_hset_instance(type_checker & tc, io_state const & ios, list<expr> const & ctx, expr const & type);
optional<expr> mk_subsingleton_instance(type_checker & tc, io_state const & ios, list<expr> const & ctx, expr const & type);

void initialize_class_instance_resolution();
void finalize_class_instance_resolution();
}
