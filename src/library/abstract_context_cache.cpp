/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "library/abstract_context_cache.h"
#include "library/type_context.h"
#include "library/class.h"
#include "library/reducible.h"
#include "library/aux_recursors.h"

#ifndef LEAN_DEFAULT_UNFOLD_LEMMAS
#define LEAN_DEFAULT_UNFOLD_LEMMAS false
#endif

#ifndef LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD
#define LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD 1024
#endif

#ifndef LEAN_DEFAULT_SMART_UNFOLDING
#define LEAN_DEFAULT_SMART_UNFOLDING true
#endif

#ifndef LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH
#define LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH 32
#endif

namespace lean {
static name * g_class_instance_max_depth = nullptr;
static name * g_nat_offset_threshold     = nullptr;
static name * g_unfold_lemmas            = nullptr;
static name * g_smart_unfolding          = nullptr;

unsigned get_class_instance_max_depth(options const & o) {
    return o.get_unsigned(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH);
}

unsigned get_nat_offset_cnstr_threshold(options const & o) {
    return o.get_unsigned(*g_nat_offset_threshold, LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD);
}

bool get_unfold_lemmas(options const & o) {
    return o.get_bool(*g_unfold_lemmas, LEAN_DEFAULT_UNFOLD_LEMMAS);
}

bool get_smart_unfolding(options const & o) {
    return o.get_bool(*g_smart_unfolding, LEAN_DEFAULT_SMART_UNFOLDING);
}

context_cacheless::context_cacheless():
    m_unfold_lemmas(LEAN_DEFAULT_UNFOLD_LEMMAS),
    m_nat_offset_cnstr_threshold(LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD),
    m_smart_unfolding(LEAN_DEFAULT_SMART_UNFOLDING),
    m_class_instance_max_depth(LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH) {
}

context_cacheless::context_cacheless(options const & o):
    m_options(o),
    m_unfold_lemmas(::lean::get_unfold_lemmas(o)),
    m_nat_offset_cnstr_threshold(::lean::get_nat_offset_cnstr_threshold(o)),
    m_smart_unfolding(::lean::get_smart_unfolding(o)),
    m_class_instance_max_depth(::lean::get_class_instance_max_depth(o)) {
}

context_cacheless::context_cacheless(abstract_context_cache const & c, bool):
    m_options(c.get_options()),
    m_unfold_lemmas(c.get_unfold_lemmas()),
    m_nat_offset_cnstr_threshold(c.get_nat_offset_cnstr_threshold()),
    m_smart_unfolding(c.get_smart_unfolding()),
    m_class_instance_max_depth(c.get_class_instance_max_depth()) {
}

bool context_cacheless::is_transparent(type_context_old & ctx, transparency_mode m, declaration const & d) {
    if (m == transparency_mode::None)
        return false;
    name const & n = d.get_name();
    if (get_proj_info(ctx, n) != nullptr)
        return false;
    if (m == transparency_mode::All)
        return true;
    if (d.is_theorem() && !get_unfold_lemmas())
        return false;
    if (m == transparency_mode::Instances && is_instance(ctx.env(), d.get_name()))
        return true;
    auto s = get_reducible_status(ctx.env(), d.get_name());
    if (s == reducible_status::Reducible && (m == transparency_mode::Reducible || m == transparency_mode::Instances))
        return true;
    if (s != reducible_status::Irreducible && m == transparency_mode::Semireducible)
        return true;
    return false;
}

optional<declaration> context_cacheless::get_decl(type_context_old & ctx, transparency_mode m, name const & n) {
    if (auto d = ctx.env().find(n)) {
        if (d->is_definition() && is_transparent(ctx, m, *d)) {
            return d;
        }
    }
    return optional<declaration>();
}

projection_info const * context_cacheless::get_proj_info(type_context_old & ctx, name const & n) {
    return get_projection_info(ctx.env(), n);
}

bool context_cacheless::get_aux_recursor(type_context_old & ctx, name const & n) {
    return ::lean::is_aux_recursor(ctx.env(), n);
}

void context_cacheless::get_unification_hints(type_context_old & ctx, name const & f1, name const & f2, buffer<unification_hint> & hints) {
    return ::lean::get_unification_hints(ctx.env(), f1, f2, hints);
}

void initialize_abstract_context_cache() {
    g_class_instance_max_depth     = new name{"class", "instance_max_depth"};
    register_unsigned_option(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH,
                             "(class) max allowed depth in class-instance resolution");
    g_nat_offset_threshold         = new name{"unifier", "nat_offset_cnstr_threshold"};
    register_unsigned_option(*g_nat_offset_threshold, LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD,
                             "(unifier) the unifier has special support for offset nat constraints of the form: "
                             "(t + k_1 =?= s + k_2), (t + k_1 =?= k_2) and (k_1 =?= k_2), "
                             "where k_1 and k_2 are numerals, t and s are arbitrary terms, and they all have type nat, "
                             "the offset constraint solver is used if k_1 and k_2 are smaller than the given threshold");
    g_unfold_lemmas = new name{"type_context", "unfold_lemmas"};
    register_bool_option(*g_unfold_lemmas, LEAN_DEFAULT_UNFOLD_LEMMAS,
                         "(type-context) whether to unfold lemmas (e.g., during elaboration)");
    g_smart_unfolding = new name{"type_context", "smart_unfolding"};
    register_bool_option(*g_smart_unfolding, LEAN_DEFAULT_SMART_UNFOLDING,
                         "(type-context) enable/disable smart unfolding (e.g., during elaboration)");
}

void finalize_abstract_context_cache() {
    delete g_class_instance_max_depth;
    delete g_nat_offset_threshold;
    delete g_smart_unfolding;
    delete g_unfold_lemmas;
}
}
