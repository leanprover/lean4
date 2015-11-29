/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/blast.h"
#include "library/blast/forward/forward_extension.h"
#include "library/blast/hypothesis.h"
#include "library/blast/util.h"

namespace lean {
namespace blast {

static unsigned g_ext_id = 0;
static optional<head_index> to_head_index(expr type) {
    // TODO(dhs): we will want to filter this set,
    // because some constants are treated specially by this module
    // (e.g. [eq] and [not])
    expr const & f = get_app_fn(type);
    if (is_constant(f) || is_local(f))
        return optional<head_index>(head_index(f));
    else
        return optional<head_index>();
}

void forward_branch_extension::initialized() { }

void forward_branch_extension::hypothesis_activated(hypothesis const & h, hypothesis_idx ) {
    index_expr(h.get_type());
}

void forward_branch_extension::hypothesis_deleted(hypothesis const & , hypothesis_idx ) {
    // TODO(dhs): remove from indices
}

void forward_branch_extension::index_expr(expr const & e) {
    // TODO(dhs): index the target when it gets updated

    if (auto head_idx = to_head_index(e)) {
        m_index.insert(head_index(e), e);
    }
    switch (e.kind()) {
    case expr_kind::Var:
        lean_unreachable();  // LCOV_EXCL_LINE
    case expr_kind::Local:
    case expr_kind::Meta:
    case expr_kind::Sort:
    case expr_kind::Constant:
    case expr_kind::Macro: // TODO(dhs): do I unfold macros?
        break;
    case expr_kind::Lambda:
    case expr_kind::Pi:
        // TODO(dhs): confirm that I only index quantified-free hypotheses
        break;
    case expr_kind::App:
        index_expr(app_fn(e));
        index_expr(app_arg(e));
        break;
    }
}

void initialize_forward_extension() {
    g_ext_id = register_branch_extension(new forward_branch_extension());
}

void finalize_forward_extension() { }

forward_branch_extension & get_forward_extension() {
    return static_cast<forward_branch_extension&>(curr_state().get_extension(g_ext_id));
}
}}
