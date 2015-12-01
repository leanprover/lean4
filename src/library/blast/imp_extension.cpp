/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/imp_extension.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {

imp_extension::imp_extension(unsigned state_id): m_state_id(state_id), m_parent(nullptr) {}
imp_extension::imp_extension(imp_extension * parent):
    m_state_id(parent->m_state_id), m_parent(parent) {
    parent->inc_ref();
}

imp_extension::~imp_extension() { if (m_parent) m_parent->dec_ref(); }

imp_extension * imp_extension::clone() {
    return new imp_extension(this);
}

void imp_extension::hypothesis_activated(hypothesis const & h, hypothesis_idx hidx) {
    imp_extension_state & state = get_imp_extension_state(m_state_id);
    if (is_nil(m_asserts)) state.push();
    m_asserts = cons(h, m_asserts);
    state.assert(h);
}

void imp_extension_state::replay_actions(imp_extension * imp_ext) {
    list<hypothesis> const & asserts = reverse(imp_ext->get_asserts());
    if (is_nil(asserts)) return;
    push();
    for_each(asserts, [&](hypothesis const & h) { assert(h); });
}

void imp_extension_state::undo_actions(imp_extension * imp_ext) {
    list<hypothesis> const & asserts = imp_ext->get_asserts();
    if (is_nil(asserts)) return;
    pop();
}

}}
