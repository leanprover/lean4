/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "util/cancellable.h"
#include <algorithm>

namespace lean {

cancellation_token_cell::cancellation_token_cell(cancellation_token const & parent) :
        m_cancelled(false), m_parent(parent) {}

cancellation_token_cell::~cancellation_token_cell() {
    if (m_parent) m_parent->gc();
}

void cancellation_token_cell::cancel(std::shared_ptr<cancellable> const &) {
    unique_lock<mutex> lock(m_mutex);
    m_cancelled.store(true);
    auto children = m_children;
    lock.unlock();
    for (auto & child : children)
        cancelw(child);
}

void cancellation_token_cell::gc() {
    unique_lock<mutex> lock(m_mutex);
    m_children.erase(std::remove_if(m_children.begin(), m_children.end(),
                                    [] (std::weak_ptr<cancellable> const & c) { return c.expired(); }),
                     m_children.end());
}

void cancellation_token_cell::add_child(std::weak_ptr<cancellable> const & c) {
    unique_lock<mutex> lock(m_mutex);
    m_children.push_back(c);
    if (m_cancelled.load()) {
        lock.unlock();
        cancelw(c);
    }
}
cancellation_token mk_cancellation_token(cancellation_token const & parent) {
    auto ctok = std::make_shared<cancellation_token_cell>(parent);
    if (parent) parent->add_child(ctok);
    return ctok;
}

LEAN_THREAD_PTR(cancellation_token const, g_cancellation_token);

scope_cancellation_token::scope_cancellation_token(cancellation_token const * tok) :
    flet<cancellation_token const *>(g_cancellation_token, tok),
    scoped_interrupt_flag(*tok ? (*tok)->get_cancellation_flag() : nullptr) {
    check_interrupted();
}

cancellation_token global_cancellation_token() {
    return g_cancellation_token ? *g_cancellation_token : nullptr;
}

}
