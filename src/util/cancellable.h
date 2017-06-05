/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once

#include <vector>
#include "util/thread.h"
#include "util/flet.h"
#include "util/interrupt.h"

namespace lean {

struct cancellable {
    virtual ~cancellable() {}
    virtual void cancel(std::shared_ptr<cancellable> const & self) = 0;
};

class cancellation_token_cell;
using cancellation_token = std::shared_ptr<cancellation_token_cell>;

class cancellation_token_cell : public cancellable {
    mutex m_mutex;
    atomic_bool m_cancelled;
    std::vector<std::weak_ptr<cancellable>> m_children;
    unsigned m_expired_children = 0;
    cancellation_token m_parent;

    friend cancellation_token mk_cancellation_token(cancellation_token const &);

public:
    cancellation_token_cell(cancellation_token const & parent);
    ~cancellation_token_cell();

    void add_child(std::weak_ptr<cancellable> const &);
    void gc();

    void cancel(std::shared_ptr<cancellable> const & self) override;

    cancellation_token const & get_parent() const { return m_parent; }

    bool is_cancelled() const { return m_cancelled.load(); }

    atomic_bool * get_cancellation_flag() { return &m_cancelled; }
};

cancellation_token mk_cancellation_token(cancellation_token const & parent);
inline cancellation_token mk_cancellation_token() { return mk_cancellation_token(nullptr); }

inline void cancel(std::shared_ptr<cancellable> const & c) { if (c) c->cancel(c); }
inline void cancelw(std::weak_ptr<cancellable> const & wc) { if (auto c = wc.lock()) cancel(c); }

struct scope_cancellation_token : flet<cancellation_token const *>, scoped_interrupt_flag {
    scope_cancellation_token(cancellation_token const *);
    scope_cancellation_token(cancellation_token & t) : scope_cancellation_token(&t) {}
};
cancellation_token global_cancellation_token();

}
