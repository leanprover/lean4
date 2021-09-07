/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "runtime/thread.h"
#include "runtime/optional.h"

namespace lean {

#if defined(LEAN_MULTI_THREAD)
class single_timer {
public:
    using callback = std::function<void()>;

private:
    mutex m_mutex;
    condition_variable m_timer_changed;
    bool m_shutting_down;

    optional<chrono::steady_clock::time_point> m_time;
    callback m_cb;

    lthread m_thread;

    void worker();

public:
    single_timer();
    ~single_timer();

    void set(chrono::steady_clock::time_point const &, callback const & cb, bool overwrite = true);
    void reset();
};
#else
class single_timer {};
#endif

}
