/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"
#include "runtime/uv/util.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

inline lean_external_class * g_uv_timer_external_class = nullptr;
void initialize_libuv_timer();

#ifndef LEAN_EMSCRIPTEN
using namespace std;

enum class timer_state { Initial, Running, Finished };

// A UV timer, including promise handling, timeout, and repeating behavior. Allocated with `new`; the
// close callback deletes it.
struct lean_uv_timer_object {
    uv_timer_t      m_uv_timer;                         // LibUV timer handle.
    owned_ref       m_promise;                          // The promise the next tick resolves.
    uint64_t        m_timeout = 0;                      // Timeout duration in milliseconds.
    bool            m_repeating = false;                // Flag indicating if the timer is repeating.
    timer_state     m_state = timer_state::Initial;     // The state of the timer.

    // The loop holds a reference to the timer while it is running with a promise.
    unsigned loop_refs() const {
        return m_state == timer_state::Running && m_promise.get() != nullptr;
    }

    // Every Lean reference the timer holds. The loop's reference to the timer itself is not one.
    std::array<owned_ref *, 1> lean_refs() {
        return {&m_promise};
    }
};

// `m_promise` may be null in any state: `stop` leaves a finished timer without one, and a tick or
// `cancel` leaves a repeating timer running without one.
//
// The event loop holds a reference to the timer object exactly while it is running with a non-null
// `m_promise`.

// =======================================
// Timer object manipulation functions.
static inline lean_object* lean_uv_timer_new(lean_uv_timer_object * s) { return lean_alloc_external(g_uv_timer_external_class, s); }
static inline lean_uv_timer_object* lean_to_uv_timer(lean_object * o) { return (lean_uv_timer_object*)(lean_get_external_data(o)); }

#else

// =======================================
// Timer manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, uint8_t repeating);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_reset(b_obj_arg timer);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg timer);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_cancel(b_obj_arg timer);

#endif

}
