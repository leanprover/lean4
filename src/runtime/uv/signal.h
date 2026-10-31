/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"
#include "runtime/uv/util.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

inline lean_external_class * g_uv_signal_external_class = nullptr;
void initialize_libuv_signal();

#ifndef LEAN_EMSCRIPTEN

enum class signal_state { Initial, Running, Finished };

// Structure for managing a single UV signal object, including promise handling, signal number, and
// repeating behavior. The repeating behavior exists to "set" a handler and avoid it not getting signals
// between the creation of oneshot signal handlers. Allocated with `new`; the close callback deletes it.
struct lean_uv_signal_object {
    uv_signal_t     m_uv_signal;                        // LibUV signal handle.
    owned_ref       m_promise;                          // The promise the next signal resolves.
    int             m_signum = 0;                       // Signal number to watch for.
    int             m_lean_signum = 0;                  // `m_signum` in the encoding of `Signal.toInt32`, reported to waiters.
    bool            m_repeating = false;                // Flag indicating if the signal handler is repeating.
    bool            m_received = false;                 // Whether a repeating signal arrived while no promise was pending.
    signal_state    m_state = signal_state::Initial;    // The state of the signal.

    // The loop holds a reference to the signal while it is running with a promise.
    unsigned loop_refs() const {
        return m_state == signal_state::Running && m_promise.get() != nullptr;
    }

    // Every Lean reference the signal holds. The loop's reference to the signal itself is not one.
    std::array<owned_ref *, 1> lean_refs() {
        return {&m_promise};
    }
};

// `m_promise` may be null in any state: `stop` leaves a finished signal without one, and `cancel`
// leaves it running without one. A repeating signal also keeps its last
// promise after resolving it, until `next` replaces it.
//
// The event loop holds a reference to the signal object exactly while it is running with a non-null
// `m_promise`.

// =======================================
// Signal object manipulation functions.
static inline lean_object* lean_uv_signal_new(lean_uv_signal_object * s) { return lean_alloc_external(g_uv_signal_external_class, s); }
static inline lean_uv_signal_object* lean_to_uv_signal(lean_object * o) { return (lean_uv_signal_object*)(lean_get_external_data(o)); }

#endif

// =======================================
// Signal manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_mk(uint32_t signum_obj, uint8_t repeating);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_next(b_obj_arg signal);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_stop(b_obj_arg signal);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_cancel(b_obj_arg obj);

}
