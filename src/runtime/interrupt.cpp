/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <cstdlib>
#include <ctime>
#include <execinfo.h>
#include "runtime/thread.h"
#include "runtime/interrupt.h"
#include "runtime/exception.h"
#include "runtime/memory.h"
#include "runtime/object.h"
#include "lean/lean.h"
#include "util/io.h"

namespace lean {
LEAN_THREAD_VALUE(size_t, g_max_heartbeat, 0);
LEAN_THREAD_VALUE(size_t, g_heartbeat, 0);

// --- check_system interval monitoring ---
//
// When LEAN_CHECK_SYSTEM_INTERVAL_MS=N is set, warn on stderr if check_system
// is not called within N milliseconds of CPU time on the current thread.
// Uses CLOCK_THREAD_CPUTIME_ID so that IO waits do not count towards the interval.
// Zero overhead when env var is unset.

// 0 = disabled
static unsigned g_check_system_interval_ms = 0;
static bool g_check_system_interval_initialized = false;

static unsigned get_check_system_interval_ms() {
    if (!g_check_system_interval_initialized) {
        g_check_system_interval_initialized = true;
        if (const char * env = std::getenv("LEAN_CHECK_SYSTEM_INTERVAL_MS")) {
            g_check_system_interval_ms = std::atoi(env);
        }
    }
    return g_check_system_interval_ms;
}

static uint64_t thread_cpu_time_ns() {
    struct timespec ts;
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts);
    return static_cast<uint64_t>(ts.tv_sec) * 1000000000ULL + static_cast<uint64_t>(ts.tv_nsec);
}

// Thread-local: last CPU time when check_system was called on this thread.
LEAN_THREAD_VALUE(uint64_t, g_last_check_system_ns, 0);

static void check_system_interval(char const * component_name) {
    unsigned interval_ms = get_check_system_interval_ms();
    if (interval_ms > 0) {
        uint64_t now_ns = thread_cpu_time_ns();
        uint64_t last_ns = g_last_check_system_ns;
        g_last_check_system_ns = now_ns;
        if (last_ns != 0) {
            uint64_t elapsed_ms = (now_ns - last_ns) / 1000000;
            if (elapsed_ms > interval_ms) {
                fprintf(stderr,
                    "[check_system] WARNING: %llu ms CPU time since last check_system call "
                    "(component: %s)\n",
                    (unsigned long long)elapsed_ms, component_name);
                void * bt_buf[64];
                int nptrs = backtrace(bt_buf, 64);
                backtrace_symbols_fd(bt_buf, nptrs, 2); // fd 2 = stderr
                // Reset timer after printing to avoid backtrace overhead cascading
                g_last_check_system_ns = thread_cpu_time_ns();
            }
        }
    }
}

extern "C" LEAN_EXPORT obj_res lean_check_system_interval(b_lean_obj_arg component_name) {
    check_system_interval(lean_string_cstr(component_name));
    return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT uint8_t lean_check_system_interval_is_enabled(lean_obj_arg /* unit */) {
    return get_check_system_interval_ms() > 0;
}

extern "C" LEAN_EXPORT obj_res lean_internal_get_default_max_heartbeat() {
#ifdef LEAN_DEFAULT_MAX_HEARTBEAT
    return lean_box(LEAN_DEFAULT_MAX_HEARTBEAT);
#else
    return lean_box(0);
#endif
}

void inc_heartbeat() { g_heartbeat++; }

void reset_heartbeat() { g_heartbeat = 0; }

void set_max_heartbeat(size_t max) { g_max_heartbeat = max; }

extern "C" LEAN_EXPORT obj_res lean_internal_set_max_heartbeat(usize max) {
    set_max_heartbeat(max);
    return lean_box(0);
}

size_t get_max_heartbeat() { return g_max_heartbeat; }

void set_max_heartbeat_thousands(unsigned max) { g_max_heartbeat = static_cast<size_t>(max) * 1000; }

scope_heartbeat::scope_heartbeat(size_t max):flet<size_t>(g_heartbeat, max) {}
LEAN_EXPORT scope_max_heartbeat::scope_max_heartbeat(size_t max):flet<size_t>(g_max_heartbeat, max) {}

// separate definition to allow breakpoint in debugger
void throw_heartbeat_exception() {
    throw heartbeat_exception();
}

void check_heartbeat() {
    inc_heartbeat();
    if (g_max_heartbeat > 0 && g_heartbeat > g_max_heartbeat)
        throw_heartbeat_exception();
}

LEAN_THREAD_VALUE(size_t, g_max_rec_depth, 0);
LEAN_THREAD_VALUE(size_t, g_rec_depth, 0);

/* The kernel re-checks a fully elaborated term from scratch, without the caching, metavariable
   assignments, and reducibility shortcuts the elaborator uses while building it incrementally. As a
   result the kernel recurses substantially deeper than the elaborator did for the same term (stdlib
   `grind`/`simp` proofs check several thousand levels deep). We therefore let the kernel reach a
   generous multiple of the configured `maxRecDepth` before bailing out, so that code which fits
   within `maxRecDepth` during elaboration is not rejected by the kernel. */
static constexpr size_t g_kernel_rec_depth_factor = 16;

void set_max_rec_depth(size_t max) { g_max_rec_depth = max; }
size_t get_max_rec_depth() { return g_max_rec_depth; }

LEAN_EXPORT scope_max_rec_depth::scope_max_rec_depth(size_t max) :
    m_max(g_max_rec_depth, max), m_curr(g_rec_depth, 0) {}

LEAN_EXPORT scope_rec_depth::scope_rec_depth() {
    g_rec_depth++;
    if (g_max_rec_depth > 0 && g_rec_depth > g_max_rec_depth * g_kernel_rec_depth_factor) {
        g_rec_depth--;
        throw stack_space_exception("type checker");
    }
}

LEAN_EXPORT scope_rec_depth::~scope_rec_depth() { g_rec_depth--; }

LEAN_THREAD_VALUE(lean_object *, g_cancel_tk, nullptr);

LEAN_EXPORT scope_cancel_tk::scope_cancel_tk(lean_object * o):flet<lean_object *>(g_cancel_tk, o) {}

// `IO.CancelToken` is `structure { promise : IO.Promise Unit; setRef : IO.Ref Bool }`. We read
// the `Bool` flag (field 1) directly: cheaper than walking the promise's task state, and this
// is on the hot `Core.checkInterrupted` path. Must stay in sync with the field order in
// `Init/System/CancelToken.lean`.
static bool cancel_tk_is_set(lean_object * tk) {
    lean_object * setRef = lean_ctor_get(tk, 1);
    return lean_unbox(lean_to_ref(setRef)->m_value) != 0;
}

void check_interrupted() {
    if (g_cancel_tk) {
        // `g_cancel_tk` is owned by the enclosing `scope_cancel_tk`, so it stays alive for the
        // duration of this call without an explicit `inc_ref`.
        if (cancel_tk_is_set(g_cancel_tk) &&
            !std::uncaught_exceptions()) {
            throw interrupted();
        }
    }
}

void check_system(char const * component_name, bool do_check_interrupted) {
    check_system_interval(component_name);
    check_stack(component_name);
    check_memory(component_name);
    if (do_check_interrupted) {
        check_interrupted();
        check_heartbeat();
    }
}

void sleep_for(unsigned ms, unsigned step_ms) {
    if (step_ms == 0)
        step_ms = 1;
    unsigned rounds = ms / step_ms;
    chrono::milliseconds c(step_ms);
    chrono::milliseconds r(ms % step_ms);
    for (unsigned i = 0; i < rounds; i++) {
        this_thread::sleep_for(c);
        check_interrupted();
    }
    this_thread::sleep_for(r);
    check_interrupted();
}
}
