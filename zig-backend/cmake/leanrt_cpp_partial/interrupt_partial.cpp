/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#include <runtime/interrupt.cpp>

extern "C" void leanrt_cpp_partial_hidden_reset_heartbeat() {
    lean::reset_heartbeat();
}

extern "C" lean_object * leanrt_cpp_partial_hidden_cancel_tk_get() {
    return lean::g_cancel_tk;
}

extern "C" lean_object * leanrt_cpp_partial_hidden_cancel_tk_swap(lean_object * token) {
    lean_object * prev = lean::g_cancel_tk;
    lean::g_cancel_tk = token;
    return prev;
}
