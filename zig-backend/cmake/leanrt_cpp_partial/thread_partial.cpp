/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#define lean_initialize_thread leanrt_cpp_partial_hidden_lean_initialize_thread
#define lean_finalize_thread leanrt_cpp_partial_hidden_lean_finalize_thread
#define lean_run_main leanrt_cpp_partial_hidden_run_main_impl

#include <runtime/thread.cpp>
