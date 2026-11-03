/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg);
extern "C" LEAN_EXPORT lean_obj_res lean_openssl_linked_version(lean_obj_arg);
extern "C" LEAN_EXPORT lean_obj_res lean_sha256(b_lean_obj_arg);
extern "C" LEAN_EXPORT lean_obj_res lean_sha256_string(b_lean_obj_arg);
extern "C" LEAN_EXPORT lean_obj_res lean_sha256_mix(b_lean_obj_arg, b_lean_obj_arg);
