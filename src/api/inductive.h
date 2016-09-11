/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/inductive/inductive.h"
#include "api/expr.h"
#include "api/lean_decl.h"
#include "api/lean_inductive.h"
namespace lean {
using inductive::intro_rule;
using inductive::inductive_decl;

inline inductive_decl * to_inductive_decl(lean_inductive_decl n) { return reinterpret_cast<inductive_decl *>(n); }
inline inductive_decl const & to_inductive_decl_ref(lean_inductive_decl n) { return *reinterpret_cast<inductive_decl *>(n); }
inline lean_inductive_decl of_inductive_decl(inductive_decl * n) { return reinterpret_cast<lean_inductive_decl>(n); }
}
