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
using inductive::inductive_decls;

inline inductive_decl * to_inductive_type(lean_inductive_type n) { return reinterpret_cast<inductive_decl *>(n); }
inline inductive_decl const & to_inductive_type_ref(lean_inductive_type n) { return *reinterpret_cast<inductive_decl *>(n); }
inline lean_inductive_type of_inductive_type(inductive_decl * n) { return reinterpret_cast<lean_inductive_type>(n); }

inline list<inductive_decl> * to_list_inductive_type(lean_list_inductive_type n) { return reinterpret_cast<list<inductive_decl> *>(n); }
inline list<inductive_decl> const & to_list_inductive_type_ref(lean_list_inductive_type n) { return *reinterpret_cast<list<inductive_decl> *>(n); }
inline lean_list_inductive_type of_list_inductive_type(list<inductive_decl> * n) { return reinterpret_cast<lean_list_inductive_type>(n); }

inline inductive_decls * to_inductive_decl(lean_inductive_decl n) { return reinterpret_cast<inductive_decls *>(n); }
inline inductive_decls const & to_inductive_decl_ref(lean_inductive_decl n) { return *reinterpret_cast<inductive_decls *>(n); }
inline lean_inductive_decl of_inductive_decl(inductive_decls * n) { return reinterpret_cast<lean_inductive_decl>(n); }
}
