/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "runtime/object.h"

lean::object* lean_expr_local(lean::object*, lean::object*, lean::object*, lean::object*);
extern lean::object* lean_environment_empty;
lean::object* lean_environment_contains(lean::object*, lean::object*);
lean::object* lean_elaborator_elaborate_command(lean::object*, lean::object*, lean::object*);
