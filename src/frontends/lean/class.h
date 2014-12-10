/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name.h"
#include "util/list.h"
#include "kernel/environment.h"
#include "frontends/lean/cmd_table.h"

namespace lean {
/** \brief Parse priority for an class instance */
optional<unsigned> parse_instance_priority(parser & p);
void register_class_cmds(cmd_table & r);
}
