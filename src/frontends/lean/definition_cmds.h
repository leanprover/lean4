/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parser.h"
namespace lean {
environment mutual_definition_cmd_core(parser & p, bool is_private, bool is_protected, bool is_noncomputable);
inline environment mutual_definition_cmd(parser & p) { return mutual_definition_cmd_core(p, false, false, false); }
inline environment private_mutual_definition_cmd(parser & p) { return mutual_definition_cmd_core(p, true, false, false); }
inline environment protected_mutual_definition_cmd(parser & p) { return mutual_definition_cmd_core(p, false, true, false); }
inline environment noncomputable_mutual_definition_cmd(parser & p) { return mutual_definition_cmd_core(p, false, false, true); }
inline environment private_noncomputable_mutual_definition_cmd(parser & p) { return mutual_definition_cmd_core(p, true, false, true); }
inline environment protected_noncomputable_mutual_definition_cmd(parser & p) { return mutual_definition_cmd_core(p, false, true, true); }

enum def_cmd_kind { Theorem, Definition, MetaDefinition, Example, Abbreviation, LocalAbbreviation };
environment xdefinition_cmd_core(parser & p, def_cmd_kind k, bool is_private, bool is_protected, bool is_noncomputable);
}
