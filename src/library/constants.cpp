// Copyright (c) 2015 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// DO NOT EDIT, automatically generated file, generator scripts/gen_constants_cpp.py
#include "util/name.h"
namespace lean{
name const * g_bool_false = nullptr;
name const * g_bool_true = nullptr;
name const * g_punit = nullptr;
name const * g_punit_unit = nullptr;
name const * g_uint32 = nullptr;
void initialize_constants() {
    g_bool_false = new name{"Bool", "false"};
    mark_persistent(g_bool_false->raw());
    g_bool_true = new name{"Bool", "true"};
    mark_persistent(g_bool_true->raw());
    g_punit = new name{"PUnit"};
    mark_persistent(g_punit->raw());
    g_punit_unit = new name{"PUnit", "unit"};
    mark_persistent(g_punit_unit->raw());
    g_uint32 = new name{"UInt32"};
    mark_persistent(g_uint32->raw());
}
void finalize_constants() {
    delete g_bool_false;
    delete g_bool_true;
    delete g_punit;
    delete g_punit_unit;
    delete g_uint32;
}
name const & get_bool_false_name() { return *g_bool_false; }
name const & get_bool_true_name() { return *g_bool_true; }
name const & get_punit_name() { return *g_punit; }
name const & get_punit_unit_name() { return *g_punit_unit; }
name const & get_uint32_name() { return *g_uint32; }
}
