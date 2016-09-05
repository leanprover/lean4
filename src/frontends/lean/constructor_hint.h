/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
bool has_constructor_hint(environment const & env, name const & d);

void initialize_constructor_hint();
void finalize_constructor_hint();
}
