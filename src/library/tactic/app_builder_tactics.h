/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/app_builder.h"

namespace lean {
app_builder_cache & get_app_builder_cache_for(environment const & env);

inline app_builder mk_app_builder_for(type_context & ctx) {
    return app_builder(ctx, get_app_builder_cache_for(ctx.env()));
}

void initialize_app_builder_tactics();
void finalize_app_builder_tactics();
}
