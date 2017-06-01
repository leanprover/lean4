/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <vector>
#include "util/lean_path.h"
#include "library/module.h"
#include "library/util.h"
#include "api/decl.h"
#include "api/string.h"
#include "api/exception.h"
#include "api/ios.h"
#include "api/lean_env.h"
#include "api/lean_module.h"
using namespace lean; // NOLINT
lean_bool lean_env_import(lean_env env, lean_ios ios, lean_list_name modules, lean_env * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(ios);
    check_nonnull(modules);
    auto new_env = to_env_ref(env);
    std::vector<module_name> imports;
    for (name const & n : to_list_name_ref(modules)) {
        module_name m(n);
        imports.push_back(m);
    }
    new_env = import_modules(new_env, "", imports, mk_olean_loader(standard_search_path().get_path()));
    *r = of_env(new environment(new_env));
    LEAN_CATCH;
}

lean_bool lean_env_export(lean_env env, char const * fname, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    auto lm = export_module(to_env_ref(env), fname);
    std::ofstream out(fname, std::ofstream::binary);
    write_module(lm, out);
    LEAN_CATCH;
}
