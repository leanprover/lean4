/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/sstream.h"
#include "library/module.h"
#include "library/compiler/util.h"
#include "library/compiler/init_attribute.h"

namespace lean {
struct llnf_code_ext : public environment_extension {
    comp_decls m_code;
};

struct llnf_code_ext_reg {
    unsigned m_ext_id;
    llnf_code_ext_reg() { m_ext_id = environment::register_extension(new llnf_code_ext()); }
};

static llnf_code_ext_reg * g_ext = nullptr;
static llnf_code_ext const & get_extension(environment const & env) {
    return static_cast<llnf_code_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, llnf_code_ext const & ext) {
    return env.update(g_ext->m_ext_id, new llnf_code_ext(ext));
}

environment save_llnf_code(environment const & env, comp_decls const & ds) {
    llnf_code_ext ext = get_extension(env);
    /* Check whether constants with `[init]` attribute have arity 0.
       We cannot perform this check at registration time because attributes are set before
       code generation. */
    for (comp_decl const & d : ds) {
        if (has_init_attribute(env, d.fst()) && get_num_nested_lambdas(d.snd()) != 0) {
            throw exception(sstream() << "invalid [init] attribute, '" << d.fst() << "' must not be a function");
        }
    }
    ext.m_code = append(ext.m_code, ds);
    return update(env, ext);
}

comp_decls get_llnf_code(environment const & env) {
    return get_extension(env).m_code;
}

void initialize_llnf_code() {
    g_ext = new llnf_code_ext_reg();
}

void finalize_llnf_code() {
    delete g_ext;
}
}
