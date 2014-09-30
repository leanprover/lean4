/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/hash.h"
#include "util/int64.h"
#include "kernel/environment.h"

namespace lean {
struct fingerprint_ext : public environment_extension {
    uint64 m_fingerprint;
    fingerprint_ext():m_fingerprint(0) {}
};

struct fingerprint_ext_reg {
    unsigned m_ext_id;
    fingerprint_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<fingerprint_ext>()); }
};

static fingerprint_ext_reg * g_ext = nullptr;
static fingerprint_ext const & get_extension(environment const & env) {
    return static_cast<fingerprint_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, fingerprint_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<fingerprint_ext>(ext));
}

environment update_fingerprint(environment const & env, unsigned h) {
    fingerprint_ext ext = get_extension(env);
    ext.m_fingerprint = hash(ext.m_fingerprint, static_cast<uint64>(h));
    return update(env, ext);
}

uint64 get_fingerprint(environment const & env) {
    return get_extension(env).m_fingerprint;
}

void initialize_fingerprint() {
    g_ext     = new fingerprint_ext_reg();
}

void finalize_fingerprint() {
    delete g_ext;
}
}
