/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once

#include <lean/lean.h>

#ifndef LEAN_EMSCRIPTEN
#include <openssl/ssl.h>
#include <string>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

// Loads the platform's root certificates into `ctx`'s store so clients verify public servers out of
// the box, setting `*detail` to the platform-level cause of a failure the OpenSSL error queue does
// not carry. The anchors are added to whatever the store already holds, never in place of it.
bool load_system_trust_store(SSL_CTX * ctx, std::string * detail);

#endif

}
