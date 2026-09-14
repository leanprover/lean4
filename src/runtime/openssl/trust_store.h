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

// Makes `ctx` trust the platform's root certificates so clients verify public servers out of the
// box, setting `*detail` to the platform-level cause of a failure the OpenSSL error queue does not
// carry. Anchors already in the store, or added to it later, stay trusted. On macOS the platform
// anchors never enter the store: `ctx` gets a certificate verification callback instead, which
// hands any chain the store cannot establish to the system's own trust evaluation.
bool use_system_trust_store(SSL_CTX * ctx, std::string * detail);

#endif

}
