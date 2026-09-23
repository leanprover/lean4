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

// Makes `ctx` trust the platform's root certificates, setting `*detail` to a failure's cause when the
// OpenSSL error queue does not carry it. Anchors in the store stay trusted. On macOS the platform
// anchors never enter the store; a verify callback hands chains the store cannot establish to the
// system's trust evaluation.
bool use_system_trust_store(SSL_CTX * ctx, std::string * detail);

#endif

}
