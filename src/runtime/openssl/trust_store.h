/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once

#include <lean/lean.h>
#include "runtime/openssl.h"

#ifndef LEAN_EMSCRIPTEN
#include <openssl/ssl.h>
#include <memory>
#include <string>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

// Makes `ctx` trust the platform's root certificates, setting `*detail` to the cause on failure. Anchors
// in the store stay trusted. On macOS and Windows the platform anchors never enter the store:
// `install_chain_verifier` hands chains the store cannot establish to the system's own verification.
bool use_system_trust_store(SSL_CTX * ctx, std::string * detail);

inline void free_x509_stack(STACK_OF(X509) * sk) { sk_X509_pop_free(sk, X509_free); }
using x509_stack_ptr = std::unique_ptr<STACK_OF(X509), released_by<free_x509_stack>>;

// Pushes `cert` onto `sk`, taking a reference.
bool push_ref(STACK_OF(X509) * sk, X509 * cert);

// Whether `cert` carries the key of a certificate in `distrusted`.
bool has_distrusted_key(STACK_OF(X509) * distrusted, X509 * cert);

// Installs the verify callback of a verifying context once `store`, the store it verifies peers against,
// is complete: it refuses any chain through the key of a certificate that `store` or `distrusted` (the
// distrusting blocks the caller's material held, whichever copy the store kept) rejects for `trust_id`
// (the peer's role). With `platform` (the platform's anchors are trusted) it defers chains the store
// cannot establish to the system on macOS and Windows. Returns false on allocation failure.
bool install_chain_verifier(SSL_CTX * ctx, X509_STORE * store, int trust_id, bool platform,
                            STACK_OF(X509) * distrusted);

#endif

}
