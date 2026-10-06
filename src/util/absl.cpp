/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Henrik Böving

The non-header parts of abseil needed by `absl::flat_hash_map` (see `util/flat_hash_map.h`).
*/
#include <absl/container/internal/raw_hash_set.cc>
#include <absl/base/internal/raw_logging.cc>
#include <absl/hash/internal/hash.cc>
#include <absl/hash/internal/city.cc>

namespace absl {
ABSL_NAMESPACE_BEGIN
namespace container_internal {
HashtablezInfoHandle ForcedTrySample(size_t, size_t, size_t, uint16_t) {
    return HashtablezInfoHandle{nullptr};
}
}
ABSL_NAMESPACE_END
}
