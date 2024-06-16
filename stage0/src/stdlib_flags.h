#include "util/options.h"

namespace lean {
options get_default_options() {
    options opts;
    // see https://leanprover.github.io/lean4/doc/make/index.html#further-bootstrapping-complications
#if LEAN_IS_STAGE0 == 1
    // switch to `true` for ABI-breaking changes affecting meta code
    opts = opts.update({"interpreter", "prefer_native"}, false);
    // switch to `true` for changing built-in parsers used in quotations
    opts = opts.update({"internal", "parseQuotWithCurrentStage"}, false);
#endif
    return opts;
}
}
