#include "util/options.h"

namespace lean {
options get_default_options() {
    options opts;
    // see https://lean-lang.org/lean4/doc/dev/bootstrap.html#further-bootstrapping-complications
#if LEAN_IS_STAGE0 == 1
    // switch to `true` for ABI-breaking changes affecting meta code
    opts = opts.update({"interpreter", "prefer_native"}, false);
    // switch to `true` for changing built-in parsers used in quotations
    opts = opts.update({"internal", "parseQuotWithCurrentStage"}, false);
    // toggling `parseQuotWithCurrentStage` may also require toggling the following option if macros/syntax
    // with custom precheck hooks were affected
    opts = opts.update({"quotPrecheck"}, true);

    opts = opts.update({"pp", "rawOnError"}, true);
#endif
    return opts;
}
}
