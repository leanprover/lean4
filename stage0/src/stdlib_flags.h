#include "util/options.h"

namespace lean {
options get_default_options() {
    options opts;
    // see https://lean-lang.org/lean4/doc/dev/bootstrap.html#further-bootstrapping-complications
#if LEAN_IS_STAGE0 == 1
    // set to true to generally avoid bootstrapping issues limited to proofs
    opts = opts.update({"debug", "proofAsSorry"}, false);
    // switch to `true` for ABI-breaking changes affecting meta code;
    // see also next option!
    opts = opts.update({"interpreter", "prefer_native"}, false);
    // switch to `false` when enabling `prefer_native` should also affect use
    // of built-in parsers in quotations; this is usually the case, but setting
    // both to `true` may be necessary for handling non-builtin parsers with
    // builtin elaborators
    opts = opts.update({"internal", "parseQuotWithCurrentStage"}, true);
    // changes to builtin parsers may also require toggling the following option if macros/syntax
    // with custom precheck hooks were affected
    opts = opts.update({"quotPrecheck"}, true);

    opts = opts.update({"pp", "rawOnError"}, true);
#endif
    return opts;
}
}
