#include "util/options.h"

// Should we test stage 2 and run update-stage0 on PR merge? YES
// (change to "YES" to trigger)

namespace lean {
options get_option_overrides() {
    options opts;
    // see https://github.com/leanprover/lean4/blob/master/doc/dev/bootstrap.md#further-bootstrapping-complications
#if LEAN_IS_STAGE0 == 1
    // uncomment to generally avoid bootstrapping issues limited to proofs
    //opts = opts.update({"debug", "proofAsSorry"}, true);

    // uncomment to generally avoid bootstrapping issues in `omega` and `grind`
    //opts = opts.update({"debug", "terminalTacticsAsSorry"}, true);

    // uncomment for ABI-breaking changes affecting meta code;
    // see also next option!
    opts = opts.update({"interpreter", "prefer_native"}, true);

    // uncomment when enabling `prefer_native` should also affect use
    // of built-in parsers in quotations; this is usually the case, but setting
    // both to `true` may be necessary for handling non-builtin parsers with
    // builtin elaborators
    // TODO: make consistent across stages
    //opts = opts.update({"internal", "parseQuotWithCurrentStage"}, true);

    // changes to builtin parsers may also require uncommenting the following option if macros/syntax
    // with custom precheck hooks were affected
    opts = opts.update({"quotPrecheck"}, false);
#endif
    return opts;
}
}
