#include <assert.h>

#include <lean/lean.h>

extern _Bool leanrt_test_promise_rc_balanced(void);

int main(void) {
    assert(leanrt_test_promise_rc_balanced());
    return 0;
}
