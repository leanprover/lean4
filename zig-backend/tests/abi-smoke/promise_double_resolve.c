#include <assert.h>

#include <lean/lean.h>

extern _Bool leanrt_test_promise_double_resolve_idempotent(void);

int main(void) {
    assert(leanrt_test_promise_double_resolve_idempotent());
    return 0;
}
