#include <assert.h>

#include <lean/lean.h>

extern _Bool leanrt_test_promise_drop_resolves_none(void);

int main(void) {
    assert(leanrt_test_promise_drop_resolves_none());
    return 0;
}
