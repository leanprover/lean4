#include <assert.h>

extern _Bool leanrt_test_io_wait_any_returns_first(void);

int main(void) {
    assert(leanrt_test_io_wait_any_returns_first());
    return 0;
}
