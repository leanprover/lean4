#include <assert.h>

extern _Bool leanrt_test_io_cancel_chain(void);

int main(void) {
    assert(leanrt_test_io_cancel_chain());
    return 0;
}
