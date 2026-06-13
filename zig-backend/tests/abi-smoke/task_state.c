#include <assert.h>

extern _Bool leanrt_test_io_task_state_progression(void);

int main(void) {
    assert(leanrt_test_io_task_state_progression());
    return 0;
}
