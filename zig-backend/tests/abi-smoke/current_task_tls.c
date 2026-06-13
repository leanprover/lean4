#include <assert.h>

extern int leanrt_test_current_task_tls_smoke(void);

int main(void) {
    assert(leanrt_test_current_task_tls_smoke());
    return 0;
}
