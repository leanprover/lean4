#include <assert.h>
#include <stddef.h>

typedef struct {
    size_t pre_spawn_before_reset;
    size_t pre_spawn;
    size_t post_spawn_before_reset;
    size_t post_spawn;
    size_t post_run_before_reset;
    size_t post_run;
} leanrt_task_heartbeat_snapshot;

extern _Bool leanrt_test_task_heartbeat_standard_smoke(void);
extern _Bool leanrt_test_task_heartbeat_dedicated_smoke(void);
extern void leanrt_test_task_heartbeat_snapshot(leanrt_task_heartbeat_snapshot * out);

static leanrt_task_heartbeat_snapshot snapshot(void) {
    leanrt_task_heartbeat_snapshot out;
    leanrt_test_task_heartbeat_snapshot(&out);
    return out;
}

static void assert_standard_boundaries(void) {
    const leanrt_task_heartbeat_snapshot snap = snapshot();
    assert(snap.pre_spawn_before_reset == 0);
    assert(snap.pre_spawn == 0);
    assert(snap.post_spawn_before_reset > 0);
    assert(snap.post_spawn == 0);
    assert(snap.post_run_before_reset == 0);
    assert(snap.post_run == 0);
}

static void assert_dedicated_boundaries(void) {
    const leanrt_task_heartbeat_snapshot snap = snapshot();
    assert(snap.pre_spawn_before_reset == 0);
    assert(snap.pre_spawn == 0);
    assert(snap.post_spawn_before_reset > 0);
    assert(snap.post_spawn == 0);
    assert(snap.post_run_before_reset == 0);
    assert(snap.post_run == 0);
}

int main(void) {
    assert(leanrt_test_task_heartbeat_standard_smoke());
    assert_standard_boundaries();

    assert(leanrt_test_task_heartbeat_dedicated_smoke());
    assert_dedicated_boundaries();
    return 0;
}
