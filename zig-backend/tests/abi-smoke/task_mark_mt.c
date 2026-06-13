#include <assert.h>

typedef struct {
    unsigned dequeued_closures;
    unsigned published_values;
    _Bool all_dequeued_closures_marked;
    _Bool all_published_values_marked;
    int last_dequeued_closure_rc;
    int last_published_value_rc;
} leanrt_task_mark_mt_snapshot;

extern _Bool leanrt_test_task_mark_mt_spawn_smoke(void);
extern _Bool leanrt_test_task_mark_mt_map_smoke(void);
extern _Bool leanrt_test_task_mark_mt_bind_smoke(void);
extern _Bool leanrt_test_task_mark_mt_spawn_stress(unsigned iterations);
extern void leanrt_test_task_mark_mt_snapshot(leanrt_task_mark_mt_snapshot * out);

static leanrt_task_mark_mt_snapshot snapshot(void) {
    leanrt_task_mark_mt_snapshot out;
    leanrt_test_task_mark_mt_snapshot(&out);
    return out;
}

static void assert_all_marked(const leanrt_task_mark_mt_snapshot * snap,
                              unsigned min_closures,
                              unsigned min_values) {
    assert(snap->dequeued_closures >= min_closures);
    assert(snap->published_values >= min_values);
    assert(snap->all_dequeued_closures_marked);
    assert(snap->all_published_values_marked);
    assert(snap->last_dequeued_closure_rc < 0);
    assert(snap->last_published_value_rc < 0);
}

int main(void) {
    assert(leanrt_test_task_mark_mt_spawn_smoke());
    leanrt_task_mark_mt_snapshot snap = snapshot();
    assert_all_marked(&snap, 1, 1);

    assert(leanrt_test_task_mark_mt_map_smoke());
    snap = snapshot();
    assert_all_marked(&snap, 2, 2);

    assert(leanrt_test_task_mark_mt_bind_smoke());
    snap = snapshot();
    assert_all_marked(&snap, 2, 2);

    assert(leanrt_test_task_mark_mt_spawn_stress(1000));
    snap = snapshot();
    assert(snap.dequeued_closures == 1000);
    assert(snap.published_values == 1000);
    assert_all_marked(&snap, 1000, 1000);
    return 0;
}
