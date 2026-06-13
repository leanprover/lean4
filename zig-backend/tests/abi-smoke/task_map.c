#include <assert.h>

#include <lean/lean.h>

static lean_object * blocked_producer(lean_object * unit) {
    (void)unit;
    return lean_box(42);
}

static lean_object * map_add_one(lean_object * value) {
    return lean_box(lean_unbox(value) + 1);
}

int main(void) {
    lean_object * producer_closure = lean_alloc_closure((void *)blocked_producer, 1, 0);
    lean_object * producer_task = lean_task_spawn_core(producer_closure, 0, 0);

    lean_object * map_closure = lean_alloc_closure((void *)map_add_one, 1, 0);
    lean_object * mapped_task = lean_task_map_core(map_closure, producer_task, 0, 0, 0);
    assert(lean_unbox(lean_task_get(mapped_task)) == 43);

    lean_dec(mapped_task);
    return 0;
}
