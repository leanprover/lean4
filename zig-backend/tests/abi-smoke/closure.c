#include <lean/lean.h>

#include <stdint.h>
#include <stdio.h>

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);

#define CHECK(cond)                                                                 \
    do {                                                                            \
        if (!(cond)) {                                                              \
            fprintf(stderr, "FAIL:%s:%d: %s\n", __FILE__, __LINE__, #cond);         \
            return 1;                                                               \
        }                                                                           \
    } while (0)

static lean_object *sum2(lean_object *a, lean_object *b) {
    return lean_box(lean_unbox(a) + lean_unbox(b));
}

static lean_object *sum3(lean_object *a, lean_object *b, lean_object *c) {
    return lean_box(lean_unbox(a) + lean_unbox(b) + lean_unbox(c));
}

static lean_object *add_fixed(lean_object *fixed, lean_object *extra) {
    return lean_box(lean_unbox(fixed) + lean_unbox(extra));
}

static lean_object *make_adder(lean_object *base) {
    lean_object *closure = lean_alloc_closure((void *)add_fixed, 2, 1);
    if (closure == NULL) {
        fprintf(stderr, "FAIL:%s:%d: lean_alloc_closure returned NULL\n", __FILE__, __LINE__);
        return NULL;
    }
    ((lean_closure_object *)closure)->m_objs[0] = base;
    return closure;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_initialize_thread();

    lean_object *created = lean_alloc_closure((void *)sum2, 2, 1);
    CHECK(created != NULL);
    CHECK(lean_obj_tag(created) == LeanClosure);
    CHECK(((lean_closure_object *)created)->m_fun == (void *)sum2);
    CHECK(((lean_closure_object *)created)->m_arity == 2);
    CHECK(((lean_closure_object *)created)->m_num_fixed == 1);
    ((lean_closure_object *)created)->m_objs[0] = lean_box(9);
    lean_dec(created);

    lean_object *exact = lean_alloc_closure((void *)sum2, 2, 0);
    CHECK(exact != NULL);
    lean_object *exact_result = lean_apply_2(exact, lean_box(10), lean_box(32));
    CHECK(lean_is_scalar(exact_result));
    CHECK(lean_unbox(exact_result) == 42);

    lean_object *partial_src = lean_alloc_closure((void *)sum3, 3, 0);
    CHECK(partial_src != NULL);
    lean_object *partial = lean_apply_2(partial_src, lean_box(10), lean_box(20));
    CHECK(partial != NULL);
    CHECK(lean_obj_tag(partial) == LeanClosure);
    CHECK(((lean_closure_object *)partial)->m_fun == (void *)sum3);
    CHECK(((lean_closure_object *)partial)->m_arity == 3);
    CHECK(((lean_closure_object *)partial)->m_num_fixed == 2);
    CHECK(((lean_closure_object *)partial)->m_objs[0] == lean_box(10));
    CHECK(((lean_closure_object *)partial)->m_objs[1] == lean_box(20));

    lean_object *partial_result = lean_apply_1(partial, lean_box(12));
    CHECK(lean_is_scalar(partial_result));
    CHECK(lean_unbox(partial_result) == 42);

    lean_object *over = lean_alloc_closure((void *)make_adder, 1, 0);
    CHECK(over != NULL);
    lean_object *over_result = lean_apply_2(over, lean_box(40), lean_box(2));
    CHECK(lean_is_scalar(over_result));
    CHECK(lean_unbox(over_result) == 42);

    lean_finalize_thread();
    return 0;
}
