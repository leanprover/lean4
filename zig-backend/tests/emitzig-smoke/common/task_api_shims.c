#define lean_alloc_closure lean_alloc_closure_inline
#define lean_closure_set lean_closure_set_inline
#define lean_task_spawn lean_task_spawn_inline
#define lean_task_bind lean_task_bind_inline
#define lean_task_get_own lean_task_get_own_inline
#include <lean/lean.h>
#undef lean_alloc_closure
#undef lean_closure_set
#undef lean_task_spawn
#undef lean_task_bind
#undef lean_task_get_own

lean_object * lean_alloc_closure(void * fun, unsigned arity, unsigned num_fixed) {
  lean_closure_object * o;
  assert(arity > 0);
  assert(num_fixed < arity);
  o = (lean_closure_object *)lean_alloc_object(
    lean_usize_add_checked(sizeof(lean_closure_object), lean_usize_mul_checked(sizeof(void *), num_fixed)));
  lean_set_st_header((lean_object *)o, LeanClosure, 0);
  o->m_fun = fun;
  o->m_arity = arity;
  o->m_num_fixed = num_fixed;
  return (lean_object *)o;
}

void lean_closure_set(lean_object * o, unsigned i, lean_object * a) {
  assert(i < lean_closure_num_fixed(o));
  lean_to_closure(o)->m_objs[i] = a;
}

lean_object * lean_task_spawn(lean_object * c, lean_object * prio) {
  return lean_task_spawn_core(c, lean_unbox(prio), false);
}

lean_object * lean_task_bind(lean_object * x, lean_object * f, lean_object * prio, uint8_t sync) {
  return lean_task_bind_core(x, f, lean_unbox(prio), sync, false);
}

lean_object * lean_task_get_own(lean_object * t) {
  lean_object * r = lean_task_get(t);
  lean_inc(r);
  lean_dec(t);
  return r;
}
