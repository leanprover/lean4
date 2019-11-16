// Lean compiler output
// Module: Init.Lean.TypeClass.Basic
// Imports: Init.Lean.Environment Init.Lean.TypeClass.Synth
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_PersistentHashMap_empty___rarg___closed__2;
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
lean_object* l_Lean_TypeClass_synthCommand___closed__1;
lean_object* l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1___closed__1;
lean_object* l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1;
lean_object* l_Queue_empty(lean_object*);
lean_object* l_Lean_TypeClass_synth(lean_object*, lean_object*, lean_object*);
lean_object* lean_typeclass_synth_command(lean_object*, lean_object*);
lean_object* _init_l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PersistentHashMap_empty___rarg___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_TypeClass_synthCommand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Queue_empty(lean_box(0));
return x_1;
}
}
lean_object* lean_typeclass_synth_command(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_box(0);
x_4 = l_Lean_Expr_Inhabited___closed__1;
x_5 = l_Array_empty___closed__1;
x_6 = l_Lean_TypeClass_synthCommand___closed__1;
x_7 = l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1;
x_8 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_6);
lean_ctor_set(x_8, 6, x_7);
x_9 = lean_unsigned_to_nat(100000u);
x_10 = l_Lean_TypeClass_synth(x_2, x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_TypeClass_Synth(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_TypeClass_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_TypeClass_Synth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1___closed__1 = _init_l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1___closed__1();
lean_mark_persistent(l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1___closed__1);
l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1 = _init_l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1();
lean_mark_persistent(l_PersistentHashMap_empty___at_Lean_TypeClass_synthCommand___spec__1);
l_Lean_TypeClass_synthCommand___closed__1 = _init_l_Lean_TypeClass_synthCommand___closed__1();
lean_mark_persistent(l_Lean_TypeClass_synthCommand___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
