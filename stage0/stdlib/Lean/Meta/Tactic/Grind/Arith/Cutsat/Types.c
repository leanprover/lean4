// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
// Imports: Init.Data.Int.Linear Lean.Data.PersistentArray Lean.Meta.Tactic.Grind.ENodeKey Lean.Meta.Tactic.Grind.Arith.Util
#include <lean/lean.h>
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__7;
static size_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__6;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__6;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__7;
return x_1;
}
}
lean_object* initialize_Init_Data_Int_Linear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_ENodeKey(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Linear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ENodeKey(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__3();
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
