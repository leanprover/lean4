// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Types
// Imports: Lean.Meta.Tactic.Grind.Arith.Offset.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
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
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState___closed__9;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState___closed__8;
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState___closed__4;
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___spec__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState___closed__2;
static size_t l_Lean_Meta_Grind_Arith_instInhabitedState___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState___closed__7;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState___closed__6;
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__4;
x_3 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__6;
x_4 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_2);
lean_ctor_set(x_4, 6, x_2);
lean_ctor_set(x_4, 7, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__4;
x_4 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__6;
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___spec__1;
x_8 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_3);
lean_ctor_set(x_8, 4, x_3);
lean_ctor_set(x_8, 5, x_3);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_1);
lean_ctor_set(x_8, 8, x_4);
lean_ctor_set(x_8, 9, x_3);
lean_ctor_set(x_8, 10, x_3);
lean_ctor_set(x_8, 11, x_5);
lean_ctor_set(x_8, 12, x_2);
lean_ctor_set(x_8, 13, x_4);
lean_ctor_set(x_8, 14, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*15, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__7;
x_2 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_instInhabitedState___closed__9;
return x_1;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Offset_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Offset_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_instInhabitedState___closed__1 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState___closed__1);
l_Lean_Meta_Grind_Arith_instInhabitedState___closed__2 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState___closed__2);
l_Lean_Meta_Grind_Arith_instInhabitedState___closed__3 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__3();
l_Lean_Meta_Grind_Arith_instInhabitedState___closed__4 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState___closed__4);
l_Lean_Meta_Grind_Arith_instInhabitedState___closed__5 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState___closed__5);
l_Lean_Meta_Grind_Arith_instInhabitedState___closed__6 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState___closed__6);
l_Lean_Meta_Grind_Arith_instInhabitedState___closed__7 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState___closed__7);
l_Lean_Meta_Grind_Arith_instInhabitedState___closed__8 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState___closed__8);
l_Lean_Meta_Grind_Arith_instInhabitedState___closed__9 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState___closed__9);
l_Lean_Meta_Grind_Arith_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
