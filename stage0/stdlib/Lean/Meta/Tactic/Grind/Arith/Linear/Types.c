// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Types
// Imports: Std.Internal.Rat Init.Grind.Ordered.Linarith Lean.Data.PersistentArray Lean.Meta.Tactic.Grind.ExprPtr
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10_(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__2;
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = 1;
x_7 = lean_uint64_of_nat(x_4);
x_8 = l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10_(x_5);
x_9 = l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1;
x_10 = lean_int_dec_lt(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; 
x_11 = lean_nat_abs(x_3);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_mul(x_12, x_11);
lean_dec(x_11);
x_14 = lean_uint64_of_nat(x_13);
lean_dec(x_13);
x_15 = lean_uint64_mix_hash(x_6, x_14);
x_16 = lean_uint64_mix_hash(x_15, x_7);
x_17 = lean_uint64_mix_hash(x_16, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; 
x_18 = lean_nat_abs(x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_18, x_19);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_mul(x_21, x_20);
lean_dec(x_20);
x_23 = lean_nat_add(x_22, x_19);
lean_dec(x_22);
x_24 = lean_uint64_of_nat(x_23);
lean_dec(x_23);
x_25 = lean_uint64_mix_hash(x_6, x_24);
x_26 = lean_uint64_mix_hash(x_25, x_7);
x_27 = lean_uint64_mix_hash(x_26, x_8);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__3;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__4;
return x_1;
}
}
lean_object* initialize_Std_Internal_Rat(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Ordered_Linarith(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_ExprPtr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Rat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Linarith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ExprPtr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1);
l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1);
l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean = _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__2);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__3);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__4 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__4);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
