// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ProofUtil
// Imports: Lean.Meta.Tactic.Grind.Types
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
static lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3;
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2;
size_t lean_array_size(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_name_append_index_after(x_1, x_11);
x_13 = lean_apply_1(x_2, x_8);
x_14 = l_Lean_Expr_letE___override(x_12, x_3, x_13, x_10, x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_11, x_15);
lean_dec(x_11);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_7, 0, x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
lean_inc(x_19);
x_20 = lean_name_append_index_after(x_1, x_19);
x_21 = lean_apply_1(x_2, x_8);
x_22 = l_Lean_Expr_letE___override(x_20, x_3, x_21, x_18, x_4);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_19, x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1;
x_2 = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5;
x_2 = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4;
x_3 = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3;
x_4 = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2;
x_5 = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6;
x_2 = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_8 = x_1;
} else {
 lean_dec_ref(x_1);
 x_8 = lean_box(0);
}
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0___boxed), 1, 0);
x_12 = lean_box(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed), 7, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_4);
lean_closure_set(x_13, 3, x_12);
x_27 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_28 = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9;
x_29 = lean_array_get_size(x_7);
x_30 = lean_nat_dec_lt(x_9, x_29);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec_ref(x_7);
x_14 = x_27;
goto block_26;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_29, x_29);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec_ref(x_7);
x_14 = x_27;
goto block_26;
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2), 3, 0);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__3), 4, 2);
lean_closure_set(x_33, 0, x_28);
lean_closure_set(x_33, 1, x_32);
x_34 = 0;
x_35 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_28, x_33, x_7, x_34, x_35, x_27);
x_14 = x_36;
goto block_26;
}
}
block_26:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_15 = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9;
x_16 = lean_array_size(x_14);
x_17 = 0;
lean_inc_ref(x_14);
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_15, x_11, x_16, x_17, x_14);
x_19 = lean_expr_abstract(x_2, x_18);
lean_dec_ref(x_18);
x_20 = lean_array_get_size(x_14);
x_21 = l_Array_reverse___redArg(x_14);
if (lean_is_scalar(x_8)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_8;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_size(x_21);
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_15, x_21, x_13, x_23, x_17, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
return x_25;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_mkLetOfMap___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
x_9 = l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_mkLetOfMap___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLetOfMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_mkLetOfMap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ProofUtil(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0 = _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0);
l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1 = _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1);
l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2 = _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2);
l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3 = _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3);
l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4 = _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4);
l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5 = _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5);
l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6 = _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6);
l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7 = _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7);
l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8 = _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8);
l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9 = _init_l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
