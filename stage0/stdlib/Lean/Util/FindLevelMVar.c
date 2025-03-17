// Lean compiler output
// Module: Lean.Util.FindLevelMVar
// Imports: Lean.Expr
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
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_mainLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_findLevelMVar_x3f(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visitLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_mainLevel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1___at_Lean_FindLevelMVar_main___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visitLevel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_main(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1___at_Lean_FindLevelMVar_main___spec__4___closed__1;
uint8_t l_Lean_Expr_hasLevelMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visitLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Level_hasMVar(x_2);
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_FindLevelMVar_mainLevel(x_1, x_2, x_3);
return x_5;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_mainLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_FindLevelMVar_visitLevel(x_1, x_4, x_3);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
x_8 = l_Lean_FindLevelMVar_visitLevel(x_1, x_7, x_3);
x_9 = l_Lean_FindLevelMVar_visitLevel(x_1, x_6, x_8);
lean_dec(x_8);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_FindLevelMVar_visitLevel(x_1, x_11, x_3);
x_13 = l_Lean_FindLevelMVar_visitLevel(x_1, x_10, x_12);
lean_dec(x_12);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_14);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_14);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visitLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindLevelMVar_visitLevel(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_mainLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindLevelMVar_mainLevel(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_FindLevelMVar_main(x_1, x_2, x_3);
return x_5;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Lean_FindLevelMVar_visitLevel(x_2, x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 1;
x_9 = lean_usize_sub(x_3, x_8);
x_10 = lean_array_uget(x_2, x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__2___lambda__1), 4, 3);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
x_3 = x_9;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_apply_1(x_5, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 1;
x_9 = lean_usize_sub(x_3, x_8);
x_10 = lean_array_uget(x_2, x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__2___lambda__1), 4, 3);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
x_3 = x_9;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_apply_1(x_5, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_mk(x_3);
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_le(x_6, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_apply_1(x_2, x_4);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = 0;
x_13 = l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__2(x_1, x_5, x_11, x_12, x_2, x_4);
lean_dec(x_5);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_6);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_16 = lean_apply_1(x_2, x_4);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = 0;
x_19 = l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__3(x_1, x_5, x_17, x_18, x_2, x_4);
lean_dec(x_5);
return x_19;
}
}
}
}
static lean_object* _init_l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1___at_Lean_FindLevelMVar_main___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1___at_Lean_FindLevelMVar_main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_mk(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_le(x_5, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = 0;
x_11 = l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1___at_Lean_FindLevelMVar_main___spec__4___closed__1;
x_12 = l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__2(x_1, x_4, x_9, x_10, x_11, x_3);
lean_dec(x_4);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_5);
if (x_14 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_16 = 0;
x_17 = l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1___at_Lean_FindLevelMVar_main___spec__4___closed__1;
x_18 = l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__3(x_1, x_4, x_15, x_16, x_17, x_3);
lean_dec(x_4);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_FindLevelMVar_visitLevel(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
case 4:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1___at_Lean_FindLevelMVar_main___spec__4(x_1, x_6, x_3);
return x_7;
}
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_10 = l_Lean_FindLevelMVar_visit(x_1, x_8, x_3);
x_11 = l_Lean_FindLevelMVar_visit(x_1, x_9, x_10);
return x_11;
}
case 6:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_Lean_FindLevelMVar_visit(x_1, x_12, x_3);
x_15 = l_Lean_FindLevelMVar_visit(x_1, x_13, x_14);
return x_15;
}
case 7:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_1);
x_18 = l_Lean_FindLevelMVar_visit(x_1, x_16, x_3);
x_19 = l_Lean_FindLevelMVar_visit(x_1, x_17, x_18);
return x_19;
}
case 8:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_1);
x_23 = l_Lean_FindLevelMVar_visit(x_1, x_20, x_3);
lean_inc(x_1);
x_24 = l_Lean_FindLevelMVar_visit(x_1, x_21, x_23);
x_25 = l_Lean_FindLevelMVar_visit(x_1, x_22, x_24);
return x_25;
}
case 10:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_Lean_FindLevelMVar_visit(x_1, x_26, x_3);
return x_27;
}
case 11:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_Lean_FindLevelMVar_visit(x_1, x_28, x_3);
return x_29;
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__2(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldrMUnsafe_fold___at_Lean_FindLevelMVar_main___spec__3(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findLevelMVar_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindLevelMVar_main(x_2, x_1, x_3);
return x_4;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FindLevelMVar(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1___at_Lean_FindLevelMVar_main___spec__4___closed__1 = _init_l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1___at_Lean_FindLevelMVar_main___spec__4___closed__1();
lean_mark_persistent(l_List_foldrTR___at_Lean_FindLevelMVar_main___spec__1___at_Lean_FindLevelMVar_main___spec__4___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
