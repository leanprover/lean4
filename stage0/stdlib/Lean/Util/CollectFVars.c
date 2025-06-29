// Lean compiler output
// Module: Lean.Util.CollectFVars
// Imports: Lean.Expr Lean.LocalContext
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_CollectFVars_instInhabitedState___closed__3;
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_CollectFVars_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_CollectFVars_instInhabitedState___closed__4;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_CollectFVars_instInhabitedState___closed__2;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_instInhabitedState;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_CollectFVars_instInhabitedState___closed__5;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_CollectFVars_instInhabitedState___closed__0;
static lean_object* l_Lean_CollectFVars_instInhabitedState___closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_CollectFVars_instInhabitedState___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_CollectFVars_instInhabitedState___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_CollectFVars_instInhabitedState___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_CollectFVars_instInhabitedState___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_CollectFVars_instInhabitedState___closed__5;
x_2 = lean_box(0);
x_3 = l_Lean_CollectFVars_instInhabitedState___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_CollectFVars_instInhabitedState___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_add(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_6 = l_Lean_FVarIdSet_insert(x_4, x_2);
x_7 = lean_array_push(x_5, x_2);
lean_ctor_set(x_1, 2, x_7);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_2);
x_11 = l_Lean_FVarIdSet_insert(x_9, x_2);
x_12 = lean_array_push(x_10, x_2);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Expr_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasFVar(x_1);
if (x_3 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
x_14 = l_Lean_Expr_hash(x_1);
x_15 = 32;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = 16;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_23 = 1;
x_24 = lean_usize_sub(x_22, x_23);
x_25 = lean_usize_land(x_21, x_24);
x_26 = lean_array_uget(x_12, x_25);
x_27 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___redArg(x_1, x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_2, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_2, 0);
lean_dec(x_31);
if (x_27 == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_33 = lean_ctor_get(x_4, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 0);
lean_dec(x_34);
x_35 = lean_box(0);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_11, x_36);
lean_dec(x_11);
lean_inc(x_1);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 2, x_26);
lean_ctor_set(x_2, 1, x_35);
lean_ctor_set(x_2, 0, x_1);
x_38 = lean_array_uset(x_12, x_25, x_2);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_37, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_38);
lean_ctor_set(x_4, 1, x_45);
lean_ctor_set(x_4, 0, x_37);
x_7 = x_4;
goto block_10;
}
else
{
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_37);
x_7 = x_4;
goto block_10;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_4);
x_46 = lean_box(0);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_11, x_47);
lean_dec(x_11);
lean_inc(x_1);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 2, x_26);
lean_ctor_set(x_2, 1, x_46);
lean_ctor_set(x_2, 0, x_1);
x_49 = lean_array_uset(x_12, x_25, x_2);
x_50 = lean_unsigned_to_nat(4u);
x_51 = lean_nat_mul(x_48, x_50);
x_52 = lean_unsigned_to_nat(3u);
x_53 = lean_nat_div(x_51, x_52);
lean_dec(x_51);
x_54 = lean_array_get_size(x_49);
x_55 = lean_nat_dec_le(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_56);
x_7 = x_57;
goto block_10;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_49);
x_7 = x_58;
goto block_10;
}
}
}
else
{
lean_free_object(x_2);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
x_7 = x_4;
goto block_10;
}
}
else
{
lean_dec(x_2);
if (x_27 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_59 = x_4;
} else {
 lean_dec_ref(x_4);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_11, x_61);
lean_dec(x_11);
lean_inc(x_1);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_26);
x_64 = lean_array_uset(x_12, x_25, x_63);
x_65 = lean_unsigned_to_nat(4u);
x_66 = lean_nat_mul(x_62, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = lean_nat_div(x_66, x_67);
lean_dec(x_66);
x_69 = lean_array_get_size(x_64);
x_70 = lean_nat_dec_le(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_64);
if (lean_is_scalar(x_59)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_59;
}
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_71);
x_7 = x_72;
goto block_10;
}
else
{
lean_object* x_73; 
if (lean_is_scalar(x_59)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_59;
}
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_64);
x_7 = x_73;
goto block_10;
}
}
else
{
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
x_7 = x_4;
goto block_10;
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_6);
x_9 = l_Lean_CollectFVars_main(x_1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_CollectFVars_State_add(x_2, x_9);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_CollectFVars_visit(x_11, x_2);
x_14 = l_Lean_CollectFVars_visit(x_12, x_13);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
x_3 = x_15;
x_4 = x_16;
x_5 = x_2;
goto block_8;
}
case 7:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_dec(x_1);
x_3 = x_17;
x_4 = x_18;
x_5 = x_2;
goto block_8;
}
case 8:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_CollectFVars_visit(x_19, x_2);
x_23 = l_Lean_CollectFVars_visit(x_20, x_22);
x_24 = l_Lean_CollectFVars_visit(x_21, x_23);
return x_24;
}
case 10:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lean_CollectFVars_visit(x_25, x_2);
return x_26;
}
case 11:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lean_CollectFVars_visit(x_27, x_2);
return x_28;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_CollectFVars_visit(x_3, x_5);
x_7 = l_Lean_CollectFVars_visit(x_4, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_collectFVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CollectFVars_main(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LocalContext(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LocalContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectFVars_instInhabitedState___closed__0 = _init_l_Lean_CollectFVars_instInhabitedState___closed__0();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState___closed__0);
l_Lean_CollectFVars_instInhabitedState___closed__1 = _init_l_Lean_CollectFVars_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState___closed__1);
l_Lean_CollectFVars_instInhabitedState___closed__2 = _init_l_Lean_CollectFVars_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState___closed__2);
l_Lean_CollectFVars_instInhabitedState___closed__3 = _init_l_Lean_CollectFVars_instInhabitedState___closed__3();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState___closed__3);
l_Lean_CollectFVars_instInhabitedState___closed__4 = _init_l_Lean_CollectFVars_instInhabitedState___closed__4();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState___closed__4);
l_Lean_CollectFVars_instInhabitedState___closed__5 = _init_l_Lean_CollectFVars_instInhabitedState___closed__5();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState___closed__5);
l_Lean_CollectFVars_instInhabitedState___closed__6 = _init_l_Lean_CollectFVars_instInhabitedState___closed__6();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState___closed__6);
l_Lean_CollectFVars_instInhabitedState = _init_l_Lean_CollectFVars_instInhabitedState();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
