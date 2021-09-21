// Lean compiler output
// Module: Lean.Util.CollectMVars
// Imports: Init Lean.Expr
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
LEAN_EXPORT lean_object* l_Lean_CollectMVars_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectMVars_instInhabitedState;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_CollectMVars_instInhabitedState___closed__2;
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t l_UInt64_toUSize(uint64_t);
static lean_object* l_Lean_CollectMVars_State_visitedExpr___default___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashSet___at_Lean_CollectMVars_State_visitedExpr___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_collectMVars(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_CollectMVars_visit___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_CollectMVars_visit___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_CollectMVars_visit___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_CollectMVars_visit___spec__2___boxed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_CollectMVars_State_result___default___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_CollectMVars_visit___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSetImp_expand___at_Lean_CollectMVars_visit___spec__4(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSetImp_moveEntries___at_Lean_CollectMVars_visit___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectMVars_State_visitedExpr___default;
static lean_object* l_Lean_CollectMVars_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Lean_CollectMVars_State_result___default;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectMVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashSet___at_Lean_CollectMVars_State_visitedExpr___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_CollectMVars_State_visitedExpr___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_CollectMVars_State_visitedExpr___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_CollectMVars_State_visitedExpr___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_CollectMVars_State_result___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_CollectMVars_State_result___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_CollectMVars_State_result___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_CollectMVars_instInhabitedState___closed__1;
x_2 = l_Lean_CollectMVars_State_result___default___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_CollectMVars_instInhabitedState___closed__2;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lean_CollectMVars_visit___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_expr_eqv(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = (size_t)x_5;
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_List_elem___at_Lean_CollectMVars_visit___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_CollectMVars_visit___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = (size_t)x_7;
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 1, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Expr_hash(x_13);
x_17 = (size_t)x_16;
x_18 = lean_usize_modn(x_17, x_15);
lean_dec(x_15);
x_19 = lean_array_uget(x_1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_uset(x_1, x_18, x_20);
x_1 = x_21;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSetImp_moveEntries___at_Lean_CollectMVars_visit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at_Lean_CollectMVars_visit___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashSetImp_expand___at_Lean_CollectMVars_visit___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashSetImp_moveEntries___at_Lean_CollectMVars_visit___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_CollectMVars_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_expr_eqv(x_6, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_List_replace___at_Lean_CollectMVars_visit___spec__7(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_expr_eqv(x_10, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_List_replace___at_Lean_CollectMVars_visit___spec__7(x_11, x_2, x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = (size_t)x_7;
x_9 = lean_usize_modn(x_8, x_6);
x_10 = lean_array_uget(x_5, x_9);
x_11 = l_List_elem___at_Lean_CollectMVars_visit___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_array_uset(x_5, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_6);
lean_dec(x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashSetImp_expand___at_Lean_CollectMVars_visit___spec__4(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_inc(x_2);
x_18 = l_List_replace___at_Lean_CollectMVars_visit___spec__7(x_10, x_2, x_2);
lean_dec(x_2);
x_19 = lean_array_uset(x_5, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Expr_hash(x_2);
x_24 = (size_t)x_23;
x_25 = lean_usize_modn(x_24, x_22);
x_26 = lean_array_uget(x_21, x_25);
x_27 = l_List_elem___at_Lean_CollectMVars_visit___spec__2(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_20, x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_26);
x_31 = lean_array_uset(x_21, x_25, x_30);
x_32 = lean_nat_dec_le(x_29, x_22);
lean_dec(x_22);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Std_HashSetImp_expand___at_Lean_CollectMVars_visit___spec__4(x_29, x_31);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_22);
lean_inc(x_2);
x_35 = l_List_replace___at_Lean_CollectMVars_visit___spec__7(x_26, x_2, x_2);
lean_dec(x_2);
x_36 = lean_array_uset(x_21, x_25, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectMVars_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasMVar(x_1);
if (x_3 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_4);
x_6 = l_Std_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_4, x_1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_inc(x_1);
x_10 = l_Std_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_4, x_1);
lean_ctor_set(x_2, 0, x_10);
x_11 = l_Lean_CollectMVars_main(x_1, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Std_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_4, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
x_14 = l_Lean_CollectMVars_main(x_1, x_13);
return x_14;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectMVars_main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_push(x_5, x_3);
lean_ctor_set(x_2, 1, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_array_push(x_8, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_CollectMVars_visit(x_11, x_2);
x_14 = l_Lean_CollectMVars_visit(x_12, x_13);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_CollectMVars_visit(x_15, x_2);
x_18 = l_Lean_CollectMVars_visit(x_16, x_17);
return x_18;
}
case 7:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_CollectMVars_visit(x_19, x_2);
x_22 = l_Lean_CollectMVars_visit(x_20, x_21);
return x_22;
}
case 8:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lean_CollectMVars_visit(x_23, x_2);
x_27 = l_Lean_CollectMVars_visit(x_24, x_26);
x_28 = l_Lean_CollectMVars_visit(x_25, x_27);
return x_28;
}
case 10:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lean_CollectMVars_visit(x_29, x_2);
return x_30;
}
case 11:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lean_CollectMVars_visit(x_31, x_2);
return x_32;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_CollectMVars_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_CollectMVars_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_CollectMVars_visit___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lean_CollectMVars_visit___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CollectMVars_visit(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectMVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectMVars_State_visitedExpr___default___closed__1 = _init_l_Lean_CollectMVars_State_visitedExpr___default___closed__1();
lean_mark_persistent(l_Lean_CollectMVars_State_visitedExpr___default___closed__1);
l_Lean_CollectMVars_State_visitedExpr___default = _init_l_Lean_CollectMVars_State_visitedExpr___default();
lean_mark_persistent(l_Lean_CollectMVars_State_visitedExpr___default);
l_Lean_CollectMVars_State_result___default___closed__1 = _init_l_Lean_CollectMVars_State_result___default___closed__1();
lean_mark_persistent(l_Lean_CollectMVars_State_result___default___closed__1);
l_Lean_CollectMVars_State_result___default = _init_l_Lean_CollectMVars_State_result___default();
lean_mark_persistent(l_Lean_CollectMVars_State_result___default);
l_Lean_CollectMVars_instInhabitedState___closed__1 = _init_l_Lean_CollectMVars_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_CollectMVars_instInhabitedState___closed__1);
l_Lean_CollectMVars_instInhabitedState___closed__2 = _init_l_Lean_CollectMVars_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_CollectMVars_instInhabitedState___closed__2);
l_Lean_CollectMVars_instInhabitedState = _init_l_Lean_CollectMVars_instInhabitedState();
lean_mark_persistent(l_Lean_CollectMVars_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
