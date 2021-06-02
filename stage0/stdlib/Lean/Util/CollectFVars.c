// Lean compiler output
// Module: Lean.Util.CollectFVars
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
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_CollectFVars_State_fvarSet___default;
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
lean_object* l_Lean_CollectFVars_main_match__1(lean_object*);
lean_object* l_List_foldl___at_Lean_CollectFVars_visit___spec__6(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t l_UInt64_toUSize(uint64_t);
lean_object* l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_CollectFVars_visit___spec__2(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_List_elem___at_Lean_CollectFVars_visit___spec__2___boxed(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_List_replace___at_Lean_CollectFVars_visit___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_visit(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_instInhabitedHashSet___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_HashSetImp_expand___at_Lean_CollectFVars_visit___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_State_visitedExpr___default;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_instInhabitedState;
lean_object* l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_HashSetImp_moveEntries___at_Lean_CollectFVars_visit___spec__5(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_instInhabitedState___closed__1;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_List_replace___at_Lean_CollectFVars_visit___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashSet___at_Lean_CollectFVars_State_visitedExpr___default___spec__1(lean_object*);
lean_object* l_Lean_CollectFVars_State_visitedExpr___default___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_mkHashSet___at_Lean_CollectFVars_State_visitedExpr___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_CollectFVars_State_visitedExpr___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_CollectFVars_State_visitedExpr___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_CollectFVars_State_visitedExpr___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_CollectFVars_State_fvarSet___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_CollectFVars_instInhabitedState___closed__1;
return x_1;
}
}
uint8_t l_List_elem___at_Lean_CollectFVars_visit___spec__2(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = (size_t)x_5;
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
x_9 = l_List_elem___at_Lean_CollectFVars_visit___spec__2(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_List_foldl___at_Lean_CollectFVars_visit___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashSetImp_moveEntries___at_Lean_CollectFVars_visit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at_Lean_CollectFVars_visit___spec__6(x_3, x_6);
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
lean_object* l_Std_HashSetImp_expand___at_Lean_CollectFVars_visit___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashSetImp_moveEntries___at_Lean_CollectFVars_visit___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_List_replace___at_Lean_CollectFVars_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_replace___at_Lean_CollectFVars_visit___spec__7(x_7, x_2, x_3);
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
x_13 = l_List_replace___at_Lean_CollectFVars_visit___spec__7(x_11, x_2, x_3);
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
lean_object* l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_11 = l_List_elem___at_Lean_CollectFVars_visit___spec__2(x_2, x_10);
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
x_17 = l_Std_HashSetImp_expand___at_Lean_CollectFVars_visit___spec__4(x_13, x_15);
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
x_18 = l_List_replace___at_Lean_CollectFVars_visit___spec__7(x_10, x_2, x_2);
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
x_27 = l_List_elem___at_Lean_CollectFVars_visit___spec__2(x_2, x_26);
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
x_33 = l_Std_HashSetImp_expand___at_Lean_CollectFVars_visit___spec__4(x_29, x_31);
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
x_35 = l_List_replace___at_Lean_CollectFVars_visit___spec__7(x_26, x_2, x_2);
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
lean_object* l_Lean_CollectFVars_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasFVar(x_2);
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_5, x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
lean_inc(x_2);
x_11 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_5, x_2);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_apply_2(x_1, x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_inc(x_2);
x_13 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_5, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_apply_2(x_1, x_2, x_14);
return x_15;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_List_elem___at_Lean_CollectFVars_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_CollectFVars_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_replace___at_Lean_CollectFVars_visit___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lean_CollectFVars_visit___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_CollectFVars_main_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_2(x_8, x_10, x_12);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_17 = lean_box_uint64(x_16);
x_18 = lean_apply_3(x_6, x_14, x_15, x_17);
return x_18;
}
case 6:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_4(x_4, x_19, x_20, x_21, x_23);
return x_24;
}
case 7:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_29 = lean_box_uint64(x_28);
x_30 = lean_apply_4(x_3, x_25, x_26, x_27, x_29);
return x_30;
}
case 8:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_5(x_5, x_31, x_32, x_33, x_34, x_36);
return x_37;
}
case 10:
{
lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_41 = lean_box_uint64(x_40);
x_42 = lean_apply_3(x_7, x_38, x_39, x_41);
return x_42;
}
case 11:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_47 = lean_box_uint64(x_46);
x_48 = lean_apply_4(x_2, x_43, x_44, x_45, x_47);
return x_48;
}
default: 
{
lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_apply_1(x_9, x_1);
return x_49;
}
}
}
}
lean_object* l_Lean_CollectFVars_main_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_CollectFVars_main_match__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_CollectFVars_main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_box(0);
x_7 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_5, x_3, x_6);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_9, x_3, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_28; uint8_t x_29; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_28 = l_Lean_Expr_hasFVar(x_13);
x_29 = l_Lean_Expr_hasFVar(x_14);
if (x_28 == 0)
{
lean_dec(x_13);
if (x_29 == 0)
{
lean_dec(x_14);
return x_2;
}
else
{
x_15 = x_2;
goto block_27;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
x_32 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_30, x_13);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_2, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_2, 0);
lean_dec(x_35);
lean_inc(x_13);
x_36 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_30, x_13);
lean_ctor_set(x_2, 0, x_36);
x_37 = l_Lean_CollectFVars_main(x_13, x_2);
if (x_29 == 0)
{
lean_dec(x_14);
return x_37;
}
else
{
x_15 = x_37;
goto block_27;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
lean_inc(x_13);
x_38 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_30, x_13);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
x_40 = l_Lean_CollectFVars_main(x_13, x_39);
if (x_29 == 0)
{
lean_dec(x_14);
return x_40;
}
else
{
x_15 = x_40;
goto block_27;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_13);
if (x_29 == 0)
{
lean_dec(x_14);
return x_2;
}
else
{
x_15 = x_2;
goto block_27;
}
}
}
block_27:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_16, x_14);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
lean_inc(x_14);
x_22 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_16, x_14);
lean_ctor_set(x_15, 0, x_22);
x_1 = x_14;
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
lean_inc(x_14);
x_24 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_16, x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
x_1 = x_14;
x_2 = x_25;
goto _start;
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
return x_15;
}
}
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_56; uint8_t x_57; 
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
lean_dec(x_1);
x_56 = l_Lean_Expr_hasFVar(x_41);
x_57 = l_Lean_Expr_hasFVar(x_42);
if (x_56 == 0)
{
lean_dec(x_41);
if (x_57 == 0)
{
lean_dec(x_42);
return x_2;
}
else
{
x_43 = x_2;
goto block_55;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
x_60 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_58, x_41);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_2);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_2, 1);
lean_dec(x_62);
x_63 = lean_ctor_get(x_2, 0);
lean_dec(x_63);
lean_inc(x_41);
x_64 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_58, x_41);
lean_ctor_set(x_2, 0, x_64);
x_65 = l_Lean_CollectFVars_main(x_41, x_2);
if (x_57 == 0)
{
lean_dec(x_42);
return x_65;
}
else
{
x_43 = x_65;
goto block_55;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_2);
lean_inc(x_41);
x_66 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_58, x_41);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_59);
x_68 = l_Lean_CollectFVars_main(x_41, x_67);
if (x_57 == 0)
{
lean_dec(x_42);
return x_68;
}
else
{
x_43 = x_68;
goto block_55;
}
}
}
else
{
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_41);
if (x_57 == 0)
{
lean_dec(x_42);
return x_2;
}
else
{
x_43 = x_2;
goto block_55;
}
}
}
block_55:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
x_46 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_44, x_42);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_43, 0);
lean_dec(x_49);
lean_inc(x_42);
x_50 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_44, x_42);
lean_ctor_set(x_43, 0, x_50);
x_1 = x_42;
x_2 = x_43;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
lean_inc(x_42);
x_52 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_44, x_42);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
x_1 = x_42;
x_2 = x_53;
goto _start;
}
}
else
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_42);
return x_43;
}
}
}
case 7:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_84; uint8_t x_85; 
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 2);
lean_inc(x_70);
lean_dec(x_1);
x_84 = l_Lean_Expr_hasFVar(x_69);
x_85 = l_Lean_Expr_hasFVar(x_70);
if (x_84 == 0)
{
lean_dec(x_69);
if (x_85 == 0)
{
lean_dec(x_70);
return x_2;
}
else
{
x_71 = x_2;
goto block_83;
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_2, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_2, 1);
lean_inc(x_87);
x_88 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_86, x_69);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_2);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_2, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_2, 0);
lean_dec(x_91);
lean_inc(x_69);
x_92 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_86, x_69);
lean_ctor_set(x_2, 0, x_92);
x_93 = l_Lean_CollectFVars_main(x_69, x_2);
if (x_85 == 0)
{
lean_dec(x_70);
return x_93;
}
else
{
x_71 = x_93;
goto block_83;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_2);
lean_inc(x_69);
x_94 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_86, x_69);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_87);
x_96 = l_Lean_CollectFVars_main(x_69, x_95);
if (x_85 == 0)
{
lean_dec(x_70);
return x_96;
}
else
{
x_71 = x_96;
goto block_83;
}
}
}
else
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_69);
if (x_85 == 0)
{
lean_dec(x_70);
return x_2;
}
else
{
x_71 = x_2;
goto block_83;
}
}
}
block_83:
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_74 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_72, x_70);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_71, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_71, 0);
lean_dec(x_77);
lean_inc(x_70);
x_78 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_72, x_70);
lean_ctor_set(x_71, 0, x_78);
x_1 = x_70;
x_2 = x_71;
goto _start;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_inc(x_70);
x_80 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_72, x_70);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_73);
x_1 = x_70;
x_2 = x_81;
goto _start;
}
}
else
{
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_70);
return x_71;
}
}
}
case 8:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_113; uint8_t x_114; uint8_t x_115; lean_object* x_116; 
x_97 = lean_ctor_get(x_1, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_1, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 3);
lean_inc(x_99);
lean_dec(x_1);
x_113 = l_Lean_Expr_hasFVar(x_97);
x_114 = l_Lean_Expr_hasFVar(x_98);
x_115 = l_Lean_Expr_hasFVar(x_99);
if (x_113 == 0)
{
lean_dec(x_97);
if (x_114 == 0)
{
lean_dec(x_98);
if (x_115 == 0)
{
lean_dec(x_99);
return x_2;
}
else
{
x_100 = x_2;
goto block_112;
}
}
else
{
x_116 = x_2;
goto block_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_2, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_2, 1);
lean_inc(x_130);
x_131 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_129, x_97);
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_2);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_2, 1);
lean_dec(x_133);
x_134 = lean_ctor_get(x_2, 0);
lean_dec(x_134);
lean_inc(x_97);
x_135 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_129, x_97);
lean_ctor_set(x_2, 0, x_135);
x_136 = l_Lean_CollectFVars_main(x_97, x_2);
if (x_114 == 0)
{
lean_dec(x_98);
if (x_115 == 0)
{
lean_dec(x_99);
return x_136;
}
else
{
x_100 = x_136;
goto block_112;
}
}
else
{
x_116 = x_136;
goto block_128;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_2);
lean_inc(x_97);
x_137 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_129, x_97);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_130);
x_139 = l_Lean_CollectFVars_main(x_97, x_138);
if (x_114 == 0)
{
lean_dec(x_98);
if (x_115 == 0)
{
lean_dec(x_99);
return x_139;
}
else
{
x_100 = x_139;
goto block_112;
}
}
else
{
x_116 = x_139;
goto block_128;
}
}
}
else
{
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_97);
if (x_114 == 0)
{
lean_dec(x_98);
if (x_115 == 0)
{
lean_dec(x_99);
return x_2;
}
else
{
x_100 = x_2;
goto block_112;
}
}
else
{
x_116 = x_2;
goto block_128;
}
}
}
block_112:
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
x_103 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_101, x_99);
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_100);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_100, 1);
lean_dec(x_105);
x_106 = lean_ctor_get(x_100, 0);
lean_dec(x_106);
lean_inc(x_99);
x_107 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_101, x_99);
lean_ctor_set(x_100, 0, x_107);
x_1 = x_99;
x_2 = x_100;
goto _start;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_100);
lean_inc(x_99);
x_109 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_101, x_99);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_102);
x_1 = x_99;
x_2 = x_110;
goto _start;
}
}
else
{
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_99);
return x_100;
}
}
block_128:
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
x_119 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_117, x_98);
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_116);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_116, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_116, 0);
lean_dec(x_122);
lean_inc(x_98);
x_123 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_117, x_98);
lean_ctor_set(x_116, 0, x_123);
x_124 = l_Lean_CollectFVars_main(x_98, x_116);
if (x_115 == 0)
{
lean_dec(x_99);
return x_124;
}
else
{
x_100 = x_124;
goto block_112;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_116);
lean_inc(x_98);
x_125 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_117, x_98);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_118);
x_127 = l_Lean_CollectFVars_main(x_98, x_126);
if (x_115 == 0)
{
lean_dec(x_99);
return x_127;
}
else
{
x_100 = x_127;
goto block_112;
}
}
}
else
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_98);
if (x_115 == 0)
{
lean_dec(x_99);
return x_116;
}
else
{
x_100 = x_116;
goto block_112;
}
}
}
}
case 10:
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_1, 1);
lean_inc(x_140);
lean_dec(x_1);
x_141 = l_Lean_Expr_hasFVar(x_140);
if (x_141 == 0)
{
lean_dec(x_140);
return x_2;
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_2, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_2, 1);
lean_inc(x_143);
x_144 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_142, x_140);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_2);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_2, 1);
lean_dec(x_146);
x_147 = lean_ctor_get(x_2, 0);
lean_dec(x_147);
lean_inc(x_140);
x_148 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_142, x_140);
lean_ctor_set(x_2, 0, x_148);
x_1 = x_140;
goto _start;
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_2);
lean_inc(x_140);
x_150 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_142, x_140);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_143);
x_1 = x_140;
x_2 = x_151;
goto _start;
}
}
else
{
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
return x_2;
}
}
}
case 11:
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_1, 2);
lean_inc(x_153);
lean_dec(x_1);
x_154 = l_Lean_Expr_hasFVar(x_153);
if (x_154 == 0)
{
lean_dec(x_153);
return x_2;
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_155 = lean_ctor_get(x_2, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_2, 1);
lean_inc(x_156);
x_157 = l_Std_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_155, x_153);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_2);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_2, 1);
lean_dec(x_159);
x_160 = lean_ctor_get(x_2, 0);
lean_dec(x_160);
lean_inc(x_153);
x_161 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_155, x_153);
lean_ctor_set(x_2, 0, x_161);
x_1 = x_153;
goto _start;
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
lean_inc(x_153);
x_163 = l_Std_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_155, x_153);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_156);
x_1 = x_153;
x_2 = x_164;
goto _start;
}
}
else
{
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_153);
return x_2;
}
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_Lean_collectFVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CollectFVars_main(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_CollectFVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectFVars_State_visitedExpr___default___closed__1 = _init_l_Lean_CollectFVars_State_visitedExpr___default___closed__1();
lean_mark_persistent(l_Lean_CollectFVars_State_visitedExpr___default___closed__1);
l_Lean_CollectFVars_State_visitedExpr___default = _init_l_Lean_CollectFVars_State_visitedExpr___default();
lean_mark_persistent(l_Lean_CollectFVars_State_visitedExpr___default);
l_Lean_CollectFVars_State_fvarSet___default = _init_l_Lean_CollectFVars_State_fvarSet___default();
lean_mark_persistent(l_Lean_CollectFVars_State_fvarSet___default);
l_Lean_CollectFVars_instInhabitedState___closed__1 = _init_l_Lean_CollectFVars_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState___closed__1);
l_Lean_CollectFVars_instInhabitedState = _init_l_Lean_CollectFVars_instInhabitedState();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
