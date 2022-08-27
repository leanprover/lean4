// Lean compiler output
// Module: Lean.Compiler.LCNF.ElimDead
// Imports: Init Lean.Compiler.LCNF.Basic
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectExpr(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_HashSetImp_insert___at_Lean_Compiler_LCNF_collectExpr___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_collectExpr___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__3(size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDead(lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_collectExpr___spec__6___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead_goFunDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Expr_collectM(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashSet___at_Lean_Compiler_LCNF_Code_elimDead___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_LCNF_collectExpr___spec__5(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Compiler_LCNF_collectExpr___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSetImp_expand___at_Lean_Compiler_LCNF_collectExpr___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Compiler_LCNF_collectExpr___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_FVarId_collectM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSetImp_moveEntries___at_Lean_Compiler_LCNF_collectExpr___spec__4(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Compiler_LCNF_collectExpr___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_name_eq(x_1, x_4);
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_LCNF_collectExpr___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(x_4);
x_8 = lean_uint64_to_usize(x_7);
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
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(x_13);
x_17 = lean_uint64_to_usize(x_16);
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
LEAN_EXPORT lean_object* l_Std_HashSetImp_moveEntries___at_Lean_Compiler_LCNF_collectExpr___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at_Lean_Compiler_LCNF_collectExpr___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashSetImp_expand___at_Lean_Compiler_LCNF_collectExpr___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashSetImp_moveEntries___at_Lean_Compiler_LCNF_collectExpr___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_collectExpr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_name_eq(x_6, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_List_replace___at_Lean_Compiler_LCNF_collectExpr___spec__6(x_7, x_2, x_3);
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
x_12 = lean_name_eq(x_10, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_List_replace___at_Lean_Compiler_LCNF_collectExpr___spec__6(x_11, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Std_HashSetImp_insert___at_Lean_Compiler_LCNF_collectExpr___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
x_10 = lean_array_uget(x_5, x_9);
x_11 = l_List_elem___at_Lean_Compiler_LCNF_collectExpr___spec__2(x_2, x_10);
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
x_17 = l_Std_HashSetImp_expand___at_Lean_Compiler_LCNF_collectExpr___spec__3(x_13, x_15);
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
x_18 = l_List_replace___at_Lean_Compiler_LCNF_collectExpr___spec__6(x_10, x_2, x_2);
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
x_23 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(x_2);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_modn(x_24, x_22);
x_26 = lean_array_uget(x_21, x_25);
x_27 = l_List_elem___at_Lean_Compiler_LCNF_collectExpr___spec__2(x_2, x_26);
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
x_33 = l_Std_HashSetImp_expand___at_Lean_Compiler_LCNF_collectExpr___spec__3(x_29, x_31);
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
x_35 = l_List_replace___at_Lean_Compiler_LCNF_collectExpr___spec__6(x_26, x_2, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Std_HashSetImp_insert___at_Lean_Compiler_LCNF_collectExpr___spec__1(x_1, x_3);
return x_4;
}
case 5:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Compiler_LCNF_collectExpr(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
case 6:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
case 8:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_Compiler_LCNF_collectExpr(x_1, x_11);
x_1 = x_13;
x_2 = x_12;
goto _start;
}
case 10:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
case 11:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_dec(x_2);
x_2 = x_17;
goto _start;
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Compiler_LCNF_collectExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_Compiler_LCNF_collectExpr___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_collectExpr___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lean_Compiler_LCNF_collectExpr___spec__6(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Expr_collectM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Compiler_LCNF_collectExpr(x_2, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_FVarId_collectM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Std_HashSetImp_insert___at_Lean_Compiler_LCNF_collectExpr___spec__1(x_2, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead_goFunDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
x_9 = l_List_elem___at_Lean_Compiler_LCNF_collectExpr___spec__2(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Expr_collectM(x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 2);
x_12 = l_Lean_Compiler_LCNF_Code_elimDead_go(x_11, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_ctor_set(x_7, 2, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_9, x_2, x_7);
x_2 = x_16;
x_3 = x_17;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_7, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_22 = l_Lean_Compiler_LCNF_Code_elimDead_go(x_21, x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_23);
x_26 = 1;
x_27 = lean_usize_add(x_2, x_26);
x_28 = lean_array_uset(x_9, x_2, x_25);
x_2 = x_27;
x_3 = x_28;
x_4 = x_24;
goto _start;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = l_Lean_Compiler_LCNF_Code_elimDead_go(x_31, x_4);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set(x_7, 0, x_33);
x_35 = 1;
x_36 = lean_usize_add(x_2, x_35);
x_37 = lean_array_uset(x_9, x_2, x_7);
x_2 = x_36;
x_3 = x_37;
x_4 = x_34;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
lean_dec(x_7);
x_40 = l_Lean_Compiler_LCNF_Code_elimDead_go(x_39, x_4);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = 1;
x_45 = lean_usize_add(x_2, x_44);
x_46 = lean_array_uset(x_9, x_2, x_43);
x_2 = x_45;
x_3 = x_46;
x_4 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Compiler_LCNF_Code_elimDead_go(x_5, x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_free_object(x_1);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
x_13 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Expr_collectM(x_12, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_4, 3);
lean_inc(x_15);
x_16 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Expr_collectM(x_15, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_1, 1, x_8);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
x_24 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(x_22, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_free_object(x_1);
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_4, 2);
lean_inc(x_26);
x_27 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Expr_collectM(x_26, x_22);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_4, 3);
lean_inc(x_29);
x_30 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Expr_collectM(x_29, x_28);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_21);
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_1);
x_36 = l_Lean_Compiler_LCNF_Code_elimDead_go(x_35, x_2);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(x_38, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_34);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_39);
x_43 = lean_ctor_get(x_34, 2);
lean_inc(x_43);
x_44 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Expr_collectM(x_43, x_38);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_34, 3);
lean_inc(x_46);
x_47 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Expr_collectM(x_46, x_45);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_37);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
case 1:
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_1);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_1, 0);
x_54 = lean_ctor_get(x_1, 1);
x_55 = l_Lean_Compiler_LCNF_Code_elimDead_go(x_54, x_2);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(x_58, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_free_object(x_1);
lean_dec(x_53);
return x_55;
}
else
{
lean_ctor_set(x_1, 1, x_57);
lean_ctor_set(x_55, 0, x_1);
return x_55;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
x_64 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(x_62, x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_free_object(x_1);
lean_dec(x_53);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; 
lean_ctor_set(x_1, 1, x_61);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_67 = lean_ctor_get(x_1, 0);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_1);
x_69 = l_Lean_Compiler_LCNF_Code_elimDead_go(x_68, x_2);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
x_74 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(x_71, x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_67);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_70);
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
return x_77;
}
}
}
case 2:
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_1);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_1, 0);
x_80 = lean_ctor_get(x_1, 1);
x_81 = l_Lean_Compiler_LCNF_Code_elimDead_go(x_80, x_2);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
x_86 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(x_84, x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_free_object(x_1);
lean_dec(x_79);
return x_81;
}
else
{
lean_ctor_set(x_1, 1, x_83);
lean_ctor_set(x_81, 0, x_1);
return x_81;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_81, 0);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_81);
x_89 = lean_ctor_get(x_79, 0);
lean_inc(x_89);
x_90 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(x_88, x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
lean_free_object(x_1);
lean_dec(x_79);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
else
{
lean_object* x_92; 
lean_ctor_set(x_1, 1, x_87);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_93 = lean_ctor_get(x_1, 0);
x_94 = lean_ctor_get(x_1, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_1);
x_95 = l_Lean_Compiler_LCNF_Code_elimDead_go(x_94, x_2);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
x_100 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(x_97, x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_93);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_93);
lean_ctor_set(x_102, 1, x_96);
if (lean_is_scalar(x_98)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_98;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_97);
return x_103;
}
}
}
case 3:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_1, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_1, 1);
lean_inc(x_105);
x_106 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_FVarId_collectM(x_104, x_2);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_106, 1);
x_109 = lean_ctor_get(x_106, 0);
lean_dec(x_109);
x_110 = lean_array_get_size(x_105);
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_nat_dec_lt(x_111, x_110);
if (x_112 == 0)
{
lean_dec(x_110);
lean_dec(x_105);
lean_ctor_set(x_106, 0, x_1);
return x_106;
}
else
{
uint8_t x_113; 
x_113 = lean_nat_dec_le(x_110, x_110);
if (x_113 == 0)
{
lean_dec(x_110);
lean_dec(x_105);
lean_ctor_set(x_106, 0, x_1);
return x_106;
}
else
{
size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_free_object(x_106);
x_114 = 0;
x_115 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_116 = lean_box(0);
x_117 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__2(x_105, x_114, x_115, x_116, x_108);
lean_dec(x_105);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_117, 0);
lean_dec(x_119);
lean_ctor_set(x_117, 0, x_1);
return x_117;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_1);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = lean_ctor_get(x_106, 1);
lean_inc(x_122);
lean_dec(x_106);
x_123 = lean_array_get_size(x_105);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_nat_dec_lt(x_124, x_123);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec(x_123);
lean_dec(x_105);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
else
{
uint8_t x_127; 
x_127 = lean_nat_dec_le(x_123, x_123);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_123);
lean_dec(x_105);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_122);
return x_128;
}
else
{
size_t x_129; size_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = 0;
x_130 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_131 = lean_box(0);
x_132 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__2(x_105, x_129, x_130, x_131, x_122);
lean_dec(x_105);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
}
case 4:
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_1);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_1, 0);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; size_t x_142; size_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_139 = lean_ctor_get(x_137, 2);
x_140 = lean_ctor_get(x_137, 3);
x_141 = lean_array_get_size(x_140);
x_142 = lean_usize_of_nat(x_141);
lean_dec(x_141);
x_143 = 0;
x_144 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__3(x_142, x_143, x_140, x_2);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_139);
x_147 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_FVarId_collectM(x_139, x_146);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_147, 0);
lean_dec(x_149);
lean_ctor_set(x_137, 3, x_145);
lean_ctor_set(x_147, 0, x_1);
return x_147;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
lean_ctor_set(x_137, 3, x_145);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_1);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_152 = lean_ctor_get(x_137, 0);
x_153 = lean_ctor_get(x_137, 1);
x_154 = lean_ctor_get(x_137, 2);
x_155 = lean_ctor_get(x_137, 3);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_137);
x_156 = lean_array_get_size(x_155);
x_157 = lean_usize_of_nat(x_156);
lean_dec(x_156);
x_158 = 0;
x_159 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__3(x_157, x_158, x_155, x_2);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_154);
x_162 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_FVarId_collectM(x_154, x_161);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
x_165 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_165, 0, x_152);
lean_ctor_set(x_165, 1, x_153);
lean_ctor_set(x_165, 2, x_154);
lean_ctor_set(x_165, 3, x_160);
lean_ctor_set(x_1, 0, x_165);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_167 = lean_ctor_get(x_1, 0);
lean_inc(x_167);
lean_dec(x_1);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_167, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 lean_ctor_release(x_167, 3);
 x_172 = x_167;
} else {
 lean_dec_ref(x_167);
 x_172 = lean_box(0);
}
x_173 = lean_array_get_size(x_171);
x_174 = lean_usize_of_nat(x_173);
lean_dec(x_173);
x_175 = 0;
x_176 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__3(x_174, x_175, x_171, x_2);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
lean_inc(x_170);
x_179 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_FVarId_collectM(x_170, x_178);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_182 = lean_alloc_ctor(0, 4, 0);
} else {
 x_182 = x_172;
}
lean_ctor_set(x_182, 0, x_168);
lean_ctor_set(x_182, 1, x_169);
lean_ctor_set(x_182, 2, x_170);
lean_ctor_set(x_182, 3, x_177);
x_183 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_183, 0, x_182);
if (lean_is_scalar(x_181)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_181;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_180);
return x_184;
}
}
case 5:
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_1, 0);
lean_inc(x_185);
x_186 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_FVarId_collectM(x_185, x_2);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_186, 0);
lean_dec(x_188);
lean_ctor_set(x_186, 0, x_1);
return x_186;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
default: 
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_1);
lean_ctor_set(x_191, 1, x_2);
return x_191;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__2(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Code_elimDead_go___spec__3(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashSet___at_Lean_Compiler_LCNF_Code_elimDead___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_Std_mkHashSetImp___rarg(x_2);
x_4 = l_Lean_Compiler_LCNF_Code_elimDead_go(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDead(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = l_Lean_Compiler_LCNF_Code_elimDead(x_3);
lean_ctor_set(x_1, 4, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_Code_elimDead(x_9);
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_10);
return x_11;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
