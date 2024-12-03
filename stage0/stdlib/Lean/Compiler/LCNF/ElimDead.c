// Lean compiler output
// Module: Lean.Compiler.LCNF.ElimDead
// Imports: Lean.Compiler.LCNF.CompilerM
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_elimDead___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_elimDead___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instFVarIdHashSetInhabited;
static lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1(lean_object*, size_t, size_t, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_elimDead___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_4);
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
x_26 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_22);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__4(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instFVarIdHashSetInhabited;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ElimDead", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.collectLocalDeclsType.go", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1;
x_2 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2;
x_3 = lean_unsigned_to_nat(26u);
x_4 = lean_unsigned_to_nat(41u);
x_5 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_4);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_4, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_box(0);
lean_inc(x_4);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_20);
x_26 = lean_array_uset(x_6, x_19, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_23, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_26);
lean_ctor_set(x_1, 1, x_33);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_dec(x_20);
return x_1;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint8_t x_51; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_1);
x_37 = lean_array_get_size(x_36);
x_38 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_34);
x_39 = 32;
x_40 = lean_uint64_shift_right(x_38, x_39);
x_41 = lean_uint64_xor(x_38, x_40);
x_42 = 16;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_47 = 1;
x_48 = lean_usize_sub(x_46, x_47);
x_49 = lean_usize_land(x_45, x_48);
x_50 = lean_array_uget(x_36, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_34, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_35, x_52);
lean_dec(x_35);
x_54 = lean_box(0);
lean_inc(x_34);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_34);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_50);
x_56 = lean_array_uset(x_36, x_49, x_55);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_53, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_56);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_56);
return x_65;
}
}
else
{
lean_object* x_66; 
lean_dec(x_50);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_35);
lean_ctor_set(x_66, 1, x_36);
return x_66;
}
}
}
case 5:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_ctor_get(x_2, 1);
x_69 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go(x_1, x_68);
x_1 = x_69;
x_2 = x_67;
goto _start;
}
case 6:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_2, 2);
x_2 = x_71;
goto _start;
}
case 8:
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_73 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4;
x_74 = l_panic___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__5(x_73);
return x_74;
}
case 10:
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_1);
x_75 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4;
x_76 = l_panic___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__5(x_75);
return x_76;
}
case 11:
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_1);
x_77 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4;
x_78 = l_panic___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__5(x_77);
return x_78;
}
default: 
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsType(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_4);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_4, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_box(0);
lean_inc(x_4);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_20);
x_26 = lean_array_uset(x_6, x_19, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_23, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_26);
lean_ctor_set(x_1, 1, x_33);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_dec(x_20);
return x_1;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint8_t x_51; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_1);
x_37 = lean_array_get_size(x_36);
x_38 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_34);
x_39 = 32;
x_40 = lean_uint64_shift_right(x_38, x_39);
x_41 = lean_uint64_xor(x_38, x_40);
x_42 = 16;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_47 = 1;
x_48 = lean_usize_sub(x_46, x_47);
x_49 = lean_usize_land(x_45, x_48);
x_50 = lean_array_uget(x_36, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_34, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_35, x_52);
lean_dec(x_35);
x_54 = lean_box(0);
lean_inc(x_34);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_34);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_50);
x_56 = lean_array_uset(x_36, x_49, x_55);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_53, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_56);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_56);
return x_65;
}
}
else
{
lean_object* x_66; 
lean_dec(x_50);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_35);
lean_ctor_set(x_66, 1, x_36);
return x_66;
}
}
}
default: 
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_2, 0);
x_68 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go(x_1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_array_get_size(x_9);
x_11 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_4);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_9, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_4, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_8, x_25);
lean_dec(x_8);
x_27 = lean_box(0);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 2, x_23);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_2, 0, x_4);
x_28 = lean_array_uset(x_9, x_22, x_2);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_nat_mul(x_26, x_29);
x_31 = lean_unsigned_to_nat(3u);
x_32 = lean_nat_div(x_30, x_31);
lean_dec(x_30);
x_33 = lean_array_get_size(x_28);
x_34 = lean_nat_dec_le(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_28);
lean_ctor_set(x_1, 1, x_35);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
}
else
{
lean_dec(x_23);
lean_free_object(x_2);
lean_dec(x_4);
return x_1;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_38 = lean_array_get_size(x_37);
x_39 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_4);
x_40 = 32;
x_41 = lean_uint64_shift_right(x_39, x_40);
x_42 = lean_uint64_xor(x_39, x_41);
x_43 = 16;
x_44 = lean_uint64_shift_right(x_42, x_43);
x_45 = lean_uint64_xor(x_42, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_48 = 1;
x_49 = lean_usize_sub(x_47, x_48);
x_50 = lean_usize_land(x_46, x_49);
x_51 = lean_array_uget(x_37, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_4, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_36, x_53);
lean_dec(x_36);
x_55 = lean_box(0);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 2, x_51);
lean_ctor_set(x_2, 1, x_55);
lean_ctor_set(x_2, 0, x_4);
x_56 = lean_array_uset(x_37, x_50, x_2);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_56);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_56);
return x_65;
}
}
else
{
lean_object* x_66; 
lean_dec(x_51);
lean_free_object(x_2);
lean_dec(x_4);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_36);
lean_ctor_set(x_66, 1, x_37);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; size_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; lean_object* x_84; uint8_t x_85; 
x_67 = lean_ctor_get(x_2, 2);
lean_inc(x_67);
lean_dec(x_2);
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_70 = x_1;
} else {
 lean_dec_ref(x_1);
 x_70 = lean_box(0);
}
x_71 = lean_array_get_size(x_69);
x_72 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_67);
x_73 = 32;
x_74 = lean_uint64_shift_right(x_72, x_73);
x_75 = lean_uint64_xor(x_72, x_74);
x_76 = 16;
x_77 = lean_uint64_shift_right(x_75, x_76);
x_78 = lean_uint64_xor(x_75, x_77);
x_79 = lean_uint64_to_usize(x_78);
x_80 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_81 = 1;
x_82 = lean_usize_sub(x_80, x_81);
x_83 = lean_usize_land(x_79, x_82);
x_84 = lean_array_uget(x_69, x_83);
x_85 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_67, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_68, x_86);
lean_dec(x_68);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_67);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_84);
x_90 = lean_array_uset(x_69, x_83, x_89);
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_nat_mul(x_87, x_91);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_nat_div(x_92, x_93);
lean_dec(x_92);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_le(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_90);
if (lean_is_scalar(x_70)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_70;
}
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
else
{
lean_object* x_99; 
if (lean_is_scalar(x_70)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_70;
}
lean_ctor_set(x_99, 0, x_87);
lean_ctor_set(x_99, 1, x_90);
return x_99;
}
}
else
{
lean_object* x_100; 
lean_dec(x_84);
lean_dec(x_67);
if (lean_is_scalar(x_70)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_70;
}
lean_ctor_set(x_100, 0, x_68);
lean_ctor_set(x_100, 1, x_69);
return x_100;
}
}
}
case 3:
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_2, 2);
lean_inc(x_101);
lean_dec(x_2);
x_102 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_101);
lean_dec(x_101);
return x_102;
}
case 4:
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_2, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_1);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; uint8_t x_122; 
x_106 = lean_ctor_get(x_1, 0);
x_107 = lean_ctor_get(x_1, 1);
x_108 = lean_array_get_size(x_107);
x_109 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_103);
x_110 = 32;
x_111 = lean_uint64_shift_right(x_109, x_110);
x_112 = lean_uint64_xor(x_109, x_111);
x_113 = 16;
x_114 = lean_uint64_shift_right(x_112, x_113);
x_115 = lean_uint64_xor(x_112, x_114);
x_116 = lean_uint64_to_usize(x_115);
x_117 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_118 = 1;
x_119 = lean_usize_sub(x_117, x_118);
x_120 = lean_usize_land(x_116, x_119);
x_121 = lean_array_uget(x_107, x_120);
x_122 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_103, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_add(x_106, x_123);
lean_dec(x_106);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_103);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_121);
x_127 = lean_array_uset(x_107, x_120, x_126);
x_128 = lean_unsigned_to_nat(4u);
x_129 = lean_nat_mul(x_124, x_128);
x_130 = lean_unsigned_to_nat(3u);
x_131 = lean_nat_div(x_129, x_130);
lean_dec(x_129);
x_132 = lean_array_get_size(x_127);
x_133 = lean_nat_dec_le(x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_127);
lean_ctor_set(x_1, 1, x_134);
lean_ctor_set(x_1, 0, x_124);
x_135 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_104);
lean_dec(x_104);
return x_135;
}
else
{
lean_object* x_136; 
lean_ctor_set(x_1, 1, x_127);
lean_ctor_set(x_1, 0, x_124);
x_136 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_104);
lean_dec(x_104);
return x_136;
}
}
else
{
lean_object* x_137; 
lean_dec(x_121);
lean_dec(x_103);
x_137 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_104);
lean_dec(x_104);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint64_t x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; uint64_t x_145; uint64_t x_146; uint64_t x_147; size_t x_148; size_t x_149; size_t x_150; size_t x_151; size_t x_152; lean_object* x_153; uint8_t x_154; 
x_138 = lean_ctor_get(x_1, 0);
x_139 = lean_ctor_get(x_1, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_1);
x_140 = lean_array_get_size(x_139);
x_141 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_103);
x_142 = 32;
x_143 = lean_uint64_shift_right(x_141, x_142);
x_144 = lean_uint64_xor(x_141, x_143);
x_145 = 16;
x_146 = lean_uint64_shift_right(x_144, x_145);
x_147 = lean_uint64_xor(x_144, x_146);
x_148 = lean_uint64_to_usize(x_147);
x_149 = lean_usize_of_nat(x_140);
lean_dec(x_140);
x_150 = 1;
x_151 = lean_usize_sub(x_149, x_150);
x_152 = lean_usize_land(x_148, x_151);
x_153 = lean_array_uget(x_139, x_152);
x_154 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_103, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_nat_add(x_138, x_155);
lean_dec(x_138);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_103);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_153);
x_159 = lean_array_uset(x_139, x_152, x_158);
x_160 = lean_unsigned_to_nat(4u);
x_161 = lean_nat_mul(x_156, x_160);
x_162 = lean_unsigned_to_nat(3u);
x_163 = lean_nat_div(x_161, x_162);
lean_dec(x_161);
x_164 = lean_array_get_size(x_159);
x_165 = lean_nat_dec_le(x_163, x_164);
lean_dec(x_164);
lean_dec(x_163);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_159);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_156);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_167, x_104);
lean_dec(x_104);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_156);
lean_ctor_set(x_169, 1, x_159);
x_170 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_169, x_104);
lean_dec(x_104);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_153);
lean_dec(x_103);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_138);
lean_ctor_set(x_171, 1, x_139);
x_172 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_171, x_104);
lean_dec(x_104);
return x_172;
}
}
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_9, x_1);
x_12 = lean_st_ref_set(x_2, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_9, x_1);
x_12 = lean_st_ref_set(x_2, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_array_get_size(x_13);
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_16 = 32;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = 16;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_24 = 1;
x_25 = lean_usize_sub(x_23, x_24);
x_26 = lean_usize_land(x_22, x_25);
x_27 = lean_array_uget(x_13, x_26);
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_1, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_12, x_29);
lean_dec(x_12);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_27);
x_33 = lean_array_uset(x_13, x_26, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_30, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_33);
lean_ctor_set(x_9, 1, x_40);
lean_ctor_set(x_9, 0, x_30);
x_41 = lean_st_ref_set(x_2, x_9, x_10);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_31);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_31);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_ctor_set(x_9, 1, x_33);
lean_ctor_set(x_9, 0, x_30);
x_46 = lean_st_ref_set(x_2, x_9, x_10);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_31);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_31);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_27);
lean_dec(x_1);
x_51 = lean_st_ref_set(x_2, x_9, x_10);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; uint8_t x_74; 
x_58 = lean_ctor_get(x_9, 0);
x_59 = lean_ctor_get(x_9, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_9);
x_60 = lean_array_get_size(x_59);
x_61 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_62 = 32;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = 16;
x_66 = lean_uint64_shift_right(x_64, x_65);
x_67 = lean_uint64_xor(x_64, x_66);
x_68 = lean_uint64_to_usize(x_67);
x_69 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_70 = 1;
x_71 = lean_usize_sub(x_69, x_70);
x_72 = lean_usize_land(x_68, x_71);
x_73 = lean_array_uget(x_59, x_72);
x_74 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_1, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_58, x_75);
lean_dec(x_58);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_73);
x_79 = lean_array_uset(x_59, x_72, x_78);
x_80 = lean_unsigned_to_nat(4u);
x_81 = lean_nat_mul(x_76, x_80);
x_82 = lean_unsigned_to_nat(3u);
x_83 = lean_nat_div(x_81, x_82);
lean_dec(x_81);
x_84 = lean_array_get_size(x_79);
x_85 = lean_nat_dec_le(x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_79);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_st_ref_set(x_2, x_87, x_10);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_79);
x_93 = lean_st_ref_set(x_2, x_92, x_10);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_77);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_73);
lean_dec(x_1);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_58);
lean_ctor_set(x_97, 1, x_59);
x_98 = lean_st_ref_set(x_2, x_97, x_10);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_12, x_13, x_10, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_st_ref_take(x_5, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_14, x_12);
lean_dec(x_12);
x_17 = lean_st_ref_set(x_5, x_16, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_box(0);
x_2 = x_20;
x_4 = x_21;
x_10 = x_18;
goto _start;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_14 = lean_apply_7(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_array_fset(x_3, x_2, x_15);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_22;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
x_9 = x_16;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__3(x_2, x_9, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
x_9 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ElimDead_elimDead___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_2, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_array_get_size(x_17);
x_19 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_16);
x_20 = 32;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = 16;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = 1;
x_29 = lean_usize_sub(x_27, x_28);
x_30 = lean_usize_land(x_26, x_29);
x_31 = lean_array_uget(x_17, x_30);
lean_dec(x_17);
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_16, x_31);
lean_dec(x_31);
lean_dec(x_16);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_33 = l_Lean_Compiler_LCNF_eraseLetDecl(x_8, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_11);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = lean_ctor_get(x_8, 3);
lean_inc(x_38);
x_39 = lean_st_ref_take(x_2, x_15);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_40, x_38);
x_43 = lean_st_ref_set(x_2, x_42, x_41);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; size_t x_46; size_t x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_47 = lean_ptr_addr(x_11);
x_48 = lean_usize_dec_eq(x_46, x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_1);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_1, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_43, 0, x_1);
return x_43;
}
else
{
lean_object* x_52; 
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_8);
lean_ctor_set(x_52, 1, x_11);
lean_ctor_set(x_43, 0, x_52);
return x_43;
}
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_ctor_set(x_43, 0, x_1);
return x_43;
}
}
else
{
lean_object* x_53; size_t x_54; size_t x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_54 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_55 = lean_ptr_addr(x_11);
x_56 = lean_usize_dec_eq(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_57 = x_1;
} else {
 lean_dec_ref(x_1);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_11);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
return x_59;
}
else
{
lean_object* x_60; 
lean_dec(x_11);
lean_dec(x_8);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_10);
if (x_61 == 0)
{
return x_10;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_10, 0);
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_10);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
case 1:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 1);
lean_inc(x_66);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_66);
x_67 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_66, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; size_t x_83; size_t x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; uint8_t x_89; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_get(x_2, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_array_get_size(x_74);
x_76 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_73);
x_77 = 32;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = 16;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = lean_uint64_to_usize(x_82);
x_84 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_85 = 1;
x_86 = lean_usize_sub(x_84, x_85);
x_87 = lean_usize_land(x_83, x_86);
x_88 = lean_array_uget(x_74, x_87);
lean_dec(x_74);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_73, x_88);
lean_dec(x_88);
lean_dec(x_73);
if (x_89 == 0)
{
uint8_t x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_66);
lean_dec(x_2);
lean_dec(x_1);
x_90 = 1;
x_91 = l_Lean_Compiler_LCNF_eraseFunDecl(x_65, x_90, x_3, x_4, x_5, x_6, x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_65);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
lean_ctor_set(x_91, 0, x_68);
return x_91;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_68);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
else
{
lean_object* x_96; 
lean_inc(x_65);
x_96 = l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(x_65, x_2, x_3, x_4, x_5, x_6, x_72);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; size_t x_99; size_t x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_100 = lean_ptr_addr(x_68);
x_101 = lean_usize_dec_eq(x_99, x_100);
if (x_101 == 0)
{
uint8_t x_102; 
lean_dec(x_65);
x_102 = !lean_is_exclusive(x_1);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_1, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_1, 0);
lean_dec(x_104);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_98);
lean_ctor_set(x_96, 0, x_1);
return x_96;
}
else
{
lean_object* x_105; 
lean_dec(x_1);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_68);
lean_ctor_set(x_96, 0, x_105);
return x_96;
}
}
else
{
size_t x_106; size_t x_107; uint8_t x_108; 
x_106 = lean_ptr_addr(x_65);
lean_dec(x_65);
x_107 = lean_ptr_addr(x_98);
x_108 = lean_usize_dec_eq(x_106, x_107);
if (x_108 == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_1);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_1, 1);
lean_dec(x_110);
x_111 = lean_ctor_get(x_1, 0);
lean_dec(x_111);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_98);
lean_ctor_set(x_96, 0, x_1);
return x_96;
}
else
{
lean_object* x_112; 
lean_dec(x_1);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_98);
lean_ctor_set(x_112, 1, x_68);
lean_ctor_set(x_96, 0, x_112);
return x_96;
}
}
else
{
lean_dec(x_98);
lean_dec(x_68);
lean_ctor_set(x_96, 0, x_1);
return x_96;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; size_t x_115; size_t x_116; uint8_t x_117; 
x_113 = lean_ctor_get(x_96, 0);
x_114 = lean_ctor_get(x_96, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_96);
x_115 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_116 = lean_ptr_addr(x_68);
x_117 = lean_usize_dec_eq(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_65);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_118 = x_1;
} else {
 lean_dec_ref(x_1);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_113);
lean_ctor_set(x_119, 1, x_68);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_114);
return x_120;
}
else
{
size_t x_121; size_t x_122; uint8_t x_123; 
x_121 = lean_ptr_addr(x_65);
lean_dec(x_65);
x_122 = lean_ptr_addr(x_113);
x_123 = lean_usize_dec_eq(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_124 = x_1;
} else {
 lean_dec_ref(x_1);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_113);
lean_ctor_set(x_125, 1, x_68);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_114);
return x_126;
}
else
{
lean_object* x_127; 
lean_dec(x_113);
lean_dec(x_68);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_114);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_96);
if (x_128 == 0)
{
return x_96;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_96, 0);
x_130 = lean_ctor_get(x_96, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_96);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_67);
if (x_132 == 0)
{
return x_67;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_67, 0);
x_134 = lean_ctor_get(x_67, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_67);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
case 2:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_1, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_1, 1);
lean_inc(x_137);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_137);
x_138 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_137, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; uint64_t x_151; uint64_t x_152; uint64_t x_153; size_t x_154; size_t x_155; size_t x_156; size_t x_157; size_t x_158; lean_object* x_159; uint8_t x_160; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_st_ref_get(x_2, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_136, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_array_get_size(x_145);
x_147 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_144);
x_148 = 32;
x_149 = lean_uint64_shift_right(x_147, x_148);
x_150 = lean_uint64_xor(x_147, x_149);
x_151 = 16;
x_152 = lean_uint64_shift_right(x_150, x_151);
x_153 = lean_uint64_xor(x_150, x_152);
x_154 = lean_uint64_to_usize(x_153);
x_155 = lean_usize_of_nat(x_146);
lean_dec(x_146);
x_156 = 1;
x_157 = lean_usize_sub(x_155, x_156);
x_158 = lean_usize_land(x_154, x_157);
x_159 = lean_array_uget(x_145, x_158);
lean_dec(x_145);
x_160 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_144, x_159);
lean_dec(x_159);
lean_dec(x_144);
if (x_160 == 0)
{
uint8_t x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_137);
lean_dec(x_2);
lean_dec(x_1);
x_161 = 1;
x_162 = l_Lean_Compiler_LCNF_eraseFunDecl(x_136, x_161, x_3, x_4, x_5, x_6, x_143);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_136);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_162, 0);
lean_dec(x_164);
lean_ctor_set(x_162, 0, x_139);
return x_162;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_139);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_inc(x_136);
x_167 = l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(x_136, x_2, x_3, x_4, x_5, x_6, x_143);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; size_t x_170; size_t x_171; uint8_t x_172; 
x_169 = lean_ctor_get(x_167, 0);
x_170 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_171 = lean_ptr_addr(x_139);
x_172 = lean_usize_dec_eq(x_170, x_171);
if (x_172 == 0)
{
uint8_t x_173; 
lean_dec(x_136);
x_173 = !lean_is_exclusive(x_1);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_1, 1);
lean_dec(x_174);
x_175 = lean_ctor_get(x_1, 0);
lean_dec(x_175);
lean_ctor_set(x_1, 1, x_139);
lean_ctor_set(x_1, 0, x_169);
lean_ctor_set(x_167, 0, x_1);
return x_167;
}
else
{
lean_object* x_176; 
lean_dec(x_1);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_169);
lean_ctor_set(x_176, 1, x_139);
lean_ctor_set(x_167, 0, x_176);
return x_167;
}
}
else
{
size_t x_177; size_t x_178; uint8_t x_179; 
x_177 = lean_ptr_addr(x_136);
lean_dec(x_136);
x_178 = lean_ptr_addr(x_169);
x_179 = lean_usize_dec_eq(x_177, x_178);
if (x_179 == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_1);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_1, 1);
lean_dec(x_181);
x_182 = lean_ctor_get(x_1, 0);
lean_dec(x_182);
lean_ctor_set(x_1, 1, x_139);
lean_ctor_set(x_1, 0, x_169);
lean_ctor_set(x_167, 0, x_1);
return x_167;
}
else
{
lean_object* x_183; 
lean_dec(x_1);
x_183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_183, 0, x_169);
lean_ctor_set(x_183, 1, x_139);
lean_ctor_set(x_167, 0, x_183);
return x_167;
}
}
else
{
lean_dec(x_169);
lean_dec(x_139);
lean_ctor_set(x_167, 0, x_1);
return x_167;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; size_t x_186; size_t x_187; uint8_t x_188; 
x_184 = lean_ctor_get(x_167, 0);
x_185 = lean_ctor_get(x_167, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_167);
x_186 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_187 = lean_ptr_addr(x_139);
x_188 = lean_usize_dec_eq(x_186, x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_136);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_189 = x_1;
} else {
 lean_dec_ref(x_1);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(2, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_184);
lean_ctor_set(x_190, 1, x_139);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_185);
return x_191;
}
else
{
size_t x_192; size_t x_193; uint8_t x_194; 
x_192 = lean_ptr_addr(x_136);
lean_dec(x_136);
x_193 = lean_ptr_addr(x_184);
x_194 = lean_usize_dec_eq(x_192, x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_195 = x_1;
} else {
 lean_dec_ref(x_1);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(2, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_184);
lean_ctor_set(x_196, 1, x_139);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_185);
return x_197;
}
else
{
lean_object* x_198; 
lean_dec(x_184);
lean_dec(x_139);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_1);
lean_ctor_set(x_198, 1, x_185);
return x_198;
}
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_167);
if (x_199 == 0)
{
return x_167;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_167, 0);
x_201 = lean_ctor_get(x_167, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_167);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_138);
if (x_203 == 0)
{
return x_138;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_138, 0);
x_205 = lean_ctor_get(x_138, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_138);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
case 3:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_207 = lean_ctor_get(x_1, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_1, 1);
lean_inc(x_208);
x_225 = lean_st_ref_take(x_2, x_7);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = !lean_is_exclusive(x_226);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; uint64_t x_238; size_t x_239; size_t x_240; size_t x_241; size_t x_242; size_t x_243; lean_object* x_244; uint8_t x_245; 
x_229 = lean_ctor_get(x_226, 0);
x_230 = lean_ctor_get(x_226, 1);
x_231 = lean_array_get_size(x_230);
x_232 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_207);
x_233 = 32;
x_234 = lean_uint64_shift_right(x_232, x_233);
x_235 = lean_uint64_xor(x_232, x_234);
x_236 = 16;
x_237 = lean_uint64_shift_right(x_235, x_236);
x_238 = lean_uint64_xor(x_235, x_237);
x_239 = lean_uint64_to_usize(x_238);
x_240 = lean_usize_of_nat(x_231);
lean_dec(x_231);
x_241 = 1;
x_242 = lean_usize_sub(x_240, x_241);
x_243 = lean_usize_land(x_239, x_242);
x_244 = lean_array_uget(x_230, x_243);
x_245 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_207, x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_246 = lean_unsigned_to_nat(1u);
x_247 = lean_nat_add(x_229, x_246);
lean_dec(x_229);
x_248 = lean_box(0);
x_249 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_249, 0, x_207);
lean_ctor_set(x_249, 1, x_248);
lean_ctor_set(x_249, 2, x_244);
x_250 = lean_array_uset(x_230, x_243, x_249);
x_251 = lean_unsigned_to_nat(4u);
x_252 = lean_nat_mul(x_247, x_251);
x_253 = lean_unsigned_to_nat(3u);
x_254 = lean_nat_div(x_252, x_253);
lean_dec(x_252);
x_255 = lean_array_get_size(x_250);
x_256 = lean_nat_dec_le(x_254, x_255);
lean_dec(x_255);
lean_dec(x_254);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_250);
lean_ctor_set(x_226, 1, x_257);
lean_ctor_set(x_226, 0, x_247);
x_258 = lean_st_ref_set(x_2, x_226, x_227);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
x_209 = x_259;
goto block_224;
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_ctor_set(x_226, 1, x_250);
lean_ctor_set(x_226, 0, x_247);
x_260 = lean_st_ref_set(x_2, x_226, x_227);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_209 = x_261;
goto block_224;
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_244);
lean_dec(x_207);
x_262 = lean_st_ref_set(x_2, x_226, x_227);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_209 = x_263;
goto block_224;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; uint64_t x_267; uint64_t x_268; uint64_t x_269; uint64_t x_270; uint64_t x_271; uint64_t x_272; uint64_t x_273; size_t x_274; size_t x_275; size_t x_276; size_t x_277; size_t x_278; lean_object* x_279; uint8_t x_280; 
x_264 = lean_ctor_get(x_226, 0);
x_265 = lean_ctor_get(x_226, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_226);
x_266 = lean_array_get_size(x_265);
x_267 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_207);
x_268 = 32;
x_269 = lean_uint64_shift_right(x_267, x_268);
x_270 = lean_uint64_xor(x_267, x_269);
x_271 = 16;
x_272 = lean_uint64_shift_right(x_270, x_271);
x_273 = lean_uint64_xor(x_270, x_272);
x_274 = lean_uint64_to_usize(x_273);
x_275 = lean_usize_of_nat(x_266);
lean_dec(x_266);
x_276 = 1;
x_277 = lean_usize_sub(x_275, x_276);
x_278 = lean_usize_land(x_274, x_277);
x_279 = lean_array_uget(x_265, x_278);
x_280 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_207, x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_281 = lean_unsigned_to_nat(1u);
x_282 = lean_nat_add(x_264, x_281);
lean_dec(x_264);
x_283 = lean_box(0);
x_284 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_284, 0, x_207);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set(x_284, 2, x_279);
x_285 = lean_array_uset(x_265, x_278, x_284);
x_286 = lean_unsigned_to_nat(4u);
x_287 = lean_nat_mul(x_282, x_286);
x_288 = lean_unsigned_to_nat(3u);
x_289 = lean_nat_div(x_287, x_288);
lean_dec(x_287);
x_290 = lean_array_get_size(x_285);
x_291 = lean_nat_dec_le(x_289, x_290);
lean_dec(x_290);
lean_dec(x_289);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_285);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_282);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_st_ref_set(x_2, x_293, x_227);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_209 = x_295;
goto block_224;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_282);
lean_ctor_set(x_296, 1, x_285);
x_297 = lean_st_ref_set(x_2, x_296, x_227);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
lean_dec(x_297);
x_209 = x_298;
goto block_224;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_279);
lean_dec(x_207);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_264);
lean_ctor_set(x_299, 1, x_265);
x_300 = lean_st_ref_set(x_2, x_299, x_227);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
lean_dec(x_300);
x_209 = x_301;
goto block_224;
}
}
block_224:
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = lean_array_get_size(x_208);
x_211 = lean_unsigned_to_nat(0u);
x_212 = lean_nat_dec_lt(x_211, x_210);
if (x_212 == 0)
{
lean_object* x_213; 
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_1);
lean_ctor_set(x_213, 1, x_209);
return x_213;
}
else
{
uint8_t x_214; 
x_214 = lean_nat_dec_le(x_210, x_210);
if (x_214 == 0)
{
lean_object* x_215; 
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_1);
lean_ctor_set(x_215, 1, x_209);
return x_215;
}
else
{
size_t x_216; size_t x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_216 = 0;
x_217 = lean_usize_of_nat(x_210);
lean_dec(x_210);
x_218 = lean_box(0);
x_219 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(x_208, x_216, x_217, x_218, x_2, x_3, x_4, x_5, x_6, x_209);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_208);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_219, 0);
lean_dec(x_221);
lean_ctor_set(x_219, 0, x_1);
return x_219;
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_1);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
}
}
case 4:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_1, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_302, 2);
lean_inc(x_305);
x_306 = lean_ctor_get(x_302, 3);
lean_inc(x_306);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 lean_ctor_release(x_302, 2);
 lean_ctor_release(x_302, 3);
 x_307 = x_302;
} else {
 lean_dec_ref(x_302);
 x_307 = lean_box(0);
}
x_308 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1;
lean_inc(x_2);
lean_inc(x_306);
x_309 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__2(x_306, x_308, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_312 = x_309;
} else {
 lean_dec_ref(x_309);
 x_312 = lean_box(0);
}
x_326 = lean_st_ref_take(x_2, x_311);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = !lean_is_exclusive(x_327);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; uint64_t x_333; uint64_t x_334; uint64_t x_335; uint64_t x_336; uint64_t x_337; uint64_t x_338; uint64_t x_339; size_t x_340; size_t x_341; size_t x_342; size_t x_343; size_t x_344; lean_object* x_345; uint8_t x_346; 
x_330 = lean_ctor_get(x_327, 0);
x_331 = lean_ctor_get(x_327, 1);
x_332 = lean_array_get_size(x_331);
x_333 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_305);
x_334 = 32;
x_335 = lean_uint64_shift_right(x_333, x_334);
x_336 = lean_uint64_xor(x_333, x_335);
x_337 = 16;
x_338 = lean_uint64_shift_right(x_336, x_337);
x_339 = lean_uint64_xor(x_336, x_338);
x_340 = lean_uint64_to_usize(x_339);
x_341 = lean_usize_of_nat(x_332);
lean_dec(x_332);
x_342 = 1;
x_343 = lean_usize_sub(x_341, x_342);
x_344 = lean_usize_land(x_340, x_343);
x_345 = lean_array_uget(x_331, x_344);
x_346 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_305, x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_347 = lean_unsigned_to_nat(1u);
x_348 = lean_nat_add(x_330, x_347);
lean_dec(x_330);
x_349 = lean_box(0);
lean_inc(x_305);
x_350 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_350, 0, x_305);
lean_ctor_set(x_350, 1, x_349);
lean_ctor_set(x_350, 2, x_345);
x_351 = lean_array_uset(x_331, x_344, x_350);
x_352 = lean_unsigned_to_nat(4u);
x_353 = lean_nat_mul(x_348, x_352);
x_354 = lean_unsigned_to_nat(3u);
x_355 = lean_nat_div(x_353, x_354);
lean_dec(x_353);
x_356 = lean_array_get_size(x_351);
x_357 = lean_nat_dec_le(x_355, x_356);
lean_dec(x_356);
lean_dec(x_355);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_351);
lean_ctor_set(x_327, 1, x_358);
lean_ctor_set(x_327, 0, x_348);
x_359 = lean_st_ref_set(x_2, x_327, x_328);
lean_dec(x_2);
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
lean_dec(x_359);
x_313 = x_360;
goto block_325;
}
else
{
lean_object* x_361; lean_object* x_362; 
lean_ctor_set(x_327, 1, x_351);
lean_ctor_set(x_327, 0, x_348);
x_361 = lean_st_ref_set(x_2, x_327, x_328);
lean_dec(x_2);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
x_313 = x_362;
goto block_325;
}
}
else
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_345);
x_363 = lean_st_ref_set(x_2, x_327, x_328);
lean_dec(x_2);
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
lean_dec(x_363);
x_313 = x_364;
goto block_325;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint64_t x_368; uint64_t x_369; uint64_t x_370; uint64_t x_371; uint64_t x_372; uint64_t x_373; uint64_t x_374; size_t x_375; size_t x_376; size_t x_377; size_t x_378; size_t x_379; lean_object* x_380; uint8_t x_381; 
x_365 = lean_ctor_get(x_327, 0);
x_366 = lean_ctor_get(x_327, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_327);
x_367 = lean_array_get_size(x_366);
x_368 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_305);
x_369 = 32;
x_370 = lean_uint64_shift_right(x_368, x_369);
x_371 = lean_uint64_xor(x_368, x_370);
x_372 = 16;
x_373 = lean_uint64_shift_right(x_371, x_372);
x_374 = lean_uint64_xor(x_371, x_373);
x_375 = lean_uint64_to_usize(x_374);
x_376 = lean_usize_of_nat(x_367);
lean_dec(x_367);
x_377 = 1;
x_378 = lean_usize_sub(x_376, x_377);
x_379 = lean_usize_land(x_375, x_378);
x_380 = lean_array_uget(x_366, x_379);
x_381 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_305, x_380);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_382 = lean_unsigned_to_nat(1u);
x_383 = lean_nat_add(x_365, x_382);
lean_dec(x_365);
x_384 = lean_box(0);
lean_inc(x_305);
x_385 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_385, 0, x_305);
lean_ctor_set(x_385, 1, x_384);
lean_ctor_set(x_385, 2, x_380);
x_386 = lean_array_uset(x_366, x_379, x_385);
x_387 = lean_unsigned_to_nat(4u);
x_388 = lean_nat_mul(x_383, x_387);
x_389 = lean_unsigned_to_nat(3u);
x_390 = lean_nat_div(x_388, x_389);
lean_dec(x_388);
x_391 = lean_array_get_size(x_386);
x_392 = lean_nat_dec_le(x_390, x_391);
lean_dec(x_391);
lean_dec(x_390);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_393 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_386);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_383);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_st_ref_set(x_2, x_394, x_328);
lean_dec(x_2);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
lean_dec(x_395);
x_313 = x_396;
goto block_325;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_383);
lean_ctor_set(x_397, 1, x_386);
x_398 = lean_st_ref_set(x_2, x_397, x_328);
lean_dec(x_2);
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
lean_dec(x_398);
x_313 = x_399;
goto block_325;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_380);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_365);
lean_ctor_set(x_400, 1, x_366);
x_401 = lean_st_ref_set(x_2, x_400, x_328);
lean_dec(x_2);
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
lean_dec(x_401);
x_313 = x_402;
goto block_325;
}
}
block_325:
{
size_t x_314; size_t x_315; uint8_t x_316; 
x_314 = lean_ptr_addr(x_306);
lean_dec(x_306);
x_315 = lean_ptr_addr(x_310);
x_316 = lean_usize_dec_eq(x_314, x_315);
if (x_316 == 0)
{
uint8_t x_317; 
x_317 = !lean_is_exclusive(x_1);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_1, 0);
lean_dec(x_318);
if (lean_is_scalar(x_307)) {
 x_319 = lean_alloc_ctor(0, 4, 0);
} else {
 x_319 = x_307;
}
lean_ctor_set(x_319, 0, x_303);
lean_ctor_set(x_319, 1, x_304);
lean_ctor_set(x_319, 2, x_305);
lean_ctor_set(x_319, 3, x_310);
lean_ctor_set(x_1, 0, x_319);
if (lean_is_scalar(x_312)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_312;
}
lean_ctor_set(x_320, 0, x_1);
lean_ctor_set(x_320, 1, x_313);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_1);
if (lean_is_scalar(x_307)) {
 x_321 = lean_alloc_ctor(0, 4, 0);
} else {
 x_321 = x_307;
}
lean_ctor_set(x_321, 0, x_303);
lean_ctor_set(x_321, 1, x_304);
lean_ctor_set(x_321, 2, x_305);
lean_ctor_set(x_321, 3, x_310);
x_322 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_322, 0, x_321);
if (lean_is_scalar(x_312)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_312;
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_313);
return x_323;
}
}
else
{
lean_object* x_324; 
lean_dec(x_310);
lean_dec(x_307);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
if (lean_is_scalar(x_312)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_312;
}
lean_ctor_set(x_324, 0, x_1);
lean_ctor_set(x_324, 1, x_313);
return x_324;
}
}
}
else
{
uint8_t x_403; 
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_2);
lean_dec(x_1);
x_403 = !lean_is_exclusive(x_309);
if (x_403 == 0)
{
return x_309;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_309, 0);
x_405 = lean_ctor_get(x_309, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_309);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
return x_406;
}
}
}
case 5:
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_407 = lean_ctor_get(x_1, 0);
lean_inc(x_407);
x_408 = lean_st_ref_take(x_2, x_7);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = !lean_is_exclusive(x_409);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint64_t x_415; uint64_t x_416; uint64_t x_417; uint64_t x_418; uint64_t x_419; uint64_t x_420; uint64_t x_421; size_t x_422; size_t x_423; size_t x_424; size_t x_425; size_t x_426; lean_object* x_427; uint8_t x_428; 
x_412 = lean_ctor_get(x_409, 0);
x_413 = lean_ctor_get(x_409, 1);
x_414 = lean_array_get_size(x_413);
x_415 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_407);
x_416 = 32;
x_417 = lean_uint64_shift_right(x_415, x_416);
x_418 = lean_uint64_xor(x_415, x_417);
x_419 = 16;
x_420 = lean_uint64_shift_right(x_418, x_419);
x_421 = lean_uint64_xor(x_418, x_420);
x_422 = lean_uint64_to_usize(x_421);
x_423 = lean_usize_of_nat(x_414);
lean_dec(x_414);
x_424 = 1;
x_425 = lean_usize_sub(x_423, x_424);
x_426 = lean_usize_land(x_422, x_425);
x_427 = lean_array_uget(x_413, x_426);
x_428 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_407, x_427);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_nat_add(x_412, x_429);
lean_dec(x_412);
x_431 = lean_box(0);
x_432 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_432, 0, x_407);
lean_ctor_set(x_432, 1, x_431);
lean_ctor_set(x_432, 2, x_427);
x_433 = lean_array_uset(x_413, x_426, x_432);
x_434 = lean_unsigned_to_nat(4u);
x_435 = lean_nat_mul(x_430, x_434);
x_436 = lean_unsigned_to_nat(3u);
x_437 = lean_nat_div(x_435, x_436);
lean_dec(x_435);
x_438 = lean_array_get_size(x_433);
x_439 = lean_nat_dec_le(x_437, x_438);
lean_dec(x_438);
lean_dec(x_437);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_440 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_433);
lean_ctor_set(x_409, 1, x_440);
lean_ctor_set(x_409, 0, x_430);
x_441 = lean_st_ref_set(x_2, x_409, x_410);
lean_dec(x_2);
x_442 = !lean_is_exclusive(x_441);
if (x_442 == 0)
{
lean_object* x_443; 
x_443 = lean_ctor_get(x_441, 0);
lean_dec(x_443);
lean_ctor_set(x_441, 0, x_1);
return x_441;
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_441, 1);
lean_inc(x_444);
lean_dec(x_441);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_1);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
else
{
lean_object* x_446; uint8_t x_447; 
lean_ctor_set(x_409, 1, x_433);
lean_ctor_set(x_409, 0, x_430);
x_446 = lean_st_ref_set(x_2, x_409, x_410);
lean_dec(x_2);
x_447 = !lean_is_exclusive(x_446);
if (x_447 == 0)
{
lean_object* x_448; 
x_448 = lean_ctor_get(x_446, 0);
lean_dec(x_448);
lean_ctor_set(x_446, 0, x_1);
return x_446;
}
else
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_446, 1);
lean_inc(x_449);
lean_dec(x_446);
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_1);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
else
{
lean_object* x_451; uint8_t x_452; 
lean_dec(x_427);
lean_dec(x_407);
x_451 = lean_st_ref_set(x_2, x_409, x_410);
lean_dec(x_2);
x_452 = !lean_is_exclusive(x_451);
if (x_452 == 0)
{
lean_object* x_453; 
x_453 = lean_ctor_get(x_451, 0);
lean_dec(x_453);
lean_ctor_set(x_451, 0, x_1);
return x_451;
}
else
{
lean_object* x_454; lean_object* x_455; 
x_454 = lean_ctor_get(x_451, 1);
lean_inc(x_454);
lean_dec(x_451);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_1);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; uint64_t x_459; uint64_t x_460; uint64_t x_461; uint64_t x_462; uint64_t x_463; uint64_t x_464; uint64_t x_465; size_t x_466; size_t x_467; size_t x_468; size_t x_469; size_t x_470; lean_object* x_471; uint8_t x_472; 
x_456 = lean_ctor_get(x_409, 0);
x_457 = lean_ctor_get(x_409, 1);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_409);
x_458 = lean_array_get_size(x_457);
x_459 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_407);
x_460 = 32;
x_461 = lean_uint64_shift_right(x_459, x_460);
x_462 = lean_uint64_xor(x_459, x_461);
x_463 = 16;
x_464 = lean_uint64_shift_right(x_462, x_463);
x_465 = lean_uint64_xor(x_462, x_464);
x_466 = lean_uint64_to_usize(x_465);
x_467 = lean_usize_of_nat(x_458);
lean_dec(x_458);
x_468 = 1;
x_469 = lean_usize_sub(x_467, x_468);
x_470 = lean_usize_land(x_466, x_469);
x_471 = lean_array_uget(x_457, x_470);
x_472 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_407, x_471);
if (x_472 == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; 
x_473 = lean_unsigned_to_nat(1u);
x_474 = lean_nat_add(x_456, x_473);
lean_dec(x_456);
x_475 = lean_box(0);
x_476 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_476, 0, x_407);
lean_ctor_set(x_476, 1, x_475);
lean_ctor_set(x_476, 2, x_471);
x_477 = lean_array_uset(x_457, x_470, x_476);
x_478 = lean_unsigned_to_nat(4u);
x_479 = lean_nat_mul(x_474, x_478);
x_480 = lean_unsigned_to_nat(3u);
x_481 = lean_nat_div(x_479, x_480);
lean_dec(x_479);
x_482 = lean_array_get_size(x_477);
x_483 = lean_nat_dec_le(x_481, x_482);
lean_dec(x_482);
lean_dec(x_481);
if (x_483 == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_484 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_477);
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_474);
lean_ctor_set(x_485, 1, x_484);
x_486 = lean_st_ref_set(x_2, x_485, x_410);
lean_dec(x_2);
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_488 = x_486;
} else {
 lean_dec_ref(x_486);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_1);
lean_ctor_set(x_489, 1, x_487);
return x_489;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_474);
lean_ctor_set(x_490, 1, x_477);
x_491 = lean_st_ref_set(x_2, x_490, x_410);
lean_dec(x_2);
x_492 = lean_ctor_get(x_491, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_493 = x_491;
} else {
 lean_dec_ref(x_491);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(0, 2, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_1);
lean_ctor_set(x_494, 1, x_492);
return x_494;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_471);
lean_dec(x_407);
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_456);
lean_ctor_set(x_495, 1, x_457);
x_496 = lean_st_ref_set(x_2, x_495, x_410);
lean_dec(x_2);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_498 = x_496;
} else {
 lean_dec_ref(x_496);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_1);
lean_ctor_set(x_499, 1, x_497);
return x_499;
}
}
}
default: 
{
lean_object* x_500; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_1);
lean_ctor_set(x_500, 1, x_7);
return x_500;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_elimDead___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_elimDead___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Code_elimDead___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_elimDead___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_Code_elimDead___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Compiler_LCNF_Code_elimDead___closed__3;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = l_Lean_Compiler_LCNF_Code_elimDead(x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_1, 4, x_16);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_1, 4, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_ctor_get(x_1, 3);
x_28 = lean_ctor_get(x_1, 4);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_31 = lean_ctor_get(x_1, 5);
lean_inc(x_31);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_32 = l_Lean_Compiler_LCNF_Code_elimDead(x_28, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_27);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*6, x_29);
lean_ctor_set_uint8(x_36, sizeof(void*)*6 + 1, x_30);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1 = _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1);
l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2 = _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2);
l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3 = _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3);
l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4 = _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4);
l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1 = _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1);
l_Lean_Compiler_LCNF_Code_elimDead___closed__1 = _init_l_Lean_Compiler_LCNF_Code_elimDead___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_elimDead___closed__1);
l_Lean_Compiler_LCNF_Code_elimDead___closed__2 = _init_l_Lean_Compiler_LCNF_Code_elimDead___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_elimDead___closed__2);
l_Lean_Compiler_LCNF_Code_elimDead___closed__3 = _init_l_Lean_Compiler_LCNF_Code_elimDead___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_elimDead___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
