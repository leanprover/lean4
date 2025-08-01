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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_elimDead_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCode;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0(lean_object*);
lean_object* l_Lean_beqFVarId____x40_Lean_Expr___hyg_1499____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_elimDead___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1;
extern lean_object* l_Lean_instFVarIdHashSetEmptyCollection;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_4);
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
x_26 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_22);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_3);
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
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_3, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_box(0);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_4);
lean_inc(x_3);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_19);
x_28 = lean_array_uset(x_5, x_18, x_27);
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
x_35 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_28);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_4, x_37);
lean_dec(x_4);
lean_inc(x_3);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_39, 2, x_19);
x_40 = lean_array_uset(x_5, x_18, x_39);
x_41 = lean_unsigned_to_nat(4u);
x_42 = lean_nat_mul(x_38, x_41);
x_43 = lean_unsigned_to_nat(3u);
x_44 = lean_nat_div(x_42, x_43);
lean_dec(x_42);
x_45 = lean_array_get_size(x_40);
x_46 = lean_nat_dec_le(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_40);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_1;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_2);
lean_dec_ref(x_2);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
x_9 = lean_array_get_size(x_8);
x_10 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_4);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_8, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_4, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_25 = lean_ctor_get(x_1, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
x_27 = lean_box(0);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_7, x_28);
lean_dec(x_7);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 2, x_22);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_2, 0, x_4);
x_30 = lean_array_uset(x_8, x_21, x_2);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_nat_mul(x_29, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_30);
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_29);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set(x_1, 0, x_29);
return x_1;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_7, x_39);
lean_dec(x_7);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 2, x_22);
lean_ctor_set(x_2, 1, x_38);
lean_ctor_set(x_2, 0, x_4);
x_41 = lean_array_uset(x_8, x_21, x_2);
x_42 = lean_unsigned_to_nat(4u);
x_43 = lean_nat_mul(x_40, x_42);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_div(x_43, x_44);
lean_dec(x_43);
x_46 = lean_array_get_size(x_41);
x_47 = lean_nat_dec_le(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
}
else
{
lean_dec(x_22);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_free_object(x_2);
lean_dec(x_4);
return x_1;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; size_t x_62; size_t x_63; size_t x_64; size_t x_65; size_t x_66; lean_object* x_67; uint8_t x_68; 
x_51 = lean_ctor_get(x_2, 2);
lean_inc(x_51);
lean_dec(x_2);
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_53);
x_54 = lean_array_get_size(x_53);
x_55 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_51);
x_56 = 32;
x_57 = lean_uint64_shift_right(x_55, x_56);
x_58 = lean_uint64_xor(x_55, x_57);
x_59 = 16;
x_60 = lean_uint64_shift_right(x_58, x_59);
x_61 = lean_uint64_xor(x_58, x_60);
x_62 = lean_uint64_to_usize(x_61);
x_63 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_64 = 1;
x_65 = lean_usize_sub(x_63, x_64);
x_66 = lean_usize_land(x_62, x_65);
x_67 = lean_array_uget(x_53, x_66);
x_68 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_51, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_69 = x_1;
} else {
 lean_dec_ref(x_1);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_52, x_71);
lean_dec(x_52);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_51);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_73, 2, x_67);
x_74 = lean_array_uset(x_53, x_66, x_73);
x_75 = lean_unsigned_to_nat(4u);
x_76 = lean_nat_mul(x_72, x_75);
x_77 = lean_unsigned_to_nat(3u);
x_78 = lean_nat_div(x_76, x_77);
lean_dec(x_76);
x_79 = lean_array_get_size(x_74);
x_80 = lean_nat_dec_le(x_78, x_79);
lean_dec(x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_74);
if (lean_is_scalar(x_69)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_69;
}
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
else
{
lean_object* x_83; 
if (lean_is_scalar(x_69)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_69;
}
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_74);
return x_83;
}
}
else
{
lean_dec(x_67);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
return x_1;
}
}
}
case 3:
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_84);
lean_dec_ref(x_2);
x_85 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_84);
lean_dec_ref(x_84);
return x_85;
}
case 4:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; size_t x_98; size_t x_99; size_t x_100; size_t x_101; size_t x_102; lean_object* x_103; uint8_t x_104; 
x_86 = lean_ctor_get(x_2, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_87);
lean_dec_ref(x_2);
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_89);
x_90 = lean_array_get_size(x_89);
x_91 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_86);
x_92 = 32;
x_93 = lean_uint64_shift_right(x_91, x_92);
x_94 = lean_uint64_xor(x_91, x_93);
x_95 = 16;
x_96 = lean_uint64_shift_right(x_94, x_95);
x_97 = lean_uint64_xor(x_94, x_96);
x_98 = lean_uint64_to_usize(x_97);
x_99 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_100 = 1;
x_101 = lean_usize_sub(x_99, x_100);
x_102 = lean_usize_land(x_98, x_101);
x_103 = lean_array_uget(x_89, x_102);
x_104 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_86, x_103);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_1);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_106 = lean_ctor_get(x_1, 1);
lean_dec(x_106);
x_107 = lean_ctor_get(x_1, 0);
lean_dec(x_107);
x_108 = lean_box(0);
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_nat_add(x_88, x_109);
lean_dec(x_88);
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_86);
lean_ctor_set(x_111, 1, x_108);
lean_ctor_set(x_111, 2, x_103);
x_112 = lean_array_uset(x_89, x_102, x_111);
x_113 = lean_unsigned_to_nat(4u);
x_114 = lean_nat_mul(x_110, x_113);
x_115 = lean_unsigned_to_nat(3u);
x_116 = lean_nat_div(x_114, x_115);
lean_dec(x_114);
x_117 = lean_array_get_size(x_112);
x_118 = lean_nat_dec_le(x_116, x_117);
lean_dec(x_117);
lean_dec(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_112);
lean_ctor_set(x_1, 1, x_119);
lean_ctor_set(x_1, 0, x_110);
x_120 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_87);
lean_dec_ref(x_87);
return x_120;
}
else
{
lean_object* x_121; 
lean_ctor_set(x_1, 1, x_112);
lean_ctor_set(x_1, 0, x_110);
x_121 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_87);
lean_dec_ref(x_87);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_1);
x_122 = lean_box(0);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_add(x_88, x_123);
lean_dec(x_88);
x_125 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_125, 0, x_86);
lean_ctor_set(x_125, 1, x_122);
lean_ctor_set(x_125, 2, x_103);
x_126 = lean_array_uset(x_89, x_102, x_125);
x_127 = lean_unsigned_to_nat(4u);
x_128 = lean_nat_mul(x_124, x_127);
x_129 = lean_unsigned_to_nat(3u);
x_130 = lean_nat_div(x_128, x_129);
lean_dec(x_128);
x_131 = lean_array_get_size(x_126);
x_132 = lean_nat_dec_le(x_130, x_131);
lean_dec(x_131);
lean_dec(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_126);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_124);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_134, x_87);
lean_dec_ref(x_87);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_124);
lean_ctor_set(x_136, 1, x_126);
x_137 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_136, x_87);
lean_dec_ref(x_87);
return x_137;
}
}
}
else
{
lean_object* x_138; 
lean_dec(x_103);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec(x_86);
x_138 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_87);
lean_dec_ref(x_87);
return x_138;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_5, x_1);
x_8 = lean_st_ref_set(x_2, x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
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
lean_dec_ref(x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_5, x_1);
x_8 = lean_st_ref_set(x_2, x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
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
lean_dec_ref(x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqFVarId____x40_Lean_Expr___hyg_1499____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
x_9 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__0;
x_10 = lean_box(0);
x_18 = lean_array_get_size(x_8);
x_19 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_1);
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
x_31 = lean_array_uget(x_8, x_30);
lean_inc(x_31);
lean_inc(x_1);
x_32 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_9, x_1, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_5);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_34 = lean_ctor_get(x_5, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_5, 0);
lean_dec(x_35);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_7, x_36);
lean_dec(x_7);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_10);
lean_ctor_set(x_38, 2, x_31);
x_39 = lean_array_uset(x_8, x_30, x_38);
x_40 = lean_unsigned_to_nat(4u);
x_41 = lean_nat_mul(x_37, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_39);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__1;
x_47 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_46, x_39);
lean_ctor_set(x_5, 1, x_47);
lean_ctor_set(x_5, 0, x_37);
x_11 = x_5;
goto block_17;
}
else
{
lean_ctor_set(x_5, 1, x_39);
lean_ctor_set(x_5, 0, x_37);
x_11 = x_5;
goto block_17;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_5);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_7, x_48);
lean_dec(x_7);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_10);
lean_ctor_set(x_50, 2, x_31);
x_51 = lean_array_uset(x_8, x_30, x_50);
x_52 = lean_unsigned_to_nat(4u);
x_53 = lean_nat_mul(x_49, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_nat_div(x_53, x_54);
lean_dec(x_53);
x_56 = lean_array_get_size(x_51);
x_57 = lean_nat_dec_le(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__1;
x_59 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_58, x_51);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_59);
x_11 = x_60;
goto block_17;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_51);
x_11 = x_61;
goto block_17;
}
}
}
else
{
lean_dec(x_31);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_11 = x_5;
goto block_17;
}
block_17:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_set(x_2, x_11, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; uint8_t x_36; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_12);
x_13 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__0;
x_14 = lean_box(0);
x_22 = lean_array_get_size(x_12);
x_23 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_1);
x_24 = 32;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = 16;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = 1;
x_33 = lean_usize_sub(x_31, x_32);
x_34 = lean_usize_land(x_30, x_33);
x_35 = lean_array_uget(x_12, x_34);
lean_inc(x_35);
lean_inc(x_1);
x_36 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_13, x_1, x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_38 = lean_ctor_get(x_9, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_9, 0);
lean_dec(x_39);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_11, x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_14);
lean_ctor_set(x_42, 2, x_35);
x_43 = lean_array_uset(x_12, x_34, x_42);
x_44 = lean_unsigned_to_nat(4u);
x_45 = lean_nat_mul(x_41, x_44);
x_46 = lean_unsigned_to_nat(3u);
x_47 = lean_nat_div(x_45, x_46);
lean_dec(x_45);
x_48 = lean_array_get_size(x_43);
x_49 = lean_nat_dec_le(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__1;
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_50, x_43);
lean_ctor_set(x_9, 1, x_51);
lean_ctor_set(x_9, 0, x_41);
x_15 = x_9;
goto block_21;
}
else
{
lean_ctor_set(x_9, 1, x_43);
lean_ctor_set(x_9, 0, x_41);
x_15 = x_9;
goto block_21;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_9);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_11, x_52);
lean_dec(x_11);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_14);
lean_ctor_set(x_54, 2, x_35);
x_55 = lean_array_uset(x_12, x_34, x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_mul(x_53, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_div(x_57, x_58);
lean_dec(x_57);
x_60 = lean_array_get_size(x_55);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__1;
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_62, x_55);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_63);
x_15 = x_64;
goto block_21;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_55);
x_15 = x_65;
goto block_21;
}
}
}
else
{
lean_dec(x_35);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_15 = x_9;
goto block_21;
}
block_21:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_st_ref_set(x_2, x_15, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_10);
x_11 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_9, x_8, x_12, x_4, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_8 = lean_st_ref_take(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_9, x_11);
lean_dec(x_11);
x_13 = lean_st_ref_set(x_5, x_12, x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_box(0);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_15;
x_6 = x_14;
goto _start;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_29);
x_13 = x_29;
goto block_28;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_30);
x_13 = x_30;
goto block_28;
}
block_28:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_14 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_13, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc_ref(x_12);
x_17 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_12, x_15);
x_18 = lean_ptr_addr(x_12);
lean_dec_ref(x_12);
x_19 = lean_ptr_addr(x_17);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = lean_array_fset(x_2, x_1, x_17);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_23;
x_8 = x_16;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_17);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_1, x_25);
lean_dec(x_1);
x_1 = x_26;
x_8 = x_16;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__2;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(319u);
x_4 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1;
x_5 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; size_t x_110; size_t x_111; size_t x_112; size_t x_113; size_t x_114; lean_object* x_115; uint8_t x_116; 
x_91 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_92);
lean_inc_ref(x_92);
x_93 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_92, x_2, x_3, x_4, x_5, x_6, x_7);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_st_ref_get(x_2, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec_ref(x_96);
x_99 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_91, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_91, 3);
lean_inc(x_101);
x_102 = lean_array_get_size(x_99);
x_103 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_100);
x_104 = 32;
x_105 = lean_uint64_shift_right(x_103, x_104);
x_106 = lean_uint64_xor(x_103, x_105);
x_107 = 16;
x_108 = lean_uint64_shift_right(x_106, x_107);
x_109 = lean_uint64_xor(x_106, x_108);
x_110 = lean_uint64_to_usize(x_109);
x_111 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_112 = 1;
x_113 = lean_usize_sub(x_111, x_112);
x_114 = lean_usize_land(x_110, x_113);
x_115 = lean_array_uget(x_99, x_114);
lean_dec_ref(x_99);
x_116 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_100, x_115);
lean_dec(x_115);
lean_dec(x_100);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
lean_dec(x_101);
lean_dec_ref(x_92);
lean_dec_ref(x_1);
x_117 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_91, x_4, x_98);
lean_dec_ref(x_91);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_117, 0);
lean_dec(x_119);
lean_ctor_set(x_117, 0, x_94);
return x_117;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_94);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_st_ref_take(x_2, x_98);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_123, x_101);
x_126 = lean_st_ref_set(x_2, x_125, x_124);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; size_t x_129; size_t x_130; uint8_t x_131; 
x_128 = lean_ctor_get(x_126, 0);
lean_dec(x_128);
x_129 = lean_ptr_addr(x_92);
lean_dec_ref(x_92);
x_130 = lean_ptr_addr(x_94);
x_131 = lean_usize_dec_eq(x_129, x_130);
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_1);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_1, 1);
lean_dec(x_133);
x_134 = lean_ctor_get(x_1, 0);
lean_dec(x_134);
lean_ctor_set(x_1, 1, x_94);
lean_ctor_set(x_126, 0, x_1);
return x_126;
}
else
{
lean_object* x_135; 
lean_dec(x_1);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_91);
lean_ctor_set(x_135, 1, x_94);
lean_ctor_set(x_126, 0, x_135);
return x_126;
}
}
else
{
lean_dec(x_94);
lean_dec_ref(x_91);
lean_ctor_set(x_126, 0, x_1);
return x_126;
}
}
else
{
lean_object* x_136; size_t x_137; size_t x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_126, 1);
lean_inc(x_136);
lean_dec(x_126);
x_137 = lean_ptr_addr(x_92);
lean_dec_ref(x_92);
x_138 = lean_ptr_addr(x_94);
x_139 = lean_usize_dec_eq(x_137, x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_140 = x_1;
} else {
 lean_dec_ref(x_1);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_91);
lean_ctor_set(x_141, 1, x_94);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_136);
return x_142;
}
else
{
lean_object* x_143; 
lean_dec(x_94);
lean_dec_ref(x_91);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_1);
lean_ctor_set(x_143, 1, x_136);
return x_143;
}
}
}
}
case 3:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; uint64_t x_187; uint64_t x_188; uint64_t x_189; uint64_t x_190; size_t x_191; size_t x_192; size_t x_193; size_t x_194; size_t x_195; lean_object* x_196; uint8_t x_197; 
x_144 = lean_ctor_get(x_1, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_145);
x_146 = lean_st_ref_take(x_2, x_7);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_181 = lean_ctor_get(x_147, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_147, 1);
lean_inc_ref(x_182);
x_183 = lean_array_get_size(x_182);
x_184 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_144);
x_185 = 32;
x_186 = lean_uint64_shift_right(x_184, x_185);
x_187 = lean_uint64_xor(x_184, x_186);
x_188 = 16;
x_189 = lean_uint64_shift_right(x_187, x_188);
x_190 = lean_uint64_xor(x_187, x_189);
x_191 = lean_uint64_to_usize(x_190);
x_192 = lean_usize_of_nat(x_183);
lean_dec(x_183);
x_193 = 1;
x_194 = lean_usize_sub(x_192, x_193);
x_195 = lean_usize_land(x_191, x_194);
x_196 = lean_array_uget(x_182, x_195);
x_197 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_144, x_196);
if (x_197 == 0)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_147);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_199 = lean_ctor_get(x_147, 1);
lean_dec(x_199);
x_200 = lean_ctor_get(x_147, 0);
lean_dec(x_200);
x_201 = lean_box(0);
x_202 = lean_unsigned_to_nat(1u);
x_203 = lean_nat_add(x_181, x_202);
lean_dec(x_181);
x_204 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_204, 0, x_144);
lean_ctor_set(x_204, 1, x_201);
lean_ctor_set(x_204, 2, x_196);
x_205 = lean_array_uset(x_182, x_195, x_204);
x_206 = lean_unsigned_to_nat(4u);
x_207 = lean_nat_mul(x_203, x_206);
x_208 = lean_unsigned_to_nat(3u);
x_209 = lean_nat_div(x_207, x_208);
lean_dec(x_207);
x_210 = lean_array_get_size(x_205);
x_211 = lean_nat_dec_le(x_209, x_210);
lean_dec(x_210);
lean_dec(x_209);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_205);
lean_ctor_set(x_147, 1, x_212);
lean_ctor_set(x_147, 0, x_203);
x_149 = x_147;
goto block_180;
}
else
{
lean_ctor_set(x_147, 1, x_205);
lean_ctor_set(x_147, 0, x_203);
x_149 = x_147;
goto block_180;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_147);
x_213 = lean_box(0);
x_214 = lean_unsigned_to_nat(1u);
x_215 = lean_nat_add(x_181, x_214);
lean_dec(x_181);
x_216 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_216, 0, x_144);
lean_ctor_set(x_216, 1, x_213);
lean_ctor_set(x_216, 2, x_196);
x_217 = lean_array_uset(x_182, x_195, x_216);
x_218 = lean_unsigned_to_nat(4u);
x_219 = lean_nat_mul(x_215, x_218);
x_220 = lean_unsigned_to_nat(3u);
x_221 = lean_nat_div(x_219, x_220);
lean_dec(x_219);
x_222 = lean_array_get_size(x_217);
x_223 = lean_nat_dec_le(x_221, x_222);
lean_dec(x_222);
lean_dec(x_221);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_217);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_215);
lean_ctor_set(x_225, 1, x_224);
x_149 = x_225;
goto block_180;
}
else
{
lean_object* x_226; 
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_215);
lean_ctor_set(x_226, 1, x_217);
x_149 = x_226;
goto block_180;
}
}
}
else
{
lean_dec(x_196);
lean_dec_ref(x_182);
lean_dec(x_181);
lean_dec(x_144);
x_149 = x_147;
goto block_180;
}
block_180:
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_st_ref_set(x_2, x_149, x_148);
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_152 = lean_ctor_get(x_150, 1);
x_153 = lean_ctor_get(x_150, 0);
lean_dec(x_153);
x_154 = lean_unsigned_to_nat(0u);
x_155 = lean_array_get_size(x_145);
x_156 = lean_nat_dec_lt(x_154, x_155);
if (x_156 == 0)
{
lean_dec(x_155);
lean_dec_ref(x_145);
lean_ctor_set(x_150, 0, x_1);
return x_150;
}
else
{
uint8_t x_157; 
x_157 = lean_nat_dec_le(x_155, x_155);
if (x_157 == 0)
{
lean_dec(x_155);
lean_dec_ref(x_145);
lean_ctor_set(x_150, 0, x_1);
return x_150;
}
else
{
lean_object* x_158; size_t x_159; size_t x_160; lean_object* x_161; uint8_t x_162; 
lean_free_object(x_150);
x_158 = lean_box(0);
x_159 = 0;
x_160 = lean_usize_of_nat(x_155);
lean_dec(x_155);
x_161 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___redArg(x_145, x_159, x_160, x_158, x_2, x_152);
lean_dec_ref(x_145);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_161, 0);
lean_dec(x_163);
lean_ctor_set(x_161, 0, x_1);
return x_161;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_1);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_150, 1);
lean_inc(x_166);
lean_dec(x_150);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_array_get_size(x_145);
x_169 = lean_nat_dec_lt(x_167, x_168);
if (x_169 == 0)
{
lean_object* x_170; 
lean_dec(x_168);
lean_dec_ref(x_145);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_1);
lean_ctor_set(x_170, 1, x_166);
return x_170;
}
else
{
uint8_t x_171; 
x_171 = lean_nat_dec_le(x_168, x_168);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_168);
lean_dec_ref(x_145);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_1);
lean_ctor_set(x_172, 1, x_166);
return x_172;
}
else
{
lean_object* x_173; size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_173 = lean_box(0);
x_174 = 0;
x_175 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_176 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___redArg(x_145, x_174, x_175, x_173, x_2, x_166);
lean_dec_ref(x_145);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_178 = x_176;
} else {
 lean_dec_ref(x_176);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_1);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
}
}
}
case 4:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint64_t x_265; uint64_t x_266; uint64_t x_267; uint64_t x_268; uint64_t x_269; uint64_t x_270; uint64_t x_271; size_t x_272; size_t x_273; size_t x_274; size_t x_275; size_t x_276; lean_object* x_277; uint8_t x_278; 
x_227 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc_ref(x_229);
x_230 = lean_ctor_get(x_227, 2);
lean_inc(x_230);
x_231 = lean_ctor_get(x_227, 3);
lean_inc_ref(x_231);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 lean_ctor_release(x_227, 2);
 lean_ctor_release(x_227, 3);
 x_232 = x_227;
} else {
 lean_dec_ref(x_227);
 x_232 = lean_box(0);
}
x_233 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_231);
x_234 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__2(x_233, x_231, x_2, x_3, x_4, x_5, x_6, x_7);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec_ref(x_234);
x_237 = lean_st_ref_take(x_2, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec_ref(x_237);
x_262 = lean_ctor_get(x_238, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_238, 1);
lean_inc_ref(x_263);
x_264 = lean_array_get_size(x_263);
x_265 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_230);
x_266 = 32;
x_267 = lean_uint64_shift_right(x_265, x_266);
x_268 = lean_uint64_xor(x_265, x_267);
x_269 = 16;
x_270 = lean_uint64_shift_right(x_268, x_269);
x_271 = lean_uint64_xor(x_268, x_270);
x_272 = lean_uint64_to_usize(x_271);
x_273 = lean_usize_of_nat(x_264);
lean_dec(x_264);
x_274 = 1;
x_275 = lean_usize_sub(x_273, x_274);
x_276 = lean_usize_land(x_272, x_275);
x_277 = lean_array_uget(x_263, x_276);
x_278 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_230, x_277);
if (x_278 == 0)
{
uint8_t x_279; 
x_279 = !lean_is_exclusive(x_238);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_280 = lean_ctor_get(x_238, 1);
lean_dec(x_280);
x_281 = lean_ctor_get(x_238, 0);
lean_dec(x_281);
x_282 = lean_box(0);
x_283 = lean_unsigned_to_nat(1u);
x_284 = lean_nat_add(x_262, x_283);
lean_dec(x_262);
lean_inc(x_230);
x_285 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_285, 0, x_230);
lean_ctor_set(x_285, 1, x_282);
lean_ctor_set(x_285, 2, x_277);
x_286 = lean_array_uset(x_263, x_276, x_285);
x_287 = lean_unsigned_to_nat(4u);
x_288 = lean_nat_mul(x_284, x_287);
x_289 = lean_unsigned_to_nat(3u);
x_290 = lean_nat_div(x_288, x_289);
lean_dec(x_288);
x_291 = lean_array_get_size(x_286);
x_292 = lean_nat_dec_le(x_290, x_291);
lean_dec(x_291);
lean_dec(x_290);
if (x_292 == 0)
{
lean_object* x_293; 
x_293 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_286);
lean_ctor_set(x_238, 1, x_293);
lean_ctor_set(x_238, 0, x_284);
x_240 = x_238;
goto block_261;
}
else
{
lean_ctor_set(x_238, 1, x_286);
lean_ctor_set(x_238, 0, x_284);
x_240 = x_238;
goto block_261;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
lean_dec(x_238);
x_294 = lean_box(0);
x_295 = lean_unsigned_to_nat(1u);
x_296 = lean_nat_add(x_262, x_295);
lean_dec(x_262);
lean_inc(x_230);
x_297 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_297, 0, x_230);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_277);
x_298 = lean_array_uset(x_263, x_276, x_297);
x_299 = lean_unsigned_to_nat(4u);
x_300 = lean_nat_mul(x_296, x_299);
x_301 = lean_unsigned_to_nat(3u);
x_302 = lean_nat_div(x_300, x_301);
lean_dec(x_300);
x_303 = lean_array_get_size(x_298);
x_304 = lean_nat_dec_le(x_302, x_303);
lean_dec(x_303);
lean_dec(x_302);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_298);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_296);
lean_ctor_set(x_306, 1, x_305);
x_240 = x_306;
goto block_261;
}
else
{
lean_object* x_307; 
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_296);
lean_ctor_set(x_307, 1, x_298);
x_240 = x_307;
goto block_261;
}
}
}
else
{
lean_dec(x_277);
lean_dec_ref(x_263);
lean_dec(x_262);
x_240 = x_238;
goto block_261;
}
block_261:
{
lean_object* x_241; uint8_t x_242; 
x_241 = lean_st_ref_set(x_2, x_240, x_239);
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
lean_object* x_243; size_t x_244; size_t x_245; uint8_t x_246; 
x_243 = lean_ctor_get(x_241, 0);
lean_dec(x_243);
x_244 = lean_ptr_addr(x_231);
lean_dec_ref(x_231);
x_245 = lean_ptr_addr(x_235);
x_246 = lean_usize_dec_eq(x_244, x_245);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_1);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_1, 0);
lean_dec(x_248);
if (lean_is_scalar(x_232)) {
 x_249 = lean_alloc_ctor(0, 4, 0);
} else {
 x_249 = x_232;
}
lean_ctor_set(x_249, 0, x_228);
lean_ctor_set(x_249, 1, x_229);
lean_ctor_set(x_249, 2, x_230);
lean_ctor_set(x_249, 3, x_235);
lean_ctor_set(x_1, 0, x_249);
lean_ctor_set(x_241, 0, x_1);
return x_241;
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_1);
if (lean_is_scalar(x_232)) {
 x_250 = lean_alloc_ctor(0, 4, 0);
} else {
 x_250 = x_232;
}
lean_ctor_set(x_250, 0, x_228);
lean_ctor_set(x_250, 1, x_229);
lean_ctor_set(x_250, 2, x_230);
lean_ctor_set(x_250, 3, x_235);
x_251 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_241, 0, x_251);
return x_241;
}
}
else
{
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_ctor_set(x_241, 0, x_1);
return x_241;
}
}
else
{
lean_object* x_252; size_t x_253; size_t x_254; uint8_t x_255; 
x_252 = lean_ctor_get(x_241, 1);
lean_inc(x_252);
lean_dec(x_241);
x_253 = lean_ptr_addr(x_231);
lean_dec_ref(x_231);
x_254 = lean_ptr_addr(x_235);
x_255 = lean_usize_dec_eq(x_253, x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_256 = x_1;
} else {
 lean_dec_ref(x_1);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_257 = lean_alloc_ctor(0, 4, 0);
} else {
 x_257 = x_232;
}
lean_ctor_set(x_257, 0, x_228);
lean_ctor_set(x_257, 1, x_229);
lean_ctor_set(x_257, 2, x_230);
lean_ctor_set(x_257, 3, x_235);
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(4, 1, 0);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_252);
return x_259;
}
else
{
lean_object* x_260; 
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_1);
lean_ctor_set(x_260, 1, x_252);
return x_260;
}
}
}
}
case 5:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint64_t x_322; uint64_t x_323; uint64_t x_324; uint64_t x_325; uint64_t x_326; uint64_t x_327; uint64_t x_328; size_t x_329; size_t x_330; size_t x_331; size_t x_332; size_t x_333; lean_object* x_334; uint8_t x_335; 
x_308 = lean_ctor_get(x_1, 0);
lean_inc(x_308);
x_309 = lean_st_ref_take(x_2, x_7);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec_ref(x_309);
x_319 = lean_ctor_get(x_310, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_310, 1);
lean_inc_ref(x_320);
x_321 = lean_array_get_size(x_320);
x_322 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_308);
x_323 = 32;
x_324 = lean_uint64_shift_right(x_322, x_323);
x_325 = lean_uint64_xor(x_322, x_324);
x_326 = 16;
x_327 = lean_uint64_shift_right(x_325, x_326);
x_328 = lean_uint64_xor(x_325, x_327);
x_329 = lean_uint64_to_usize(x_328);
x_330 = lean_usize_of_nat(x_321);
lean_dec(x_321);
x_331 = 1;
x_332 = lean_usize_sub(x_330, x_331);
x_333 = lean_usize_land(x_329, x_332);
x_334 = lean_array_uget(x_320, x_333);
x_335 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_308, x_334);
if (x_335 == 0)
{
uint8_t x_336; 
x_336 = !lean_is_exclusive(x_310);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_337 = lean_ctor_get(x_310, 1);
lean_dec(x_337);
x_338 = lean_ctor_get(x_310, 0);
lean_dec(x_338);
x_339 = lean_box(0);
x_340 = lean_unsigned_to_nat(1u);
x_341 = lean_nat_add(x_319, x_340);
lean_dec(x_319);
x_342 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_342, 0, x_308);
lean_ctor_set(x_342, 1, x_339);
lean_ctor_set(x_342, 2, x_334);
x_343 = lean_array_uset(x_320, x_333, x_342);
x_344 = lean_unsigned_to_nat(4u);
x_345 = lean_nat_mul(x_341, x_344);
x_346 = lean_unsigned_to_nat(3u);
x_347 = lean_nat_div(x_345, x_346);
lean_dec(x_345);
x_348 = lean_array_get_size(x_343);
x_349 = lean_nat_dec_le(x_347, x_348);
lean_dec(x_348);
lean_dec(x_347);
if (x_349 == 0)
{
lean_object* x_350; 
x_350 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_343);
lean_ctor_set(x_310, 1, x_350);
lean_ctor_set(x_310, 0, x_341);
x_312 = x_310;
goto block_318;
}
else
{
lean_ctor_set(x_310, 1, x_343);
lean_ctor_set(x_310, 0, x_341);
x_312 = x_310;
goto block_318;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; 
lean_dec(x_310);
x_351 = lean_box(0);
x_352 = lean_unsigned_to_nat(1u);
x_353 = lean_nat_add(x_319, x_352);
lean_dec(x_319);
x_354 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_354, 0, x_308);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_334);
x_355 = lean_array_uset(x_320, x_333, x_354);
x_356 = lean_unsigned_to_nat(4u);
x_357 = lean_nat_mul(x_353, x_356);
x_358 = lean_unsigned_to_nat(3u);
x_359 = lean_nat_div(x_357, x_358);
lean_dec(x_357);
x_360 = lean_array_get_size(x_355);
x_361 = lean_nat_dec_le(x_359, x_360);
lean_dec(x_360);
lean_dec(x_359);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; 
x_362 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_355);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_353);
lean_ctor_set(x_363, 1, x_362);
x_312 = x_363;
goto block_318;
}
else
{
lean_object* x_364; 
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_353);
lean_ctor_set(x_364, 1, x_355);
x_312 = x_364;
goto block_318;
}
}
}
else
{
lean_dec(x_334);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec(x_308);
x_312 = x_310;
goto block_318;
}
block_318:
{
lean_object* x_313; uint8_t x_314; 
x_313 = lean_st_ref_set(x_2, x_312, x_311);
x_314 = !lean_is_exclusive(x_313);
if (x_314 == 0)
{
lean_object* x_315; 
x_315 = lean_ctor_get(x_313, 0);
lean_dec(x_315);
lean_ctor_set(x_313, 0, x_1);
return x_313;
}
else
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_313, 1);
lean_inc(x_316);
lean_dec(x_313);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_1);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
case 6:
{
lean_object* x_365; 
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_1);
lean_ctor_set(x_365, 1, x_7);
return x_365;
}
default: 
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_366);
x_367 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_367);
x_24 = x_366;
x_25 = x_367;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
goto block_90;
}
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec_ref(x_10);
lean_dec_ref(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_18);
lean_dec_ref(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
block_90:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; uint8_t x_54; 
x_32 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_25, x_26, x_27, x_28, x_29, x_30, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_st_ref_get(x_26, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc_ref(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_39);
x_40 = lean_array_get_size(x_38);
x_41 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_39);
x_42 = 32;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = 16;
x_46 = lean_uint64_shift_right(x_44, x_45);
x_47 = lean_uint64_xor(x_44, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_50 = 1;
x_51 = lean_usize_sub(x_49, x_50);
x_52 = lean_usize_land(x_48, x_51);
x_53 = lean_array_uget(x_38, x_52);
lean_dec_ref(x_38);
x_54 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_39, x_53);
lean_dec(x_53);
lean_dec(x_39);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; uint8_t x_57; 
lean_dec_ref(x_1);
x_55 = 1;
x_56 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_24, x_55, x_28, x_37);
lean_dec_ref(x_24);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_33);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_33);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; 
x_61 = l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(x_24, x_26, x_27, x_28, x_29, x_30, x_37);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_65);
x_66 = lean_ptr_addr(x_65);
lean_dec_ref(x_65);
x_67 = lean_ptr_addr(x_33);
x_68 = lean_usize_dec_eq(x_66, x_67);
if (x_68 == 0)
{
lean_dec_ref(x_64);
x_8 = x_62;
x_9 = x_63;
x_10 = x_33;
x_11 = x_68;
goto block_15;
}
else
{
size_t x_69; size_t x_70; uint8_t x_71; 
x_69 = lean_ptr_addr(x_64);
lean_dec_ref(x_64);
x_70 = lean_ptr_addr(x_62);
x_71 = lean_usize_dec_eq(x_69, x_70);
x_8 = x_62;
x_9 = x_63;
x_10 = x_33;
x_11 = x_71;
goto block_15;
}
}
case 2:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; uint8_t x_78; 
x_72 = lean_ctor_get(x_61, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_61, 1);
lean_inc(x_73);
lean_dec_ref(x_61);
x_74 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_75);
x_76 = lean_ptr_addr(x_75);
lean_dec_ref(x_75);
x_77 = lean_ptr_addr(x_33);
x_78 = lean_usize_dec_eq(x_76, x_77);
if (x_78 == 0)
{
lean_dec_ref(x_74);
x_16 = x_72;
x_17 = x_73;
x_18 = x_33;
x_19 = x_78;
goto block_23;
}
else
{
size_t x_79; size_t x_80; uint8_t x_81; 
x_79 = lean_ptr_addr(x_74);
lean_dec_ref(x_74);
x_80 = lean_ptr_addr(x_72);
x_81 = lean_usize_dec_eq(x_79, x_80);
x_16 = x_72;
x_17 = x_73;
x_18 = x_33;
x_19 = x_81;
goto block_23;
}
}
default: 
{
uint8_t x_82; 
lean_dec(x_33);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_61);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_61, 0);
lean_dec(x_83);
x_84 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3;
x_85 = l_panic___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0(x_84);
lean_ctor_set(x_61, 0, x_85);
return x_61;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_61, 1);
lean_inc(x_86);
lean_dec(x_61);
x_87 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3;
x_88 = l_panic___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_instFVarIdHashSetEmptyCollection;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Code_elimDead(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_elimDead_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_apply_6(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_2);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_apply_6(x_1, x_20, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDead___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_elimDead___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = l_Lean_Compiler_LCNF_Decl_elimDead___closed__0;
x_15 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_elimDead_spec__0(x_14, x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 4, x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 4, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
x_29 = lean_ctor_get(x_1, 4);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_32 = lean_ctor_get(x_1, 5);
lean_inc(x_32);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_33 = l_Lean_Compiler_LCNF_Decl_elimDead___closed__0;
x_34 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_elimDead_spec__0(x_33, x_29, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_26);
lean_ctor_set(x_38, 2, x_27);
lean_ctor_set(x_38, 3, x_28);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set(x_38, 5, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*6, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*6 + 1, x_31);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_32);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
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
l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__0 = _init_l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__0);
l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__1 = _init_l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__1);
l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__0 = _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__0);
l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1 = _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1);
l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__2 = _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__2);
l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3 = _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3);
l_Lean_Compiler_LCNF_Decl_elimDead___closed__0 = _init_l_Lean_Compiler_LCNF_Decl_elimDead___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_elimDead___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
