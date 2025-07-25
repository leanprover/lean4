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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__4;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_elimDead_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562____boxed(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_elimDead___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getCode(lean_object*);
extern lean_object* l_Lean_instFVarIdHashSetEmptyCollection;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__5;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3;
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_6 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_4, x_1);
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
x_7 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_4);
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
x_26 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_22);
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
x_7 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_3);
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
x_10 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_4);
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
x_55 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_51);
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
x_91 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_86);
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
x_1 = lean_alloc_closure((void*)(l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562____boxed), 1, 0);
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
x_19 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_1);
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
x_23 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_1);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_11 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_9, x_8, x_12, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_Alt_getCode(x_1);
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
lean_dec_ref(x_1);
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
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1;
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_ctor_get(x_60, 2);
x_65 = lean_ctor_get(x_60, 3);
x_66 = lean_ctor_get(x_60, 4);
x_67 = lean_ctor_get(x_60, 1);
lean_dec(x_67);
x_68 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__2;
x_69 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3;
lean_inc_ref(x_63);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_70, 0, x_63);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_71, 0, x_63);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_73, 0, x_66);
x_74 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_74, 0, x_65);
x_75 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_75, 0, x_64);
lean_ctor_set(x_60, 4, x_73);
lean_ctor_set(x_60, 3, x_74);
lean_ctor_set(x_60, 2, x_75);
lean_ctor_set(x_60, 1, x_68);
lean_ctor_set(x_60, 0, x_72);
lean_ctor_set(x_58, 1, x_69);
x_76 = l_ReaderT_instMonad___redArg(x_58);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_ctor_get(x_78, 2);
x_83 = lean_ctor_get(x_78, 3);
x_84 = lean_ctor_get(x_78, 4);
x_85 = lean_ctor_get(x_78, 1);
lean_dec(x_85);
x_86 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__4;
x_87 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__5;
lean_inc_ref(x_81);
x_88 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_88, 0, x_81);
x_89 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_89, 0, x_81);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_91, 0, x_84);
x_92 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_92, 0, x_83);
x_93 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_93, 0, x_82);
lean_ctor_set(x_78, 4, x_91);
lean_ctor_set(x_78, 3, x_92);
lean_ctor_set(x_78, 2, x_93);
lean_ctor_set(x_78, 1, x_86);
lean_ctor_set(x_78, 0, x_90);
lean_ctor_set(x_76, 1, x_87);
x_94 = l_ReaderT_instMonad___redArg(x_76);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec_ref(x_94);
x_95 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_96);
lean_inc(x_4);
lean_inc(x_2);
x_97 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_96, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; size_t x_114; size_t x_115; size_t x_116; size_t x_117; size_t x_118; lean_object* x_119; uint8_t x_120; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = lean_st_ref_get(x_2, x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
x_103 = lean_ctor_get(x_101, 1);
lean_inc_ref(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_95, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_95, 3);
lean_inc(x_105);
x_106 = lean_array_get_size(x_103);
x_107 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_104);
x_108 = 32;
x_109 = lean_uint64_shift_right(x_107, x_108);
x_110 = lean_uint64_xor(x_107, x_109);
x_111 = 16;
x_112 = lean_uint64_shift_right(x_110, x_111);
x_113 = lean_uint64_xor(x_110, x_112);
x_114 = lean_uint64_to_usize(x_113);
x_115 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_116 = 1;
x_117 = lean_usize_sub(x_115, x_116);
x_118 = lean_usize_land(x_114, x_117);
x_119 = lean_array_uget(x_103, x_118);
lean_dec_ref(x_103);
x_120 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_104, x_119);
lean_dec(x_119);
lean_dec(x_104);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
lean_dec(x_105);
lean_dec(x_2);
lean_dec_ref(x_1);
x_121 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_95, x_4, x_102);
lean_dec(x_4);
lean_dec_ref(x_95);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_121, 0);
lean_dec(x_123);
lean_ctor_set(x_121, 0, x_98);
return x_121;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_98);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec_ref(x_95);
lean_dec(x_4);
x_126 = lean_st_ref_take(x_2, x_102);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
x_129 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_127, x_105);
x_130 = lean_st_ref_set(x_2, x_129, x_128);
lean_dec(x_2);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_130, 0);
lean_dec(x_132);
x_133 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(x_1, x_98);
lean_ctor_set(x_130, 0, x_133);
return x_130;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
lean_dec(x_130);
x_135 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(x_1, x_98);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
else
{
lean_dec_ref(x_95);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_97;
}
}
case 3:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint64_t x_177; uint64_t x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; size_t x_184; size_t x_185; size_t x_186; size_t x_187; size_t x_188; lean_object* x_189; uint8_t x_190; 
lean_dec_ref(x_94);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_138);
x_139 = lean_st_ref_take(x_2, x_7);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec_ref(x_139);
x_174 = lean_ctor_get(x_140, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_140, 1);
lean_inc_ref(x_175);
x_176 = lean_array_get_size(x_175);
x_177 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_137);
x_178 = 32;
x_179 = lean_uint64_shift_right(x_177, x_178);
x_180 = lean_uint64_xor(x_177, x_179);
x_181 = 16;
x_182 = lean_uint64_shift_right(x_180, x_181);
x_183 = lean_uint64_xor(x_180, x_182);
x_184 = lean_uint64_to_usize(x_183);
x_185 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_186 = 1;
x_187 = lean_usize_sub(x_185, x_186);
x_188 = lean_usize_land(x_184, x_187);
x_189 = lean_array_uget(x_175, x_188);
x_190 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_137, x_189);
if (x_190 == 0)
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_140);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_192 = lean_ctor_get(x_140, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_140, 0);
lean_dec(x_193);
x_194 = lean_box(0);
x_195 = lean_unsigned_to_nat(1u);
x_196 = lean_nat_add(x_174, x_195);
lean_dec(x_174);
x_197 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_197, 0, x_137);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_189);
x_198 = lean_array_uset(x_175, x_188, x_197);
x_199 = lean_unsigned_to_nat(4u);
x_200 = lean_nat_mul(x_196, x_199);
x_201 = lean_unsigned_to_nat(3u);
x_202 = lean_nat_div(x_200, x_201);
lean_dec(x_200);
x_203 = lean_array_get_size(x_198);
x_204 = lean_nat_dec_le(x_202, x_203);
lean_dec(x_203);
lean_dec(x_202);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_198);
lean_ctor_set(x_140, 1, x_205);
lean_ctor_set(x_140, 0, x_196);
x_142 = x_140;
goto block_173;
}
else
{
lean_ctor_set(x_140, 1, x_198);
lean_ctor_set(x_140, 0, x_196);
x_142 = x_140;
goto block_173;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
lean_dec(x_140);
x_206 = lean_box(0);
x_207 = lean_unsigned_to_nat(1u);
x_208 = lean_nat_add(x_174, x_207);
lean_dec(x_174);
x_209 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_209, 0, x_137);
lean_ctor_set(x_209, 1, x_206);
lean_ctor_set(x_209, 2, x_189);
x_210 = lean_array_uset(x_175, x_188, x_209);
x_211 = lean_unsigned_to_nat(4u);
x_212 = lean_nat_mul(x_208, x_211);
x_213 = lean_unsigned_to_nat(3u);
x_214 = lean_nat_div(x_212, x_213);
lean_dec(x_212);
x_215 = lean_array_get_size(x_210);
x_216 = lean_nat_dec_le(x_214, x_215);
lean_dec(x_215);
lean_dec(x_214);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_210);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_208);
lean_ctor_set(x_218, 1, x_217);
x_142 = x_218;
goto block_173;
}
else
{
lean_object* x_219; 
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_208);
lean_ctor_set(x_219, 1, x_210);
x_142 = x_219;
goto block_173;
}
}
}
else
{
lean_dec(x_189);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec(x_137);
x_142 = x_140;
goto block_173;
}
block_173:
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_st_ref_set(x_2, x_142, x_141);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_143, 1);
x_146 = lean_ctor_get(x_143, 0);
lean_dec(x_146);
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_array_get_size(x_138);
x_149 = lean_nat_dec_lt(x_147, x_148);
if (x_149 == 0)
{
lean_dec(x_148);
lean_dec_ref(x_138);
lean_dec(x_2);
lean_ctor_set(x_143, 0, x_1);
return x_143;
}
else
{
uint8_t x_150; 
x_150 = lean_nat_dec_le(x_148, x_148);
if (x_150 == 0)
{
lean_dec(x_148);
lean_dec_ref(x_138);
lean_dec(x_2);
lean_ctor_set(x_143, 0, x_1);
return x_143;
}
else
{
lean_object* x_151; size_t x_152; size_t x_153; lean_object* x_154; uint8_t x_155; 
lean_free_object(x_143);
x_151 = lean_box(0);
x_152 = 0;
x_153 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_154 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_138, x_152, x_153, x_151, x_2, x_145);
lean_dec(x_2);
lean_dec_ref(x_138);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_154, 0);
lean_dec(x_156);
lean_ctor_set(x_154, 0, x_1);
return x_154;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_1);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_143, 1);
lean_inc(x_159);
lean_dec(x_143);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_array_get_size(x_138);
x_162 = lean_nat_dec_lt(x_160, x_161);
if (x_162 == 0)
{
lean_object* x_163; 
lean_dec(x_161);
lean_dec_ref(x_138);
lean_dec(x_2);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_1);
lean_ctor_set(x_163, 1, x_159);
return x_163;
}
else
{
uint8_t x_164; 
x_164 = lean_nat_dec_le(x_161, x_161);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_161);
lean_dec_ref(x_138);
lean_dec(x_2);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_1);
lean_ctor_set(x_165, 1, x_159);
return x_165;
}
else
{
lean_object* x_166; size_t x_167; size_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_box(0);
x_167 = 0;
x_168 = lean_usize_of_nat(x_161);
lean_dec(x_161);
x_169 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_138, x_167, x_168, x_166, x_2, x_159);
lean_dec(x_2);
lean_dec_ref(x_138);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_1);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
}
}
case 4:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_220 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_220);
x_221 = lean_ctor_get(x_220, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 3);
lean_inc_ref(x_222);
lean_dec_ref(x_220);
x_223 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ElimDead_elimDead___lam__0), 7, 0);
x_224 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_94, x_222, x_223);
lean_inc(x_2);
x_225 = lean_apply_6(x_224, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint64_t x_243; uint64_t x_244; uint64_t x_245; uint64_t x_246; uint64_t x_247; uint64_t x_248; uint64_t x_249; size_t x_250; size_t x_251; size_t x_252; size_t x_253; size_t x_254; lean_object* x_255; uint8_t x_256; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec_ref(x_225);
x_228 = lean_st_ref_take(x_2, x_227);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec_ref(x_228);
x_240 = lean_ctor_get(x_229, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_229, 1);
lean_inc_ref(x_241);
x_242 = lean_array_get_size(x_241);
x_243 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_221);
x_244 = 32;
x_245 = lean_uint64_shift_right(x_243, x_244);
x_246 = lean_uint64_xor(x_243, x_245);
x_247 = 16;
x_248 = lean_uint64_shift_right(x_246, x_247);
x_249 = lean_uint64_xor(x_246, x_248);
x_250 = lean_uint64_to_usize(x_249);
x_251 = lean_usize_of_nat(x_242);
lean_dec(x_242);
x_252 = 1;
x_253 = lean_usize_sub(x_251, x_252);
x_254 = lean_usize_land(x_250, x_253);
x_255 = lean_array_uget(x_241, x_254);
x_256 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_221, x_255);
if (x_256 == 0)
{
uint8_t x_257; 
x_257 = !lean_is_exclusive(x_229);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_258 = lean_ctor_get(x_229, 1);
lean_dec(x_258);
x_259 = lean_ctor_get(x_229, 0);
lean_dec(x_259);
x_260 = lean_box(0);
x_261 = lean_unsigned_to_nat(1u);
x_262 = lean_nat_add(x_240, x_261);
lean_dec(x_240);
x_263 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_263, 0, x_221);
lean_ctor_set(x_263, 1, x_260);
lean_ctor_set(x_263, 2, x_255);
x_264 = lean_array_uset(x_241, x_254, x_263);
x_265 = lean_unsigned_to_nat(4u);
x_266 = lean_nat_mul(x_262, x_265);
x_267 = lean_unsigned_to_nat(3u);
x_268 = lean_nat_div(x_266, x_267);
lean_dec(x_266);
x_269 = lean_array_get_size(x_264);
x_270 = lean_nat_dec_le(x_268, x_269);
lean_dec(x_269);
lean_dec(x_268);
if (x_270 == 0)
{
lean_object* x_271; 
x_271 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_264);
lean_ctor_set(x_229, 1, x_271);
lean_ctor_set(x_229, 0, x_262);
x_231 = x_229;
goto block_239;
}
else
{
lean_ctor_set(x_229, 1, x_264);
lean_ctor_set(x_229, 0, x_262);
x_231 = x_229;
goto block_239;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_dec(x_229);
x_272 = lean_box(0);
x_273 = lean_unsigned_to_nat(1u);
x_274 = lean_nat_add(x_240, x_273);
lean_dec(x_240);
x_275 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_275, 0, x_221);
lean_ctor_set(x_275, 1, x_272);
lean_ctor_set(x_275, 2, x_255);
x_276 = lean_array_uset(x_241, x_254, x_275);
x_277 = lean_unsigned_to_nat(4u);
x_278 = lean_nat_mul(x_274, x_277);
x_279 = lean_unsigned_to_nat(3u);
x_280 = lean_nat_div(x_278, x_279);
lean_dec(x_278);
x_281 = lean_array_get_size(x_276);
x_282 = lean_nat_dec_le(x_280, x_281);
lean_dec(x_281);
lean_dec(x_280);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_276);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_274);
lean_ctor_set(x_284, 1, x_283);
x_231 = x_284;
goto block_239;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_274);
lean_ctor_set(x_285, 1, x_276);
x_231 = x_285;
goto block_239;
}
}
}
else
{
lean_dec(x_255);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_221);
x_231 = x_229;
goto block_239;
}
block_239:
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_st_ref_set(x_2, x_231, x_230);
lean_dec(x_2);
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_232, 0);
lean_dec(x_234);
x_235 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_226);
lean_ctor_set(x_232, 0, x_235);
return x_232;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_232, 1);
lean_inc(x_236);
lean_dec(x_232);
x_237 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_226);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
}
else
{
uint8_t x_286; 
lean_dec(x_221);
lean_dec(x_2);
lean_dec_ref(x_1);
x_286 = !lean_is_exclusive(x_225);
if (x_286 == 0)
{
return x_225;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_225, 0);
x_288 = lean_ctor_get(x_225, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_225);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
}
case 5:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint64_t x_304; uint64_t x_305; uint64_t x_306; uint64_t x_307; uint64_t x_308; uint64_t x_309; uint64_t x_310; size_t x_311; size_t x_312; size_t x_313; size_t x_314; size_t x_315; lean_object* x_316; uint8_t x_317; 
lean_dec_ref(x_94);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_290 = lean_ctor_get(x_1, 0);
lean_inc(x_290);
x_291 = lean_st_ref_take(x_2, x_7);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec_ref(x_291);
x_301 = lean_ctor_get(x_292, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_292, 1);
lean_inc_ref(x_302);
x_303 = lean_array_get_size(x_302);
x_304 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_290);
x_305 = 32;
x_306 = lean_uint64_shift_right(x_304, x_305);
x_307 = lean_uint64_xor(x_304, x_306);
x_308 = 16;
x_309 = lean_uint64_shift_right(x_307, x_308);
x_310 = lean_uint64_xor(x_307, x_309);
x_311 = lean_uint64_to_usize(x_310);
x_312 = lean_usize_of_nat(x_303);
lean_dec(x_303);
x_313 = 1;
x_314 = lean_usize_sub(x_312, x_313);
x_315 = lean_usize_land(x_311, x_314);
x_316 = lean_array_uget(x_302, x_315);
x_317 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_290, x_316);
if (x_317 == 0)
{
uint8_t x_318; 
x_318 = !lean_is_exclusive(x_292);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_319 = lean_ctor_get(x_292, 1);
lean_dec(x_319);
x_320 = lean_ctor_get(x_292, 0);
lean_dec(x_320);
x_321 = lean_box(0);
x_322 = lean_unsigned_to_nat(1u);
x_323 = lean_nat_add(x_301, x_322);
lean_dec(x_301);
x_324 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_324, 0, x_290);
lean_ctor_set(x_324, 1, x_321);
lean_ctor_set(x_324, 2, x_316);
x_325 = lean_array_uset(x_302, x_315, x_324);
x_326 = lean_unsigned_to_nat(4u);
x_327 = lean_nat_mul(x_323, x_326);
x_328 = lean_unsigned_to_nat(3u);
x_329 = lean_nat_div(x_327, x_328);
lean_dec(x_327);
x_330 = lean_array_get_size(x_325);
x_331 = lean_nat_dec_le(x_329, x_330);
lean_dec(x_330);
lean_dec(x_329);
if (x_331 == 0)
{
lean_object* x_332; 
x_332 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_325);
lean_ctor_set(x_292, 1, x_332);
lean_ctor_set(x_292, 0, x_323);
x_294 = x_292;
goto block_300;
}
else
{
lean_ctor_set(x_292, 1, x_325);
lean_ctor_set(x_292, 0, x_323);
x_294 = x_292;
goto block_300;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
lean_dec(x_292);
x_333 = lean_box(0);
x_334 = lean_unsigned_to_nat(1u);
x_335 = lean_nat_add(x_301, x_334);
lean_dec(x_301);
x_336 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_336, 0, x_290);
lean_ctor_set(x_336, 1, x_333);
lean_ctor_set(x_336, 2, x_316);
x_337 = lean_array_uset(x_302, x_315, x_336);
x_338 = lean_unsigned_to_nat(4u);
x_339 = lean_nat_mul(x_335, x_338);
x_340 = lean_unsigned_to_nat(3u);
x_341 = lean_nat_div(x_339, x_340);
lean_dec(x_339);
x_342 = lean_array_get_size(x_337);
x_343 = lean_nat_dec_le(x_341, x_342);
lean_dec(x_342);
lean_dec(x_341);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; 
x_344 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_337);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_335);
lean_ctor_set(x_345, 1, x_344);
x_294 = x_345;
goto block_300;
}
else
{
lean_object* x_346; 
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_335);
lean_ctor_set(x_346, 1, x_337);
x_294 = x_346;
goto block_300;
}
}
}
else
{
lean_dec(x_316);
lean_dec_ref(x_302);
lean_dec(x_301);
lean_dec(x_290);
x_294 = x_292;
goto block_300;
}
block_300:
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_st_ref_set(x_2, x_294, x_293);
lean_dec(x_2);
x_296 = !lean_is_exclusive(x_295);
if (x_296 == 0)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_295, 0);
lean_dec(x_297);
lean_ctor_set(x_295, 0, x_1);
return x_295;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
lean_dec(x_295);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_1);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
case 6:
{
lean_object* x_347; 
lean_dec_ref(x_94);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_1);
lean_ctor_set(x_347, 1, x_7);
return x_347;
}
default: 
{
lean_object* x_348; lean_object* x_349; 
lean_dec_ref(x_94);
x_348 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_348);
x_349 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_349);
x_8 = x_348;
x_9 = x_349;
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
goto block_57;
}
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_350 = lean_ctor_get(x_78, 0);
x_351 = lean_ctor_get(x_78, 2);
x_352 = lean_ctor_get(x_78, 3);
x_353 = lean_ctor_get(x_78, 4);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_78);
x_354 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__4;
x_355 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__5;
lean_inc_ref(x_350);
x_356 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_356, 0, x_350);
x_357 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_357, 0, x_350);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
x_359 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_359, 0, x_353);
x_360 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_360, 0, x_352);
x_361 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_361, 0, x_351);
x_362 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_362, 0, x_358);
lean_ctor_set(x_362, 1, x_354);
lean_ctor_set(x_362, 2, x_361);
lean_ctor_set(x_362, 3, x_360);
lean_ctor_set(x_362, 4, x_359);
lean_ctor_set(x_76, 1, x_355);
lean_ctor_set(x_76, 0, x_362);
x_363 = l_ReaderT_instMonad___redArg(x_76);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec_ref(x_363);
x_364 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_364);
x_365 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_365);
lean_inc(x_4);
lean_inc(x_2);
x_366 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_365, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint64_t x_376; uint64_t x_377; uint64_t x_378; uint64_t x_379; uint64_t x_380; uint64_t x_381; uint64_t x_382; size_t x_383; size_t x_384; size_t x_385; size_t x_386; size_t x_387; lean_object* x_388; uint8_t x_389; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec_ref(x_366);
x_369 = lean_st_ref_get(x_2, x_368);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec_ref(x_369);
x_372 = lean_ctor_get(x_370, 1);
lean_inc_ref(x_372);
lean_dec(x_370);
x_373 = lean_ctor_get(x_364, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_364, 3);
lean_inc(x_374);
x_375 = lean_array_get_size(x_372);
x_376 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_373);
x_377 = 32;
x_378 = lean_uint64_shift_right(x_376, x_377);
x_379 = lean_uint64_xor(x_376, x_378);
x_380 = 16;
x_381 = lean_uint64_shift_right(x_379, x_380);
x_382 = lean_uint64_xor(x_379, x_381);
x_383 = lean_uint64_to_usize(x_382);
x_384 = lean_usize_of_nat(x_375);
lean_dec(x_375);
x_385 = 1;
x_386 = lean_usize_sub(x_384, x_385);
x_387 = lean_usize_land(x_383, x_386);
x_388 = lean_array_uget(x_372, x_387);
lean_dec_ref(x_372);
x_389 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_373, x_388);
lean_dec(x_388);
lean_dec(x_373);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_374);
lean_dec(x_2);
lean_dec_ref(x_1);
x_390 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_364, x_4, x_371);
lean_dec(x_4);
lean_dec_ref(x_364);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_392 = x_390;
} else {
 lean_dec_ref(x_390);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_367);
lean_ctor_set(x_393, 1, x_391);
return x_393;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec_ref(x_364);
lean_dec(x_4);
x_394 = lean_st_ref_take(x_2, x_371);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec_ref(x_394);
x_397 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_395, x_374);
x_398 = lean_st_ref_set(x_2, x_397, x_396);
lean_dec(x_2);
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_400 = x_398;
} else {
 lean_dec_ref(x_398);
 x_400 = lean_box(0);
}
x_401 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(x_1, x_367);
if (lean_is_scalar(x_400)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_400;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_399);
return x_402;
}
}
else
{
lean_dec_ref(x_364);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_366;
}
}
case 3:
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint64_t x_429; uint64_t x_430; uint64_t x_431; uint64_t x_432; uint64_t x_433; uint64_t x_434; uint64_t x_435; size_t x_436; size_t x_437; size_t x_438; size_t x_439; size_t x_440; lean_object* x_441; uint8_t x_442; 
lean_dec_ref(x_363);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_403 = lean_ctor_get(x_1, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_404);
x_405 = lean_st_ref_take(x_2, x_7);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec_ref(x_405);
x_426 = lean_ctor_get(x_406, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_406, 1);
lean_inc_ref(x_427);
x_428 = lean_array_get_size(x_427);
x_429 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_403);
x_430 = 32;
x_431 = lean_uint64_shift_right(x_429, x_430);
x_432 = lean_uint64_xor(x_429, x_431);
x_433 = 16;
x_434 = lean_uint64_shift_right(x_432, x_433);
x_435 = lean_uint64_xor(x_432, x_434);
x_436 = lean_uint64_to_usize(x_435);
x_437 = lean_usize_of_nat(x_428);
lean_dec(x_428);
x_438 = 1;
x_439 = lean_usize_sub(x_437, x_438);
x_440 = lean_usize_land(x_436, x_439);
x_441 = lean_array_uget(x_427, x_440);
x_442 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_403, x_441);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_443 = x_406;
} else {
 lean_dec_ref(x_406);
 x_443 = lean_box(0);
}
x_444 = lean_box(0);
x_445 = lean_unsigned_to_nat(1u);
x_446 = lean_nat_add(x_426, x_445);
lean_dec(x_426);
x_447 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_447, 0, x_403);
lean_ctor_set(x_447, 1, x_444);
lean_ctor_set(x_447, 2, x_441);
x_448 = lean_array_uset(x_427, x_440, x_447);
x_449 = lean_unsigned_to_nat(4u);
x_450 = lean_nat_mul(x_446, x_449);
x_451 = lean_unsigned_to_nat(3u);
x_452 = lean_nat_div(x_450, x_451);
lean_dec(x_450);
x_453 = lean_array_get_size(x_448);
x_454 = lean_nat_dec_le(x_452, x_453);
lean_dec(x_453);
lean_dec(x_452);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; 
x_455 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_448);
if (lean_is_scalar(x_443)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_443;
}
lean_ctor_set(x_456, 0, x_446);
lean_ctor_set(x_456, 1, x_455);
x_408 = x_456;
goto block_425;
}
else
{
lean_object* x_457; 
if (lean_is_scalar(x_443)) {
 x_457 = lean_alloc_ctor(0, 2, 0);
} else {
 x_457 = x_443;
}
lean_ctor_set(x_457, 0, x_446);
lean_ctor_set(x_457, 1, x_448);
x_408 = x_457;
goto block_425;
}
}
else
{
lean_dec(x_441);
lean_dec_ref(x_427);
lean_dec(x_426);
lean_dec(x_403);
x_408 = x_406;
goto block_425;
}
block_425:
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; 
x_409 = lean_st_ref_set(x_2, x_408, x_407);
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_411 = x_409;
} else {
 lean_dec_ref(x_409);
 x_411 = lean_box(0);
}
x_412 = lean_unsigned_to_nat(0u);
x_413 = lean_array_get_size(x_404);
x_414 = lean_nat_dec_lt(x_412, x_413);
if (x_414 == 0)
{
lean_object* x_415; 
lean_dec(x_413);
lean_dec_ref(x_404);
lean_dec(x_2);
if (lean_is_scalar(x_411)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_411;
}
lean_ctor_set(x_415, 0, x_1);
lean_ctor_set(x_415, 1, x_410);
return x_415;
}
else
{
uint8_t x_416; 
x_416 = lean_nat_dec_le(x_413, x_413);
if (x_416 == 0)
{
lean_object* x_417; 
lean_dec(x_413);
lean_dec_ref(x_404);
lean_dec(x_2);
if (lean_is_scalar(x_411)) {
 x_417 = lean_alloc_ctor(0, 2, 0);
} else {
 x_417 = x_411;
}
lean_ctor_set(x_417, 0, x_1);
lean_ctor_set(x_417, 1, x_410);
return x_417;
}
else
{
lean_object* x_418; size_t x_419; size_t x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_411);
x_418 = lean_box(0);
x_419 = 0;
x_420 = lean_usize_of_nat(x_413);
lean_dec(x_413);
x_421 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_404, x_419, x_420, x_418, x_2, x_410);
lean_dec(x_2);
lean_dec_ref(x_404);
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_423 = x_421;
} else {
 lean_dec_ref(x_421);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_1);
lean_ctor_set(x_424, 1, x_422);
return x_424;
}
}
}
}
case 4:
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_458 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_458);
x_459 = lean_ctor_get(x_458, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 3);
lean_inc_ref(x_460);
lean_dec_ref(x_458);
x_461 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ElimDead_elimDead___lam__0), 7, 0);
x_462 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_363, x_460, x_461);
lean_inc(x_2);
x_463 = lean_apply_6(x_462, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint64_t x_479; uint64_t x_480; uint64_t x_481; uint64_t x_482; uint64_t x_483; uint64_t x_484; uint64_t x_485; size_t x_486; size_t x_487; size_t x_488; size_t x_489; size_t x_490; lean_object* x_491; uint8_t x_492; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec_ref(x_463);
x_466 = lean_st_ref_take(x_2, x_465);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec_ref(x_466);
x_476 = lean_ctor_get(x_467, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_467, 1);
lean_inc_ref(x_477);
x_478 = lean_array_get_size(x_477);
x_479 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_459);
x_480 = 32;
x_481 = lean_uint64_shift_right(x_479, x_480);
x_482 = lean_uint64_xor(x_479, x_481);
x_483 = 16;
x_484 = lean_uint64_shift_right(x_482, x_483);
x_485 = lean_uint64_xor(x_482, x_484);
x_486 = lean_uint64_to_usize(x_485);
x_487 = lean_usize_of_nat(x_478);
lean_dec(x_478);
x_488 = 1;
x_489 = lean_usize_sub(x_487, x_488);
x_490 = lean_usize_land(x_486, x_489);
x_491 = lean_array_uget(x_477, x_490);
x_492 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_459, x_491);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; 
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_493 = x_467;
} else {
 lean_dec_ref(x_467);
 x_493 = lean_box(0);
}
x_494 = lean_box(0);
x_495 = lean_unsigned_to_nat(1u);
x_496 = lean_nat_add(x_476, x_495);
lean_dec(x_476);
x_497 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_497, 0, x_459);
lean_ctor_set(x_497, 1, x_494);
lean_ctor_set(x_497, 2, x_491);
x_498 = lean_array_uset(x_477, x_490, x_497);
x_499 = lean_unsigned_to_nat(4u);
x_500 = lean_nat_mul(x_496, x_499);
x_501 = lean_unsigned_to_nat(3u);
x_502 = lean_nat_div(x_500, x_501);
lean_dec(x_500);
x_503 = lean_array_get_size(x_498);
x_504 = lean_nat_dec_le(x_502, x_503);
lean_dec(x_503);
lean_dec(x_502);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_498);
if (lean_is_scalar(x_493)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_493;
}
lean_ctor_set(x_506, 0, x_496);
lean_ctor_set(x_506, 1, x_505);
x_469 = x_506;
goto block_475;
}
else
{
lean_object* x_507; 
if (lean_is_scalar(x_493)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_493;
}
lean_ctor_set(x_507, 0, x_496);
lean_ctor_set(x_507, 1, x_498);
x_469 = x_507;
goto block_475;
}
}
else
{
lean_dec(x_491);
lean_dec_ref(x_477);
lean_dec(x_476);
lean_dec(x_459);
x_469 = x_467;
goto block_475;
}
block_475:
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_470 = lean_st_ref_set(x_2, x_469, x_468);
lean_dec(x_2);
x_471 = lean_ctor_get(x_470, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_472 = x_470;
} else {
 lean_dec_ref(x_470);
 x_472 = lean_box(0);
}
x_473 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_464);
if (lean_is_scalar(x_472)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_472;
}
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_471);
return x_474;
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_459);
lean_dec(x_2);
lean_dec_ref(x_1);
x_508 = lean_ctor_get(x_463, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_463, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_510 = x_463;
} else {
 lean_dec_ref(x_463);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_509);
return x_511;
}
}
case 5:
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_522; lean_object* x_523; lean_object* x_524; uint64_t x_525; uint64_t x_526; uint64_t x_527; uint64_t x_528; uint64_t x_529; uint64_t x_530; uint64_t x_531; size_t x_532; size_t x_533; size_t x_534; size_t x_535; size_t x_536; lean_object* x_537; uint8_t x_538; 
lean_dec_ref(x_363);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_512 = lean_ctor_get(x_1, 0);
lean_inc(x_512);
x_513 = lean_st_ref_take(x_2, x_7);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec_ref(x_513);
x_522 = lean_ctor_get(x_514, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_514, 1);
lean_inc_ref(x_523);
x_524 = lean_array_get_size(x_523);
x_525 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_512);
x_526 = 32;
x_527 = lean_uint64_shift_right(x_525, x_526);
x_528 = lean_uint64_xor(x_525, x_527);
x_529 = 16;
x_530 = lean_uint64_shift_right(x_528, x_529);
x_531 = lean_uint64_xor(x_528, x_530);
x_532 = lean_uint64_to_usize(x_531);
x_533 = lean_usize_of_nat(x_524);
lean_dec(x_524);
x_534 = 1;
x_535 = lean_usize_sub(x_533, x_534);
x_536 = lean_usize_land(x_532, x_535);
x_537 = lean_array_uget(x_523, x_536);
x_538 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_512, x_537);
if (x_538 == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; uint8_t x_550; 
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 x_539 = x_514;
} else {
 lean_dec_ref(x_514);
 x_539 = lean_box(0);
}
x_540 = lean_box(0);
x_541 = lean_unsigned_to_nat(1u);
x_542 = lean_nat_add(x_522, x_541);
lean_dec(x_522);
x_543 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_543, 0, x_512);
lean_ctor_set(x_543, 1, x_540);
lean_ctor_set(x_543, 2, x_537);
x_544 = lean_array_uset(x_523, x_536, x_543);
x_545 = lean_unsigned_to_nat(4u);
x_546 = lean_nat_mul(x_542, x_545);
x_547 = lean_unsigned_to_nat(3u);
x_548 = lean_nat_div(x_546, x_547);
lean_dec(x_546);
x_549 = lean_array_get_size(x_544);
x_550 = lean_nat_dec_le(x_548, x_549);
lean_dec(x_549);
lean_dec(x_548);
if (x_550 == 0)
{
lean_object* x_551; lean_object* x_552; 
x_551 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_544);
if (lean_is_scalar(x_539)) {
 x_552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_552 = x_539;
}
lean_ctor_set(x_552, 0, x_542);
lean_ctor_set(x_552, 1, x_551);
x_516 = x_552;
goto block_521;
}
else
{
lean_object* x_553; 
if (lean_is_scalar(x_539)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_539;
}
lean_ctor_set(x_553, 0, x_542);
lean_ctor_set(x_553, 1, x_544);
x_516 = x_553;
goto block_521;
}
}
else
{
lean_dec(x_537);
lean_dec_ref(x_523);
lean_dec(x_522);
lean_dec(x_512);
x_516 = x_514;
goto block_521;
}
block_521:
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_517 = lean_st_ref_set(x_2, x_516, x_515);
lean_dec(x_2);
x_518 = lean_ctor_get(x_517, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 lean_ctor_release(x_517, 1);
 x_519 = x_517;
} else {
 lean_dec_ref(x_517);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(0, 2, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_1);
lean_ctor_set(x_520, 1, x_518);
return x_520;
}
}
case 6:
{
lean_object* x_554; 
lean_dec_ref(x_363);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_554 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_554, 0, x_1);
lean_ctor_set(x_554, 1, x_7);
return x_554;
}
default: 
{
lean_object* x_555; lean_object* x_556; 
lean_dec_ref(x_363);
x_555 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_555);
x_556 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_556);
x_8 = x_555;
x_9 = x_556;
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
goto block_57;
}
}
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_557 = lean_ctor_get(x_76, 0);
lean_inc(x_557);
lean_dec(x_76);
x_558 = lean_ctor_get(x_557, 0);
lean_inc_ref(x_558);
x_559 = lean_ctor_get(x_557, 2);
lean_inc_ref(x_559);
x_560 = lean_ctor_get(x_557, 3);
lean_inc_ref(x_560);
x_561 = lean_ctor_get(x_557, 4);
lean_inc_ref(x_561);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 lean_ctor_release(x_557, 2);
 lean_ctor_release(x_557, 3);
 lean_ctor_release(x_557, 4);
 x_562 = x_557;
} else {
 lean_dec_ref(x_557);
 x_562 = lean_box(0);
}
x_563 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__4;
x_564 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__5;
lean_inc_ref(x_558);
x_565 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_565, 0, x_558);
x_566 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_566, 0, x_558);
x_567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_566);
x_568 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_568, 0, x_561);
x_569 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_569, 0, x_560);
x_570 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_570, 0, x_559);
if (lean_is_scalar(x_562)) {
 x_571 = lean_alloc_ctor(0, 5, 0);
} else {
 x_571 = x_562;
}
lean_ctor_set(x_571, 0, x_567);
lean_ctor_set(x_571, 1, x_563);
lean_ctor_set(x_571, 2, x_570);
lean_ctor_set(x_571, 3, x_569);
lean_ctor_set(x_571, 4, x_568);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_571);
lean_ctor_set(x_572, 1, x_564);
x_573 = l_ReaderT_instMonad___redArg(x_572);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec_ref(x_573);
x_574 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_574);
x_575 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_575);
lean_inc(x_4);
lean_inc(x_2);
x_576 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_575, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; uint64_t x_586; uint64_t x_587; uint64_t x_588; uint64_t x_589; uint64_t x_590; uint64_t x_591; uint64_t x_592; size_t x_593; size_t x_594; size_t x_595; size_t x_596; size_t x_597; lean_object* x_598; uint8_t x_599; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec_ref(x_576);
x_579 = lean_st_ref_get(x_2, x_578);
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
lean_dec_ref(x_579);
x_582 = lean_ctor_get(x_580, 1);
lean_inc_ref(x_582);
lean_dec(x_580);
x_583 = lean_ctor_get(x_574, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_574, 3);
lean_inc(x_584);
x_585 = lean_array_get_size(x_582);
x_586 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_583);
x_587 = 32;
x_588 = lean_uint64_shift_right(x_586, x_587);
x_589 = lean_uint64_xor(x_586, x_588);
x_590 = 16;
x_591 = lean_uint64_shift_right(x_589, x_590);
x_592 = lean_uint64_xor(x_589, x_591);
x_593 = lean_uint64_to_usize(x_592);
x_594 = lean_usize_of_nat(x_585);
lean_dec(x_585);
x_595 = 1;
x_596 = lean_usize_sub(x_594, x_595);
x_597 = lean_usize_land(x_593, x_596);
x_598 = lean_array_uget(x_582, x_597);
lean_dec_ref(x_582);
x_599 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_583, x_598);
lean_dec(x_598);
lean_dec(x_583);
if (x_599 == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_584);
lean_dec(x_2);
lean_dec_ref(x_1);
x_600 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_574, x_4, x_581);
lean_dec(x_4);
lean_dec_ref(x_574);
x_601 = lean_ctor_get(x_600, 1);
lean_inc(x_601);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_602 = x_600;
} else {
 lean_dec_ref(x_600);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_577);
lean_ctor_set(x_603, 1, x_601);
return x_603;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec_ref(x_574);
lean_dec(x_4);
x_604 = lean_st_ref_take(x_2, x_581);
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
lean_dec_ref(x_604);
x_607 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_605, x_584);
x_608 = lean_st_ref_set(x_2, x_607, x_606);
lean_dec(x_2);
x_609 = lean_ctor_get(x_608, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_610 = x_608;
} else {
 lean_dec_ref(x_608);
 x_610 = lean_box(0);
}
x_611 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(x_1, x_577);
if (lean_is_scalar(x_610)) {
 x_612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_612 = x_610;
}
lean_ctor_set(x_612, 0, x_611);
lean_ctor_set(x_612, 1, x_609);
return x_612;
}
}
else
{
lean_dec_ref(x_574);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_576;
}
}
case 3:
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_636; lean_object* x_637; lean_object* x_638; uint64_t x_639; uint64_t x_640; uint64_t x_641; uint64_t x_642; uint64_t x_643; uint64_t x_644; uint64_t x_645; size_t x_646; size_t x_647; size_t x_648; size_t x_649; size_t x_650; lean_object* x_651; uint8_t x_652; 
lean_dec_ref(x_573);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_613 = lean_ctor_get(x_1, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_614);
x_615 = lean_st_ref_take(x_2, x_7);
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
lean_dec_ref(x_615);
x_636 = lean_ctor_get(x_616, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_616, 1);
lean_inc_ref(x_637);
x_638 = lean_array_get_size(x_637);
x_639 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_613);
x_640 = 32;
x_641 = lean_uint64_shift_right(x_639, x_640);
x_642 = lean_uint64_xor(x_639, x_641);
x_643 = 16;
x_644 = lean_uint64_shift_right(x_642, x_643);
x_645 = lean_uint64_xor(x_642, x_644);
x_646 = lean_uint64_to_usize(x_645);
x_647 = lean_usize_of_nat(x_638);
lean_dec(x_638);
x_648 = 1;
x_649 = lean_usize_sub(x_647, x_648);
x_650 = lean_usize_land(x_646, x_649);
x_651 = lean_array_uget(x_637, x_650);
x_652 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_613, x_651);
if (x_652 == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; uint8_t x_664; 
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_653 = x_616;
} else {
 lean_dec_ref(x_616);
 x_653 = lean_box(0);
}
x_654 = lean_box(0);
x_655 = lean_unsigned_to_nat(1u);
x_656 = lean_nat_add(x_636, x_655);
lean_dec(x_636);
x_657 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_657, 0, x_613);
lean_ctor_set(x_657, 1, x_654);
lean_ctor_set(x_657, 2, x_651);
x_658 = lean_array_uset(x_637, x_650, x_657);
x_659 = lean_unsigned_to_nat(4u);
x_660 = lean_nat_mul(x_656, x_659);
x_661 = lean_unsigned_to_nat(3u);
x_662 = lean_nat_div(x_660, x_661);
lean_dec(x_660);
x_663 = lean_array_get_size(x_658);
x_664 = lean_nat_dec_le(x_662, x_663);
lean_dec(x_663);
lean_dec(x_662);
if (x_664 == 0)
{
lean_object* x_665; lean_object* x_666; 
x_665 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_658);
if (lean_is_scalar(x_653)) {
 x_666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_666 = x_653;
}
lean_ctor_set(x_666, 0, x_656);
lean_ctor_set(x_666, 1, x_665);
x_618 = x_666;
goto block_635;
}
else
{
lean_object* x_667; 
if (lean_is_scalar(x_653)) {
 x_667 = lean_alloc_ctor(0, 2, 0);
} else {
 x_667 = x_653;
}
lean_ctor_set(x_667, 0, x_656);
lean_ctor_set(x_667, 1, x_658);
x_618 = x_667;
goto block_635;
}
}
else
{
lean_dec(x_651);
lean_dec_ref(x_637);
lean_dec(x_636);
lean_dec(x_613);
x_618 = x_616;
goto block_635;
}
block_635:
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
x_619 = lean_st_ref_set(x_2, x_618, x_617);
x_620 = lean_ctor_get(x_619, 1);
lean_inc(x_620);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_621 = x_619;
} else {
 lean_dec_ref(x_619);
 x_621 = lean_box(0);
}
x_622 = lean_unsigned_to_nat(0u);
x_623 = lean_array_get_size(x_614);
x_624 = lean_nat_dec_lt(x_622, x_623);
if (x_624 == 0)
{
lean_object* x_625; 
lean_dec(x_623);
lean_dec_ref(x_614);
lean_dec(x_2);
if (lean_is_scalar(x_621)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_621;
}
lean_ctor_set(x_625, 0, x_1);
lean_ctor_set(x_625, 1, x_620);
return x_625;
}
else
{
uint8_t x_626; 
x_626 = lean_nat_dec_le(x_623, x_623);
if (x_626 == 0)
{
lean_object* x_627; 
lean_dec(x_623);
lean_dec_ref(x_614);
lean_dec(x_2);
if (lean_is_scalar(x_621)) {
 x_627 = lean_alloc_ctor(0, 2, 0);
} else {
 x_627 = x_621;
}
lean_ctor_set(x_627, 0, x_1);
lean_ctor_set(x_627, 1, x_620);
return x_627;
}
else
{
lean_object* x_628; size_t x_629; size_t x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_621);
x_628 = lean_box(0);
x_629 = 0;
x_630 = lean_usize_of_nat(x_623);
lean_dec(x_623);
x_631 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_614, x_629, x_630, x_628, x_2, x_620);
lean_dec(x_2);
lean_dec_ref(x_614);
x_632 = lean_ctor_get(x_631, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_633 = x_631;
} else {
 lean_dec_ref(x_631);
 x_633 = lean_box(0);
}
if (lean_is_scalar(x_633)) {
 x_634 = lean_alloc_ctor(0, 2, 0);
} else {
 x_634 = x_633;
}
lean_ctor_set(x_634, 0, x_1);
lean_ctor_set(x_634, 1, x_632);
return x_634;
}
}
}
}
case 4:
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_668 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_668);
x_669 = lean_ctor_get(x_668, 2);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 3);
lean_inc_ref(x_670);
lean_dec_ref(x_668);
x_671 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ElimDead_elimDead___lam__0), 7, 0);
x_672 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_573, x_670, x_671);
lean_inc(x_2);
x_673 = lean_apply_6(x_672, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_673) == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_686; lean_object* x_687; lean_object* x_688; uint64_t x_689; uint64_t x_690; uint64_t x_691; uint64_t x_692; uint64_t x_693; uint64_t x_694; uint64_t x_695; size_t x_696; size_t x_697; size_t x_698; size_t x_699; size_t x_700; lean_object* x_701; uint8_t x_702; 
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
lean_dec_ref(x_673);
x_676 = lean_st_ref_take(x_2, x_675);
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec_ref(x_676);
x_686 = lean_ctor_get(x_677, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_677, 1);
lean_inc_ref(x_687);
x_688 = lean_array_get_size(x_687);
x_689 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_669);
x_690 = 32;
x_691 = lean_uint64_shift_right(x_689, x_690);
x_692 = lean_uint64_xor(x_689, x_691);
x_693 = 16;
x_694 = lean_uint64_shift_right(x_692, x_693);
x_695 = lean_uint64_xor(x_692, x_694);
x_696 = lean_uint64_to_usize(x_695);
x_697 = lean_usize_of_nat(x_688);
lean_dec(x_688);
x_698 = 1;
x_699 = lean_usize_sub(x_697, x_698);
x_700 = lean_usize_land(x_696, x_699);
x_701 = lean_array_uget(x_687, x_700);
x_702 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_669, x_701);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; uint8_t x_714; 
if (lean_is_exclusive(x_677)) {
 lean_ctor_release(x_677, 0);
 lean_ctor_release(x_677, 1);
 x_703 = x_677;
} else {
 lean_dec_ref(x_677);
 x_703 = lean_box(0);
}
x_704 = lean_box(0);
x_705 = lean_unsigned_to_nat(1u);
x_706 = lean_nat_add(x_686, x_705);
lean_dec(x_686);
x_707 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_707, 0, x_669);
lean_ctor_set(x_707, 1, x_704);
lean_ctor_set(x_707, 2, x_701);
x_708 = lean_array_uset(x_687, x_700, x_707);
x_709 = lean_unsigned_to_nat(4u);
x_710 = lean_nat_mul(x_706, x_709);
x_711 = lean_unsigned_to_nat(3u);
x_712 = lean_nat_div(x_710, x_711);
lean_dec(x_710);
x_713 = lean_array_get_size(x_708);
x_714 = lean_nat_dec_le(x_712, x_713);
lean_dec(x_713);
lean_dec(x_712);
if (x_714 == 0)
{
lean_object* x_715; lean_object* x_716; 
x_715 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_708);
if (lean_is_scalar(x_703)) {
 x_716 = lean_alloc_ctor(0, 2, 0);
} else {
 x_716 = x_703;
}
lean_ctor_set(x_716, 0, x_706);
lean_ctor_set(x_716, 1, x_715);
x_679 = x_716;
goto block_685;
}
else
{
lean_object* x_717; 
if (lean_is_scalar(x_703)) {
 x_717 = lean_alloc_ctor(0, 2, 0);
} else {
 x_717 = x_703;
}
lean_ctor_set(x_717, 0, x_706);
lean_ctor_set(x_717, 1, x_708);
x_679 = x_717;
goto block_685;
}
}
else
{
lean_dec(x_701);
lean_dec_ref(x_687);
lean_dec(x_686);
lean_dec(x_669);
x_679 = x_677;
goto block_685;
}
block_685:
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_680 = lean_st_ref_set(x_2, x_679, x_678);
lean_dec(x_2);
x_681 = lean_ctor_get(x_680, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_682 = x_680;
} else {
 lean_dec_ref(x_680);
 x_682 = lean_box(0);
}
x_683 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_674);
if (lean_is_scalar(x_682)) {
 x_684 = lean_alloc_ctor(0, 2, 0);
} else {
 x_684 = x_682;
}
lean_ctor_set(x_684, 0, x_683);
lean_ctor_set(x_684, 1, x_681);
return x_684;
}
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec(x_669);
lean_dec(x_2);
lean_dec_ref(x_1);
x_718 = lean_ctor_get(x_673, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_673, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 x_720 = x_673;
} else {
 lean_dec_ref(x_673);
 x_720 = lean_box(0);
}
if (lean_is_scalar(x_720)) {
 x_721 = lean_alloc_ctor(1, 2, 0);
} else {
 x_721 = x_720;
}
lean_ctor_set(x_721, 0, x_718);
lean_ctor_set(x_721, 1, x_719);
return x_721;
}
}
case 5:
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_732; lean_object* x_733; lean_object* x_734; uint64_t x_735; uint64_t x_736; uint64_t x_737; uint64_t x_738; uint64_t x_739; uint64_t x_740; uint64_t x_741; size_t x_742; size_t x_743; size_t x_744; size_t x_745; size_t x_746; lean_object* x_747; uint8_t x_748; 
lean_dec_ref(x_573);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_722 = lean_ctor_get(x_1, 0);
lean_inc(x_722);
x_723 = lean_st_ref_take(x_2, x_7);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec_ref(x_723);
x_732 = lean_ctor_get(x_724, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_724, 1);
lean_inc_ref(x_733);
x_734 = lean_array_get_size(x_733);
x_735 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_722);
x_736 = 32;
x_737 = lean_uint64_shift_right(x_735, x_736);
x_738 = lean_uint64_xor(x_735, x_737);
x_739 = 16;
x_740 = lean_uint64_shift_right(x_738, x_739);
x_741 = lean_uint64_xor(x_738, x_740);
x_742 = lean_uint64_to_usize(x_741);
x_743 = lean_usize_of_nat(x_734);
lean_dec(x_734);
x_744 = 1;
x_745 = lean_usize_sub(x_743, x_744);
x_746 = lean_usize_land(x_742, x_745);
x_747 = lean_array_uget(x_733, x_746);
x_748 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_722, x_747);
if (x_748 == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; uint8_t x_760; 
if (lean_is_exclusive(x_724)) {
 lean_ctor_release(x_724, 0);
 lean_ctor_release(x_724, 1);
 x_749 = x_724;
} else {
 lean_dec_ref(x_724);
 x_749 = lean_box(0);
}
x_750 = lean_box(0);
x_751 = lean_unsigned_to_nat(1u);
x_752 = lean_nat_add(x_732, x_751);
lean_dec(x_732);
x_753 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_753, 0, x_722);
lean_ctor_set(x_753, 1, x_750);
lean_ctor_set(x_753, 2, x_747);
x_754 = lean_array_uset(x_733, x_746, x_753);
x_755 = lean_unsigned_to_nat(4u);
x_756 = lean_nat_mul(x_752, x_755);
x_757 = lean_unsigned_to_nat(3u);
x_758 = lean_nat_div(x_756, x_757);
lean_dec(x_756);
x_759 = lean_array_get_size(x_754);
x_760 = lean_nat_dec_le(x_758, x_759);
lean_dec(x_759);
lean_dec(x_758);
if (x_760 == 0)
{
lean_object* x_761; lean_object* x_762; 
x_761 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_754);
if (lean_is_scalar(x_749)) {
 x_762 = lean_alloc_ctor(0, 2, 0);
} else {
 x_762 = x_749;
}
lean_ctor_set(x_762, 0, x_752);
lean_ctor_set(x_762, 1, x_761);
x_726 = x_762;
goto block_731;
}
else
{
lean_object* x_763; 
if (lean_is_scalar(x_749)) {
 x_763 = lean_alloc_ctor(0, 2, 0);
} else {
 x_763 = x_749;
}
lean_ctor_set(x_763, 0, x_752);
lean_ctor_set(x_763, 1, x_754);
x_726 = x_763;
goto block_731;
}
}
else
{
lean_dec(x_747);
lean_dec_ref(x_733);
lean_dec(x_732);
lean_dec(x_722);
x_726 = x_724;
goto block_731;
}
block_731:
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_727 = lean_st_ref_set(x_2, x_726, x_725);
lean_dec(x_2);
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_729 = x_727;
} else {
 lean_dec_ref(x_727);
 x_729 = lean_box(0);
}
if (lean_is_scalar(x_729)) {
 x_730 = lean_alloc_ctor(0, 2, 0);
} else {
 x_730 = x_729;
}
lean_ctor_set(x_730, 0, x_1);
lean_ctor_set(x_730, 1, x_728);
return x_730;
}
}
case 6:
{
lean_object* x_764; 
lean_dec_ref(x_573);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_764 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_764, 0, x_1);
lean_ctor_set(x_764, 1, x_7);
return x_764;
}
default: 
{
lean_object* x_765; lean_object* x_766; 
lean_dec_ref(x_573);
x_765 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_765);
x_766 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_766);
x_8 = x_765;
x_9 = x_766;
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
goto block_57;
}
}
}
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_767 = lean_ctor_get(x_60, 0);
x_768 = lean_ctor_get(x_60, 2);
x_769 = lean_ctor_get(x_60, 3);
x_770 = lean_ctor_get(x_60, 4);
lean_inc(x_770);
lean_inc(x_769);
lean_inc(x_768);
lean_inc(x_767);
lean_dec(x_60);
x_771 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__2;
x_772 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3;
lean_inc_ref(x_767);
x_773 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_773, 0, x_767);
x_774 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_774, 0, x_767);
x_775 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_775, 0, x_773);
lean_ctor_set(x_775, 1, x_774);
x_776 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_776, 0, x_770);
x_777 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_777, 0, x_769);
x_778 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_778, 0, x_768);
x_779 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_779, 0, x_775);
lean_ctor_set(x_779, 1, x_771);
lean_ctor_set(x_779, 2, x_778);
lean_ctor_set(x_779, 3, x_777);
lean_ctor_set(x_779, 4, x_776);
lean_ctor_set(x_58, 1, x_772);
lean_ctor_set(x_58, 0, x_779);
x_780 = l_ReaderT_instMonad___redArg(x_58);
x_781 = lean_ctor_get(x_780, 0);
lean_inc_ref(x_781);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 x_782 = x_780;
} else {
 lean_dec_ref(x_780);
 x_782 = lean_box(0);
}
x_783 = lean_ctor_get(x_781, 0);
lean_inc_ref(x_783);
x_784 = lean_ctor_get(x_781, 2);
lean_inc_ref(x_784);
x_785 = lean_ctor_get(x_781, 3);
lean_inc_ref(x_785);
x_786 = lean_ctor_get(x_781, 4);
lean_inc_ref(x_786);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 lean_ctor_release(x_781, 2);
 lean_ctor_release(x_781, 3);
 lean_ctor_release(x_781, 4);
 x_787 = x_781;
} else {
 lean_dec_ref(x_781);
 x_787 = lean_box(0);
}
x_788 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__4;
x_789 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__5;
lean_inc_ref(x_783);
x_790 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_790, 0, x_783);
x_791 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_791, 0, x_783);
x_792 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_792, 0, x_790);
lean_ctor_set(x_792, 1, x_791);
x_793 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_793, 0, x_786);
x_794 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_794, 0, x_785);
x_795 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_795, 0, x_784);
if (lean_is_scalar(x_787)) {
 x_796 = lean_alloc_ctor(0, 5, 0);
} else {
 x_796 = x_787;
}
lean_ctor_set(x_796, 0, x_792);
lean_ctor_set(x_796, 1, x_788);
lean_ctor_set(x_796, 2, x_795);
lean_ctor_set(x_796, 3, x_794);
lean_ctor_set(x_796, 4, x_793);
if (lean_is_scalar(x_782)) {
 x_797 = lean_alloc_ctor(0, 2, 0);
} else {
 x_797 = x_782;
}
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_789);
x_798 = l_ReaderT_instMonad___redArg(x_797);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
lean_dec_ref(x_798);
x_799 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_799);
x_800 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_800);
lean_inc(x_4);
lean_inc(x_2);
x_801 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_800, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; uint64_t x_811; uint64_t x_812; uint64_t x_813; uint64_t x_814; uint64_t x_815; uint64_t x_816; uint64_t x_817; size_t x_818; size_t x_819; size_t x_820; size_t x_821; size_t x_822; lean_object* x_823; uint8_t x_824; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_801, 1);
lean_inc(x_803);
lean_dec_ref(x_801);
x_804 = lean_st_ref_get(x_2, x_803);
x_805 = lean_ctor_get(x_804, 0);
lean_inc(x_805);
x_806 = lean_ctor_get(x_804, 1);
lean_inc(x_806);
lean_dec_ref(x_804);
x_807 = lean_ctor_get(x_805, 1);
lean_inc_ref(x_807);
lean_dec(x_805);
x_808 = lean_ctor_get(x_799, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_799, 3);
lean_inc(x_809);
x_810 = lean_array_get_size(x_807);
x_811 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_808);
x_812 = 32;
x_813 = lean_uint64_shift_right(x_811, x_812);
x_814 = lean_uint64_xor(x_811, x_813);
x_815 = 16;
x_816 = lean_uint64_shift_right(x_814, x_815);
x_817 = lean_uint64_xor(x_814, x_816);
x_818 = lean_uint64_to_usize(x_817);
x_819 = lean_usize_of_nat(x_810);
lean_dec(x_810);
x_820 = 1;
x_821 = lean_usize_sub(x_819, x_820);
x_822 = lean_usize_land(x_818, x_821);
x_823 = lean_array_uget(x_807, x_822);
lean_dec_ref(x_807);
x_824 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_808, x_823);
lean_dec(x_823);
lean_dec(x_808);
if (x_824 == 0)
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
lean_dec(x_809);
lean_dec(x_2);
lean_dec_ref(x_1);
x_825 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_799, x_4, x_806);
lean_dec(x_4);
lean_dec_ref(x_799);
x_826 = lean_ctor_get(x_825, 1);
lean_inc(x_826);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_827 = x_825;
} else {
 lean_dec_ref(x_825);
 x_827 = lean_box(0);
}
if (lean_is_scalar(x_827)) {
 x_828 = lean_alloc_ctor(0, 2, 0);
} else {
 x_828 = x_827;
}
lean_ctor_set(x_828, 0, x_802);
lean_ctor_set(x_828, 1, x_826);
return x_828;
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
lean_dec_ref(x_799);
lean_dec(x_4);
x_829 = lean_st_ref_take(x_2, x_806);
x_830 = lean_ctor_get(x_829, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
lean_dec_ref(x_829);
x_832 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_830, x_809);
x_833 = lean_st_ref_set(x_2, x_832, x_831);
lean_dec(x_2);
x_834 = lean_ctor_get(x_833, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_835 = x_833;
} else {
 lean_dec_ref(x_833);
 x_835 = lean_box(0);
}
x_836 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(x_1, x_802);
if (lean_is_scalar(x_835)) {
 x_837 = lean_alloc_ctor(0, 2, 0);
} else {
 x_837 = x_835;
}
lean_ctor_set(x_837, 0, x_836);
lean_ctor_set(x_837, 1, x_834);
return x_837;
}
}
else
{
lean_dec_ref(x_799);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_801;
}
}
case 3:
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_861; lean_object* x_862; lean_object* x_863; uint64_t x_864; uint64_t x_865; uint64_t x_866; uint64_t x_867; uint64_t x_868; uint64_t x_869; uint64_t x_870; size_t x_871; size_t x_872; size_t x_873; size_t x_874; size_t x_875; lean_object* x_876; uint8_t x_877; 
lean_dec_ref(x_798);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_838 = lean_ctor_get(x_1, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_839);
x_840 = lean_st_ref_take(x_2, x_7);
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_840, 1);
lean_inc(x_842);
lean_dec_ref(x_840);
x_861 = lean_ctor_get(x_841, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_841, 1);
lean_inc_ref(x_862);
x_863 = lean_array_get_size(x_862);
x_864 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_838);
x_865 = 32;
x_866 = lean_uint64_shift_right(x_864, x_865);
x_867 = lean_uint64_xor(x_864, x_866);
x_868 = 16;
x_869 = lean_uint64_shift_right(x_867, x_868);
x_870 = lean_uint64_xor(x_867, x_869);
x_871 = lean_uint64_to_usize(x_870);
x_872 = lean_usize_of_nat(x_863);
lean_dec(x_863);
x_873 = 1;
x_874 = lean_usize_sub(x_872, x_873);
x_875 = lean_usize_land(x_871, x_874);
x_876 = lean_array_uget(x_862, x_875);
x_877 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_838, x_876);
if (x_877 == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; uint8_t x_889; 
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 x_878 = x_841;
} else {
 lean_dec_ref(x_841);
 x_878 = lean_box(0);
}
x_879 = lean_box(0);
x_880 = lean_unsigned_to_nat(1u);
x_881 = lean_nat_add(x_861, x_880);
lean_dec(x_861);
x_882 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_882, 0, x_838);
lean_ctor_set(x_882, 1, x_879);
lean_ctor_set(x_882, 2, x_876);
x_883 = lean_array_uset(x_862, x_875, x_882);
x_884 = lean_unsigned_to_nat(4u);
x_885 = lean_nat_mul(x_881, x_884);
x_886 = lean_unsigned_to_nat(3u);
x_887 = lean_nat_div(x_885, x_886);
lean_dec(x_885);
x_888 = lean_array_get_size(x_883);
x_889 = lean_nat_dec_le(x_887, x_888);
lean_dec(x_888);
lean_dec(x_887);
if (x_889 == 0)
{
lean_object* x_890; lean_object* x_891; 
x_890 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_883);
if (lean_is_scalar(x_878)) {
 x_891 = lean_alloc_ctor(0, 2, 0);
} else {
 x_891 = x_878;
}
lean_ctor_set(x_891, 0, x_881);
lean_ctor_set(x_891, 1, x_890);
x_843 = x_891;
goto block_860;
}
else
{
lean_object* x_892; 
if (lean_is_scalar(x_878)) {
 x_892 = lean_alloc_ctor(0, 2, 0);
} else {
 x_892 = x_878;
}
lean_ctor_set(x_892, 0, x_881);
lean_ctor_set(x_892, 1, x_883);
x_843 = x_892;
goto block_860;
}
}
else
{
lean_dec(x_876);
lean_dec_ref(x_862);
lean_dec(x_861);
lean_dec(x_838);
x_843 = x_841;
goto block_860;
}
block_860:
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; uint8_t x_849; 
x_844 = lean_st_ref_set(x_2, x_843, x_842);
x_845 = lean_ctor_get(x_844, 1);
lean_inc(x_845);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_846 = x_844;
} else {
 lean_dec_ref(x_844);
 x_846 = lean_box(0);
}
x_847 = lean_unsigned_to_nat(0u);
x_848 = lean_array_get_size(x_839);
x_849 = lean_nat_dec_lt(x_847, x_848);
if (x_849 == 0)
{
lean_object* x_850; 
lean_dec(x_848);
lean_dec_ref(x_839);
lean_dec(x_2);
if (lean_is_scalar(x_846)) {
 x_850 = lean_alloc_ctor(0, 2, 0);
} else {
 x_850 = x_846;
}
lean_ctor_set(x_850, 0, x_1);
lean_ctor_set(x_850, 1, x_845);
return x_850;
}
else
{
uint8_t x_851; 
x_851 = lean_nat_dec_le(x_848, x_848);
if (x_851 == 0)
{
lean_object* x_852; 
lean_dec(x_848);
lean_dec_ref(x_839);
lean_dec(x_2);
if (lean_is_scalar(x_846)) {
 x_852 = lean_alloc_ctor(0, 2, 0);
} else {
 x_852 = x_846;
}
lean_ctor_set(x_852, 0, x_1);
lean_ctor_set(x_852, 1, x_845);
return x_852;
}
else
{
lean_object* x_853; size_t x_854; size_t x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
lean_dec(x_846);
x_853 = lean_box(0);
x_854 = 0;
x_855 = lean_usize_of_nat(x_848);
lean_dec(x_848);
x_856 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_839, x_854, x_855, x_853, x_2, x_845);
lean_dec(x_2);
lean_dec_ref(x_839);
x_857 = lean_ctor_get(x_856, 1);
lean_inc(x_857);
if (lean_is_exclusive(x_856)) {
 lean_ctor_release(x_856, 0);
 lean_ctor_release(x_856, 1);
 x_858 = x_856;
} else {
 lean_dec_ref(x_856);
 x_858 = lean_box(0);
}
if (lean_is_scalar(x_858)) {
 x_859 = lean_alloc_ctor(0, 2, 0);
} else {
 x_859 = x_858;
}
lean_ctor_set(x_859, 0, x_1);
lean_ctor_set(x_859, 1, x_857);
return x_859;
}
}
}
}
case 4:
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_893 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_893);
x_894 = lean_ctor_get(x_893, 2);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 3);
lean_inc_ref(x_895);
lean_dec_ref(x_893);
x_896 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ElimDead_elimDead___lam__0), 7, 0);
x_897 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_798, x_895, x_896);
lean_inc(x_2);
x_898 = lean_apply_6(x_897, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_911; lean_object* x_912; lean_object* x_913; uint64_t x_914; uint64_t x_915; uint64_t x_916; uint64_t x_917; uint64_t x_918; uint64_t x_919; uint64_t x_920; size_t x_921; size_t x_922; size_t x_923; size_t x_924; size_t x_925; lean_object* x_926; uint8_t x_927; 
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_898, 1);
lean_inc(x_900);
lean_dec_ref(x_898);
x_901 = lean_st_ref_take(x_2, x_900);
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_901, 1);
lean_inc(x_903);
lean_dec_ref(x_901);
x_911 = lean_ctor_get(x_902, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_902, 1);
lean_inc_ref(x_912);
x_913 = lean_array_get_size(x_912);
x_914 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_894);
x_915 = 32;
x_916 = lean_uint64_shift_right(x_914, x_915);
x_917 = lean_uint64_xor(x_914, x_916);
x_918 = 16;
x_919 = lean_uint64_shift_right(x_917, x_918);
x_920 = lean_uint64_xor(x_917, x_919);
x_921 = lean_uint64_to_usize(x_920);
x_922 = lean_usize_of_nat(x_913);
lean_dec(x_913);
x_923 = 1;
x_924 = lean_usize_sub(x_922, x_923);
x_925 = lean_usize_land(x_921, x_924);
x_926 = lean_array_uget(x_912, x_925);
x_927 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_894, x_926);
if (x_927 == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; uint8_t x_939; 
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_928 = x_902;
} else {
 lean_dec_ref(x_902);
 x_928 = lean_box(0);
}
x_929 = lean_box(0);
x_930 = lean_unsigned_to_nat(1u);
x_931 = lean_nat_add(x_911, x_930);
lean_dec(x_911);
x_932 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_932, 0, x_894);
lean_ctor_set(x_932, 1, x_929);
lean_ctor_set(x_932, 2, x_926);
x_933 = lean_array_uset(x_912, x_925, x_932);
x_934 = lean_unsigned_to_nat(4u);
x_935 = lean_nat_mul(x_931, x_934);
x_936 = lean_unsigned_to_nat(3u);
x_937 = lean_nat_div(x_935, x_936);
lean_dec(x_935);
x_938 = lean_array_get_size(x_933);
x_939 = lean_nat_dec_le(x_937, x_938);
lean_dec(x_938);
lean_dec(x_937);
if (x_939 == 0)
{
lean_object* x_940; lean_object* x_941; 
x_940 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_933);
if (lean_is_scalar(x_928)) {
 x_941 = lean_alloc_ctor(0, 2, 0);
} else {
 x_941 = x_928;
}
lean_ctor_set(x_941, 0, x_931);
lean_ctor_set(x_941, 1, x_940);
x_904 = x_941;
goto block_910;
}
else
{
lean_object* x_942; 
if (lean_is_scalar(x_928)) {
 x_942 = lean_alloc_ctor(0, 2, 0);
} else {
 x_942 = x_928;
}
lean_ctor_set(x_942, 0, x_931);
lean_ctor_set(x_942, 1, x_933);
x_904 = x_942;
goto block_910;
}
}
else
{
lean_dec(x_926);
lean_dec_ref(x_912);
lean_dec(x_911);
lean_dec(x_894);
x_904 = x_902;
goto block_910;
}
block_910:
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_905 = lean_st_ref_set(x_2, x_904, x_903);
lean_dec(x_2);
x_906 = lean_ctor_get(x_905, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 x_907 = x_905;
} else {
 lean_dec_ref(x_905);
 x_907 = lean_box(0);
}
x_908 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_899);
if (lean_is_scalar(x_907)) {
 x_909 = lean_alloc_ctor(0, 2, 0);
} else {
 x_909 = x_907;
}
lean_ctor_set(x_909, 0, x_908);
lean_ctor_set(x_909, 1, x_906);
return x_909;
}
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; 
lean_dec(x_894);
lean_dec(x_2);
lean_dec_ref(x_1);
x_943 = lean_ctor_get(x_898, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_898, 1);
lean_inc(x_944);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_945 = x_898;
} else {
 lean_dec_ref(x_898);
 x_945 = lean_box(0);
}
if (lean_is_scalar(x_945)) {
 x_946 = lean_alloc_ctor(1, 2, 0);
} else {
 x_946 = x_945;
}
lean_ctor_set(x_946, 0, x_943);
lean_ctor_set(x_946, 1, x_944);
return x_946;
}
}
case 5:
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_957; lean_object* x_958; lean_object* x_959; uint64_t x_960; uint64_t x_961; uint64_t x_962; uint64_t x_963; uint64_t x_964; uint64_t x_965; uint64_t x_966; size_t x_967; size_t x_968; size_t x_969; size_t x_970; size_t x_971; lean_object* x_972; uint8_t x_973; 
lean_dec_ref(x_798);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_947 = lean_ctor_get(x_1, 0);
lean_inc(x_947);
x_948 = lean_st_ref_take(x_2, x_7);
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
lean_dec_ref(x_948);
x_957 = lean_ctor_get(x_949, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_949, 1);
lean_inc_ref(x_958);
x_959 = lean_array_get_size(x_958);
x_960 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_947);
x_961 = 32;
x_962 = lean_uint64_shift_right(x_960, x_961);
x_963 = lean_uint64_xor(x_960, x_962);
x_964 = 16;
x_965 = lean_uint64_shift_right(x_963, x_964);
x_966 = lean_uint64_xor(x_963, x_965);
x_967 = lean_uint64_to_usize(x_966);
x_968 = lean_usize_of_nat(x_959);
lean_dec(x_959);
x_969 = 1;
x_970 = lean_usize_sub(x_968, x_969);
x_971 = lean_usize_land(x_967, x_970);
x_972 = lean_array_uget(x_958, x_971);
x_973 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_947, x_972);
if (x_973 == 0)
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; uint8_t x_985; 
if (lean_is_exclusive(x_949)) {
 lean_ctor_release(x_949, 0);
 lean_ctor_release(x_949, 1);
 x_974 = x_949;
} else {
 lean_dec_ref(x_949);
 x_974 = lean_box(0);
}
x_975 = lean_box(0);
x_976 = lean_unsigned_to_nat(1u);
x_977 = lean_nat_add(x_957, x_976);
lean_dec(x_957);
x_978 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_978, 0, x_947);
lean_ctor_set(x_978, 1, x_975);
lean_ctor_set(x_978, 2, x_972);
x_979 = lean_array_uset(x_958, x_971, x_978);
x_980 = lean_unsigned_to_nat(4u);
x_981 = lean_nat_mul(x_977, x_980);
x_982 = lean_unsigned_to_nat(3u);
x_983 = lean_nat_div(x_981, x_982);
lean_dec(x_981);
x_984 = lean_array_get_size(x_979);
x_985 = lean_nat_dec_le(x_983, x_984);
lean_dec(x_984);
lean_dec(x_983);
if (x_985 == 0)
{
lean_object* x_986; lean_object* x_987; 
x_986 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_979);
if (lean_is_scalar(x_974)) {
 x_987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_987 = x_974;
}
lean_ctor_set(x_987, 0, x_977);
lean_ctor_set(x_987, 1, x_986);
x_951 = x_987;
goto block_956;
}
else
{
lean_object* x_988; 
if (lean_is_scalar(x_974)) {
 x_988 = lean_alloc_ctor(0, 2, 0);
} else {
 x_988 = x_974;
}
lean_ctor_set(x_988, 0, x_977);
lean_ctor_set(x_988, 1, x_979);
x_951 = x_988;
goto block_956;
}
}
else
{
lean_dec(x_972);
lean_dec_ref(x_958);
lean_dec(x_957);
lean_dec(x_947);
x_951 = x_949;
goto block_956;
}
block_956:
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_952 = lean_st_ref_set(x_2, x_951, x_950);
lean_dec(x_2);
x_953 = lean_ctor_get(x_952, 1);
lean_inc(x_953);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_954 = x_952;
} else {
 lean_dec_ref(x_952);
 x_954 = lean_box(0);
}
if (lean_is_scalar(x_954)) {
 x_955 = lean_alloc_ctor(0, 2, 0);
} else {
 x_955 = x_954;
}
lean_ctor_set(x_955, 0, x_1);
lean_ctor_set(x_955, 1, x_953);
return x_955;
}
}
case 6:
{
lean_object* x_989; 
lean_dec_ref(x_798);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_989 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_989, 0, x_1);
lean_ctor_set(x_989, 1, x_7);
return x_989;
}
default: 
{
lean_object* x_990; lean_object* x_991; 
lean_dec_ref(x_798);
x_990 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_990);
x_991 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_991);
x_8 = x_990;
x_9 = x_991;
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
goto block_57;
}
}
}
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_992 = lean_ctor_get(x_58, 0);
lean_inc(x_992);
lean_dec(x_58);
x_993 = lean_ctor_get(x_992, 0);
lean_inc_ref(x_993);
x_994 = lean_ctor_get(x_992, 2);
lean_inc_ref(x_994);
x_995 = lean_ctor_get(x_992, 3);
lean_inc_ref(x_995);
x_996 = lean_ctor_get(x_992, 4);
lean_inc_ref(x_996);
if (lean_is_exclusive(x_992)) {
 lean_ctor_release(x_992, 0);
 lean_ctor_release(x_992, 1);
 lean_ctor_release(x_992, 2);
 lean_ctor_release(x_992, 3);
 lean_ctor_release(x_992, 4);
 x_997 = x_992;
} else {
 lean_dec_ref(x_992);
 x_997 = lean_box(0);
}
x_998 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__2;
x_999 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__3;
lean_inc_ref(x_993);
x_1000 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_1000, 0, x_993);
x_1001 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_1001, 0, x_993);
x_1002 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1002, 0, x_1000);
lean_ctor_set(x_1002, 1, x_1001);
x_1003 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_1003, 0, x_996);
x_1004 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_1004, 0, x_995);
x_1005 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_1005, 0, x_994);
if (lean_is_scalar(x_997)) {
 x_1006 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1006 = x_997;
}
lean_ctor_set(x_1006, 0, x_1002);
lean_ctor_set(x_1006, 1, x_998);
lean_ctor_set(x_1006, 2, x_1005);
lean_ctor_set(x_1006, 3, x_1004);
lean_ctor_set(x_1006, 4, x_1003);
x_1007 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1007, 0, x_1006);
lean_ctor_set(x_1007, 1, x_999);
x_1008 = l_ReaderT_instMonad___redArg(x_1007);
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc_ref(x_1009);
if (lean_is_exclusive(x_1008)) {
 lean_ctor_release(x_1008, 0);
 lean_ctor_release(x_1008, 1);
 x_1010 = x_1008;
} else {
 lean_dec_ref(x_1008);
 x_1010 = lean_box(0);
}
x_1011 = lean_ctor_get(x_1009, 0);
lean_inc_ref(x_1011);
x_1012 = lean_ctor_get(x_1009, 2);
lean_inc_ref(x_1012);
x_1013 = lean_ctor_get(x_1009, 3);
lean_inc_ref(x_1013);
x_1014 = lean_ctor_get(x_1009, 4);
lean_inc_ref(x_1014);
if (lean_is_exclusive(x_1009)) {
 lean_ctor_release(x_1009, 0);
 lean_ctor_release(x_1009, 1);
 lean_ctor_release(x_1009, 2);
 lean_ctor_release(x_1009, 3);
 lean_ctor_release(x_1009, 4);
 x_1015 = x_1009;
} else {
 lean_dec_ref(x_1009);
 x_1015 = lean_box(0);
}
x_1016 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__4;
x_1017 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__5;
lean_inc_ref(x_1011);
x_1018 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_1018, 0, x_1011);
x_1019 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_1019, 0, x_1011);
x_1020 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1020, 0, x_1018);
lean_ctor_set(x_1020, 1, x_1019);
x_1021 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_1021, 0, x_1014);
x_1022 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_1022, 0, x_1013);
x_1023 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_1023, 0, x_1012);
if (lean_is_scalar(x_1015)) {
 x_1024 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1024 = x_1015;
}
lean_ctor_set(x_1024, 0, x_1020);
lean_ctor_set(x_1024, 1, x_1016);
lean_ctor_set(x_1024, 2, x_1023);
lean_ctor_set(x_1024, 3, x_1022);
lean_ctor_set(x_1024, 4, x_1021);
if (lean_is_scalar(x_1010)) {
 x_1025 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1025 = x_1010;
}
lean_ctor_set(x_1025, 0, x_1024);
lean_ctor_set(x_1025, 1, x_1017);
x_1026 = l_ReaderT_instMonad___redArg(x_1025);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
lean_dec_ref(x_1026);
x_1027 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1027);
x_1028 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1028);
lean_inc(x_4);
lean_inc(x_2);
x_1029 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_1028, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; uint64_t x_1039; uint64_t x_1040; uint64_t x_1041; uint64_t x_1042; uint64_t x_1043; uint64_t x_1044; uint64_t x_1045; size_t x_1046; size_t x_1047; size_t x_1048; size_t x_1049; size_t x_1050; lean_object* x_1051; uint8_t x_1052; 
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
lean_dec_ref(x_1029);
x_1032 = lean_st_ref_get(x_2, x_1031);
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec_ref(x_1032);
x_1035 = lean_ctor_get(x_1033, 1);
lean_inc_ref(x_1035);
lean_dec(x_1033);
x_1036 = lean_ctor_get(x_1027, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_1027, 3);
lean_inc(x_1037);
x_1038 = lean_array_get_size(x_1035);
x_1039 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_1036);
x_1040 = 32;
x_1041 = lean_uint64_shift_right(x_1039, x_1040);
x_1042 = lean_uint64_xor(x_1039, x_1041);
x_1043 = 16;
x_1044 = lean_uint64_shift_right(x_1042, x_1043);
x_1045 = lean_uint64_xor(x_1042, x_1044);
x_1046 = lean_uint64_to_usize(x_1045);
x_1047 = lean_usize_of_nat(x_1038);
lean_dec(x_1038);
x_1048 = 1;
x_1049 = lean_usize_sub(x_1047, x_1048);
x_1050 = lean_usize_land(x_1046, x_1049);
x_1051 = lean_array_uget(x_1035, x_1050);
lean_dec_ref(x_1035);
x_1052 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_1036, x_1051);
lean_dec(x_1051);
lean_dec(x_1036);
if (x_1052 == 0)
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_1037);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1053 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_1027, x_4, x_1034);
lean_dec(x_4);
lean_dec_ref(x_1027);
x_1054 = lean_ctor_get(x_1053, 1);
lean_inc(x_1054);
if (lean_is_exclusive(x_1053)) {
 lean_ctor_release(x_1053, 0);
 lean_ctor_release(x_1053, 1);
 x_1055 = x_1053;
} else {
 lean_dec_ref(x_1053);
 x_1055 = lean_box(0);
}
if (lean_is_scalar(x_1055)) {
 x_1056 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1056 = x_1055;
}
lean_ctor_set(x_1056, 0, x_1030);
lean_ctor_set(x_1056, 1, x_1054);
return x_1056;
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_dec_ref(x_1027);
lean_dec(x_4);
x_1057 = lean_st_ref_take(x_2, x_1034);
x_1058 = lean_ctor_get(x_1057, 0);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1057, 1);
lean_inc(x_1059);
lean_dec_ref(x_1057);
x_1060 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_1058, x_1037);
x_1061 = lean_st_ref_set(x_2, x_1060, x_1059);
lean_dec(x_2);
x_1062 = lean_ctor_get(x_1061, 1);
lean_inc(x_1062);
if (lean_is_exclusive(x_1061)) {
 lean_ctor_release(x_1061, 0);
 lean_ctor_release(x_1061, 1);
 x_1063 = x_1061;
} else {
 lean_dec_ref(x_1061);
 x_1063 = lean_box(0);
}
x_1064 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(x_1, x_1030);
if (lean_is_scalar(x_1063)) {
 x_1065 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1065 = x_1063;
}
lean_ctor_set(x_1065, 0, x_1064);
lean_ctor_set(x_1065, 1, x_1062);
return x_1065;
}
}
else
{
lean_dec_ref(x_1027);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1029;
}
}
case 3:
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; uint64_t x_1092; uint64_t x_1093; uint64_t x_1094; uint64_t x_1095; uint64_t x_1096; uint64_t x_1097; uint64_t x_1098; size_t x_1099; size_t x_1100; size_t x_1101; size_t x_1102; size_t x_1103; lean_object* x_1104; uint8_t x_1105; 
lean_dec_ref(x_1026);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_1066 = lean_ctor_get(x_1, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1067);
x_1068 = lean_st_ref_take(x_2, x_7);
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1068, 1);
lean_inc(x_1070);
lean_dec_ref(x_1068);
x_1089 = lean_ctor_get(x_1069, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1069, 1);
lean_inc_ref(x_1090);
x_1091 = lean_array_get_size(x_1090);
x_1092 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_1066);
x_1093 = 32;
x_1094 = lean_uint64_shift_right(x_1092, x_1093);
x_1095 = lean_uint64_xor(x_1092, x_1094);
x_1096 = 16;
x_1097 = lean_uint64_shift_right(x_1095, x_1096);
x_1098 = lean_uint64_xor(x_1095, x_1097);
x_1099 = lean_uint64_to_usize(x_1098);
x_1100 = lean_usize_of_nat(x_1091);
lean_dec(x_1091);
x_1101 = 1;
x_1102 = lean_usize_sub(x_1100, x_1101);
x_1103 = lean_usize_land(x_1099, x_1102);
x_1104 = lean_array_uget(x_1090, x_1103);
x_1105 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_1066, x_1104);
if (x_1105 == 0)
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; uint8_t x_1117; 
if (lean_is_exclusive(x_1069)) {
 lean_ctor_release(x_1069, 0);
 lean_ctor_release(x_1069, 1);
 x_1106 = x_1069;
} else {
 lean_dec_ref(x_1069);
 x_1106 = lean_box(0);
}
x_1107 = lean_box(0);
x_1108 = lean_unsigned_to_nat(1u);
x_1109 = lean_nat_add(x_1089, x_1108);
lean_dec(x_1089);
x_1110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1110, 0, x_1066);
lean_ctor_set(x_1110, 1, x_1107);
lean_ctor_set(x_1110, 2, x_1104);
x_1111 = lean_array_uset(x_1090, x_1103, x_1110);
x_1112 = lean_unsigned_to_nat(4u);
x_1113 = lean_nat_mul(x_1109, x_1112);
x_1114 = lean_unsigned_to_nat(3u);
x_1115 = lean_nat_div(x_1113, x_1114);
lean_dec(x_1113);
x_1116 = lean_array_get_size(x_1111);
x_1117 = lean_nat_dec_le(x_1115, x_1116);
lean_dec(x_1116);
lean_dec(x_1115);
if (x_1117 == 0)
{
lean_object* x_1118; lean_object* x_1119; 
x_1118 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_1111);
if (lean_is_scalar(x_1106)) {
 x_1119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1119 = x_1106;
}
lean_ctor_set(x_1119, 0, x_1109);
lean_ctor_set(x_1119, 1, x_1118);
x_1071 = x_1119;
goto block_1088;
}
else
{
lean_object* x_1120; 
if (lean_is_scalar(x_1106)) {
 x_1120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1120 = x_1106;
}
lean_ctor_set(x_1120, 0, x_1109);
lean_ctor_set(x_1120, 1, x_1111);
x_1071 = x_1120;
goto block_1088;
}
}
else
{
lean_dec(x_1104);
lean_dec_ref(x_1090);
lean_dec(x_1089);
lean_dec(x_1066);
x_1071 = x_1069;
goto block_1088;
}
block_1088:
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; uint8_t x_1077; 
x_1072 = lean_st_ref_set(x_2, x_1071, x_1070);
x_1073 = lean_ctor_get(x_1072, 1);
lean_inc(x_1073);
if (lean_is_exclusive(x_1072)) {
 lean_ctor_release(x_1072, 0);
 lean_ctor_release(x_1072, 1);
 x_1074 = x_1072;
} else {
 lean_dec_ref(x_1072);
 x_1074 = lean_box(0);
}
x_1075 = lean_unsigned_to_nat(0u);
x_1076 = lean_array_get_size(x_1067);
x_1077 = lean_nat_dec_lt(x_1075, x_1076);
if (x_1077 == 0)
{
lean_object* x_1078; 
lean_dec(x_1076);
lean_dec_ref(x_1067);
lean_dec(x_2);
if (lean_is_scalar(x_1074)) {
 x_1078 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1078 = x_1074;
}
lean_ctor_set(x_1078, 0, x_1);
lean_ctor_set(x_1078, 1, x_1073);
return x_1078;
}
else
{
uint8_t x_1079; 
x_1079 = lean_nat_dec_le(x_1076, x_1076);
if (x_1079 == 0)
{
lean_object* x_1080; 
lean_dec(x_1076);
lean_dec_ref(x_1067);
lean_dec(x_2);
if (lean_is_scalar(x_1074)) {
 x_1080 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1080 = x_1074;
}
lean_ctor_set(x_1080, 0, x_1);
lean_ctor_set(x_1080, 1, x_1073);
return x_1080;
}
else
{
lean_object* x_1081; size_t x_1082; size_t x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
lean_dec(x_1074);
x_1081 = lean_box(0);
x_1082 = 0;
x_1083 = lean_usize_of_nat(x_1076);
lean_dec(x_1076);
x_1084 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_1067, x_1082, x_1083, x_1081, x_2, x_1073);
lean_dec(x_2);
lean_dec_ref(x_1067);
x_1085 = lean_ctor_get(x_1084, 1);
lean_inc(x_1085);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1086 = x_1084;
} else {
 lean_dec_ref(x_1084);
 x_1086 = lean_box(0);
}
if (lean_is_scalar(x_1086)) {
 x_1087 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1087 = x_1086;
}
lean_ctor_set(x_1087, 0, x_1);
lean_ctor_set(x_1087, 1, x_1085);
return x_1087;
}
}
}
}
case 4:
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
x_1121 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1121);
x_1122 = lean_ctor_get(x_1121, 2);
lean_inc(x_1122);
x_1123 = lean_ctor_get(x_1121, 3);
lean_inc_ref(x_1123);
lean_dec_ref(x_1121);
x_1124 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ElimDead_elimDead___lam__0), 7, 0);
x_1125 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_1026, x_1123, x_1124);
lean_inc(x_2);
x_1126 = lean_apply_6(x_1125, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1126) == 0)
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; uint64_t x_1142; uint64_t x_1143; uint64_t x_1144; uint64_t x_1145; uint64_t x_1146; uint64_t x_1147; uint64_t x_1148; size_t x_1149; size_t x_1150; size_t x_1151; size_t x_1152; size_t x_1153; lean_object* x_1154; uint8_t x_1155; 
x_1127 = lean_ctor_get(x_1126, 0);
lean_inc(x_1127);
x_1128 = lean_ctor_get(x_1126, 1);
lean_inc(x_1128);
lean_dec_ref(x_1126);
x_1129 = lean_st_ref_take(x_2, x_1128);
x_1130 = lean_ctor_get(x_1129, 0);
lean_inc(x_1130);
x_1131 = lean_ctor_get(x_1129, 1);
lean_inc(x_1131);
lean_dec_ref(x_1129);
x_1139 = lean_ctor_get(x_1130, 0);
lean_inc(x_1139);
x_1140 = lean_ctor_get(x_1130, 1);
lean_inc_ref(x_1140);
x_1141 = lean_array_get_size(x_1140);
x_1142 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_1122);
x_1143 = 32;
x_1144 = lean_uint64_shift_right(x_1142, x_1143);
x_1145 = lean_uint64_xor(x_1142, x_1144);
x_1146 = 16;
x_1147 = lean_uint64_shift_right(x_1145, x_1146);
x_1148 = lean_uint64_xor(x_1145, x_1147);
x_1149 = lean_uint64_to_usize(x_1148);
x_1150 = lean_usize_of_nat(x_1141);
lean_dec(x_1141);
x_1151 = 1;
x_1152 = lean_usize_sub(x_1150, x_1151);
x_1153 = lean_usize_land(x_1149, x_1152);
x_1154 = lean_array_uget(x_1140, x_1153);
x_1155 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_1122, x_1154);
if (x_1155 == 0)
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; uint8_t x_1167; 
if (lean_is_exclusive(x_1130)) {
 lean_ctor_release(x_1130, 0);
 lean_ctor_release(x_1130, 1);
 x_1156 = x_1130;
} else {
 lean_dec_ref(x_1130);
 x_1156 = lean_box(0);
}
x_1157 = lean_box(0);
x_1158 = lean_unsigned_to_nat(1u);
x_1159 = lean_nat_add(x_1139, x_1158);
lean_dec(x_1139);
x_1160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1160, 0, x_1122);
lean_ctor_set(x_1160, 1, x_1157);
lean_ctor_set(x_1160, 2, x_1154);
x_1161 = lean_array_uset(x_1140, x_1153, x_1160);
x_1162 = lean_unsigned_to_nat(4u);
x_1163 = lean_nat_mul(x_1159, x_1162);
x_1164 = lean_unsigned_to_nat(3u);
x_1165 = lean_nat_div(x_1163, x_1164);
lean_dec(x_1163);
x_1166 = lean_array_get_size(x_1161);
x_1167 = lean_nat_dec_le(x_1165, x_1166);
lean_dec(x_1166);
lean_dec(x_1165);
if (x_1167 == 0)
{
lean_object* x_1168; lean_object* x_1169; 
x_1168 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_1161);
if (lean_is_scalar(x_1156)) {
 x_1169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1169 = x_1156;
}
lean_ctor_set(x_1169, 0, x_1159);
lean_ctor_set(x_1169, 1, x_1168);
x_1132 = x_1169;
goto block_1138;
}
else
{
lean_object* x_1170; 
if (lean_is_scalar(x_1156)) {
 x_1170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1170 = x_1156;
}
lean_ctor_set(x_1170, 0, x_1159);
lean_ctor_set(x_1170, 1, x_1161);
x_1132 = x_1170;
goto block_1138;
}
}
else
{
lean_dec(x_1154);
lean_dec_ref(x_1140);
lean_dec(x_1139);
lean_dec(x_1122);
x_1132 = x_1130;
goto block_1138;
}
block_1138:
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
x_1133 = lean_st_ref_set(x_2, x_1132, x_1131);
lean_dec(x_2);
x_1134 = lean_ctor_get(x_1133, 1);
lean_inc(x_1134);
if (lean_is_exclusive(x_1133)) {
 lean_ctor_release(x_1133, 0);
 lean_ctor_release(x_1133, 1);
 x_1135 = x_1133;
} else {
 lean_dec_ref(x_1133);
 x_1135 = lean_box(0);
}
x_1136 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_1, x_1127);
if (lean_is_scalar(x_1135)) {
 x_1137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1137 = x_1135;
}
lean_ctor_set(x_1137, 0, x_1136);
lean_ctor_set(x_1137, 1, x_1134);
return x_1137;
}
}
else
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
lean_dec(x_1122);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1171 = lean_ctor_get(x_1126, 0);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1126, 1);
lean_inc(x_1172);
if (lean_is_exclusive(x_1126)) {
 lean_ctor_release(x_1126, 0);
 lean_ctor_release(x_1126, 1);
 x_1173 = x_1126;
} else {
 lean_dec_ref(x_1126);
 x_1173 = lean_box(0);
}
if (lean_is_scalar(x_1173)) {
 x_1174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1174 = x_1173;
}
lean_ctor_set(x_1174, 0, x_1171);
lean_ctor_set(x_1174, 1, x_1172);
return x_1174;
}
}
case 5:
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; uint64_t x_1188; uint64_t x_1189; uint64_t x_1190; uint64_t x_1191; uint64_t x_1192; uint64_t x_1193; uint64_t x_1194; size_t x_1195; size_t x_1196; size_t x_1197; size_t x_1198; size_t x_1199; lean_object* x_1200; uint8_t x_1201; 
lean_dec_ref(x_1026);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_1175 = lean_ctor_get(x_1, 0);
lean_inc(x_1175);
x_1176 = lean_st_ref_take(x_2, x_7);
x_1177 = lean_ctor_get(x_1176, 0);
lean_inc(x_1177);
x_1178 = lean_ctor_get(x_1176, 1);
lean_inc(x_1178);
lean_dec_ref(x_1176);
x_1185 = lean_ctor_get(x_1177, 0);
lean_inc(x_1185);
x_1186 = lean_ctor_get(x_1177, 1);
lean_inc_ref(x_1186);
x_1187 = lean_array_get_size(x_1186);
x_1188 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_1175);
x_1189 = 32;
x_1190 = lean_uint64_shift_right(x_1188, x_1189);
x_1191 = lean_uint64_xor(x_1188, x_1190);
x_1192 = 16;
x_1193 = lean_uint64_shift_right(x_1191, x_1192);
x_1194 = lean_uint64_xor(x_1191, x_1193);
x_1195 = lean_uint64_to_usize(x_1194);
x_1196 = lean_usize_of_nat(x_1187);
lean_dec(x_1187);
x_1197 = 1;
x_1198 = lean_usize_sub(x_1196, x_1197);
x_1199 = lean_usize_land(x_1195, x_1198);
x_1200 = lean_array_uget(x_1186, x_1199);
x_1201 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_1175, x_1200);
if (x_1201 == 0)
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; uint8_t x_1213; 
if (lean_is_exclusive(x_1177)) {
 lean_ctor_release(x_1177, 0);
 lean_ctor_release(x_1177, 1);
 x_1202 = x_1177;
} else {
 lean_dec_ref(x_1177);
 x_1202 = lean_box(0);
}
x_1203 = lean_box(0);
x_1204 = lean_unsigned_to_nat(1u);
x_1205 = lean_nat_add(x_1185, x_1204);
lean_dec(x_1185);
x_1206 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1206, 0, x_1175);
lean_ctor_set(x_1206, 1, x_1203);
lean_ctor_set(x_1206, 2, x_1200);
x_1207 = lean_array_uset(x_1186, x_1199, x_1206);
x_1208 = lean_unsigned_to_nat(4u);
x_1209 = lean_nat_mul(x_1205, x_1208);
x_1210 = lean_unsigned_to_nat(3u);
x_1211 = lean_nat_div(x_1209, x_1210);
lean_dec(x_1209);
x_1212 = lean_array_get_size(x_1207);
x_1213 = lean_nat_dec_le(x_1211, x_1212);
lean_dec(x_1212);
lean_dec(x_1211);
if (x_1213 == 0)
{
lean_object* x_1214; lean_object* x_1215; 
x_1214 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__1___redArg(x_1207);
if (lean_is_scalar(x_1202)) {
 x_1215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1215 = x_1202;
}
lean_ctor_set(x_1215, 0, x_1205);
lean_ctor_set(x_1215, 1, x_1214);
x_1179 = x_1215;
goto block_1184;
}
else
{
lean_object* x_1216; 
if (lean_is_scalar(x_1202)) {
 x_1216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1216 = x_1202;
}
lean_ctor_set(x_1216, 0, x_1205);
lean_ctor_set(x_1216, 1, x_1207);
x_1179 = x_1216;
goto block_1184;
}
}
else
{
lean_dec(x_1200);
lean_dec_ref(x_1186);
lean_dec(x_1185);
lean_dec(x_1175);
x_1179 = x_1177;
goto block_1184;
}
block_1184:
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1180 = lean_st_ref_set(x_2, x_1179, x_1178);
lean_dec(x_2);
x_1181 = lean_ctor_get(x_1180, 1);
lean_inc(x_1181);
if (lean_is_exclusive(x_1180)) {
 lean_ctor_release(x_1180, 0);
 lean_ctor_release(x_1180, 1);
 x_1182 = x_1180;
} else {
 lean_dec_ref(x_1180);
 x_1182 = lean_box(0);
}
if (lean_is_scalar(x_1182)) {
 x_1183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1183 = x_1182;
}
lean_ctor_set(x_1183, 0, x_1);
lean_ctor_set(x_1183, 1, x_1181);
return x_1183;
}
}
case 6:
{
lean_object* x_1217; 
lean_dec_ref(x_1026);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_1217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1217, 0, x_1);
lean_ctor_set(x_1217, 1, x_7);
return x_1217;
}
default: 
{
lean_object* x_1218; lean_object* x_1219; 
lean_dec_ref(x_1026);
x_1218 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1218);
x_1219 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1219);
x_8 = x_1218;
x_9 = x_1219;
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
goto block_57;
}
}
}
block_57:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
x_16 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; uint8_t x_38; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_st_ref_get(x_10, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
x_24 = lean_array_get_size(x_22);
x_25 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_23);
x_26 = 32;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = 16;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_34 = 1;
x_35 = lean_usize_sub(x_33, x_34);
x_36 = lean_usize_land(x_32, x_35);
x_37 = lean_array_uget(x_22, x_36);
lean_dec_ref(x_22);
x_38 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(x_23, x_37);
lean_dec(x_37);
lean_dec(x_23);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_1);
x_39 = 1;
x_40 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_8, x_39, x_12, x_21);
lean_dec(x_12);
lean_dec_ref(x_8);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_17);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_17);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; 
x_45 = l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(x_8, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_47, x_17);
lean_dec_ref(x_1);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_45);
x_51 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_1, x_49, x_17);
lean_dec_ref(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_17);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_45, 0);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_instFVarIdHashSetEmptyCollection;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc(x_9);
x_11 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
else
{
lean_dec(x_9);
return x_11;
}
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
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_elimDead), 6, 0);
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
l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__4 = _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__4);
l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__5 = _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__5);
l_Lean_Compiler_LCNF_Decl_elimDead___closed__0 = _init_l_Lean_Compiler_LCNF_Decl_elimDead___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_elimDead___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
