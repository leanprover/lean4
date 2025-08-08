// Lean compiler output
// Module: Lean.Compiler.LCNF.Internalize
// Imports: Lean.Compiler.LCNF.Types Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.CompilerM
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
static lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0;
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__3;
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
lean_object* l_StateRefT_x27_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_internalize_go___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_modify(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__5;
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(lean_object*, lean_object*, uint8_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__0;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2;
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__11;
lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0___redArg(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0;
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__2;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_instMonadStateOfMonadStateOf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_internalize_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__4;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__7;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__8;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0;
static lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_st_ref_get(x_2, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_12);
lean_ctor_set(x_9, 1, x_14);
x_15 = lean_st_ref_set(x_2, x_9, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = l_Lean_Name_num___override(x_4, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_dec(x_6);
x_22 = l_Lean_Name_num___override(x_4, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_st_ref_set(x_2, x_28, x_10);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_dec(x_6);
x_33 = l_Lean_Name_num___override(x_4, x_32);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftBaseIOEIO___lam__0), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMonadLiftSTRealWorldBaseIO___lam__0), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftT___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__4;
x_2 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__5;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__3;
x_2 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__6;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__2;
x_2 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__7;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1;
x_2 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__8;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0;
x_2 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__9;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_get), 5, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__11;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10;
x_2 = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0;
x_2 = l_instMonadStateOfMonadStateOf___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1;
x_2 = lean_alloc_closure((void*)(l_modify), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_st_ref_take(x_1, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 2);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_9, x_15);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_16);
lean_ctor_set(x_11, 2, x_5);
x_17 = lean_st_ref_set(x_1, x_11, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_Name_num___override(x_8, x_9);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Name_num___override(x_8, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
x_29 = lean_ctor_get(x_11, 6);
x_30 = lean_ctor_get(x_11, 7);
x_31 = lean_ctor_get(x_11, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_9, x_32);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_33);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_5);
lean_ctor_set(x_34, 3, x_26);
lean_ctor_set(x_34, 4, x_27);
lean_ctor_set(x_34, 5, x_28);
lean_ctor_set(x_34, 6, x_29);
lean_ctor_set(x_34, 7, x_30);
lean_ctor_set(x_34, 8, x_31);
x_35 = lean_st_ref_set(x_1, x_34, x_12);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = l_Lean_Name_num___override(x_8, x_9);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_st_ref_take(x_1, x_6);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 3);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_43, 4);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_43, 5);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_43, 6);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_43, 7);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_43, 8);
lean_inc_ref(x_52);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 lean_ctor_release(x_43, 6);
 lean_ctor_release(x_43, 7);
 lean_ctor_release(x_43, 8);
 x_53 = x_43;
} else {
 lean_dec_ref(x_43);
 x_53 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_41, x_54);
lean_inc(x_40);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 9, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_47);
lean_ctor_set(x_57, 4, x_48);
lean_ctor_set(x_57, 5, x_49);
lean_ctor_set(x_57, 6, x_50);
lean_ctor_set(x_57, 7, x_51);
lean_ctor_set(x_57, 8, x_52);
x_58 = lean_st_ref_set(x_1, x_57, x_44);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = l_Lean_Name_num___override(x_40, x_41);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_4);
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
x_26 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_22);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3_spec__3___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__6___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__6___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_21; 
x_8 = l_Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_9);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_9);
x_25 = lean_array_get_size(x_23);
x_26 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_1);
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
x_38 = lean_array_uget(x_23, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(x_1, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_22, x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_24);
lean_ctor_set(x_42, 2, x_38);
x_43 = lean_array_uset(x_23, x_37, x_42);
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
lean_object* x_50; 
x_50 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3___redArg(x_43);
lean_ctor_set(x_12, 1, x_50);
lean_ctor_set(x_12, 0, x_41);
x_14 = x_12;
goto block_20;
}
else
{
lean_ctor_set(x_12, 1, x_43);
lean_ctor_set(x_12, 0, x_41);
x_14 = x_12;
goto block_20;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_box(0);
x_52 = lean_array_uset(x_23, x_37, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__6___redArg(x_1, x_24, x_38);
x_54 = lean_array_uset(x_52, x_37, x_53);
lean_ctor_set(x_12, 1, x_54);
x_14 = x_12;
goto block_20;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; size_t x_66; size_t x_67; size_t x_68; size_t x_69; size_t x_70; lean_object* x_71; uint8_t x_72; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_12);
lean_inc(x_9);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_9);
x_58 = lean_array_get_size(x_56);
x_59 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_1);
x_60 = 32;
x_61 = lean_uint64_shift_right(x_59, x_60);
x_62 = lean_uint64_xor(x_59, x_61);
x_63 = 16;
x_64 = lean_uint64_shift_right(x_62, x_63);
x_65 = lean_uint64_xor(x_62, x_64);
x_66 = lean_uint64_to_usize(x_65);
x_67 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_68 = 1;
x_69 = lean_usize_sub(x_67, x_68);
x_70 = lean_usize_land(x_66, x_69);
x_71 = lean_array_uget(x_56, x_70);
x_72 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(x_1, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_55, x_73);
lean_dec(x_55);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_57);
lean_ctor_set(x_75, 2, x_71);
x_76 = lean_array_uset(x_56, x_70, x_75);
x_77 = lean_unsigned_to_nat(4u);
x_78 = lean_nat_mul(x_74, x_77);
x_79 = lean_unsigned_to_nat(3u);
x_80 = lean_nat_div(x_78, x_79);
lean_dec(x_78);
x_81 = lean_array_get_size(x_76);
x_82 = lean_nat_dec_le(x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__3___redArg(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_83);
x_14 = x_84;
goto block_20;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_76);
x_14 = x_85;
goto block_20;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_box(0);
x_87 = lean_array_uset(x_56, x_70, x_86);
x_88 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__6___redArg(x_1, x_57, x_71);
x_89 = lean_array_uset(x_87, x_70, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_55);
lean_ctor_set(x_90, 1, x_89);
x_14 = x_90;
goto block_20;
}
}
block_20:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_set(x_2, x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshFVarId___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_10, x_4, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_st_ref_get(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_9, x_2, x_3, x_4, x_5, x_6, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_st_ref_take(x_4, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = 1;
x_27 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_16, x_26, x_11);
lean_dec(x_16);
lean_ctor_set(x_1, 2, x_27);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_19);
lean_inc_ref(x_1);
x_28 = l_Lean_Compiler_LCNF_LCtx_addParam(x_25, x_1);
lean_ctor_set(x_22, 0, x_28);
x_29 = lean_st_ref_set(x_4, x_22, x_23);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = 1;
x_37 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_16, x_36, x_11);
lean_dec(x_16);
lean_ctor_set(x_1, 2, x_37);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_19);
lean_inc_ref(x_1);
x_38 = l_Lean_Compiler_LCNF_LCtx_addParam(x_34, x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
x_40 = lean_st_ref_set(x_4, x_39, x_23);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get(x_1, 2);
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_1);
x_48 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_45, x_4, x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = lean_st_ref_get(x_2, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_44, x_2, x_3, x_4, x_5, x_6, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_st_ref_take(x_4, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
x_63 = 1;
x_64 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_52, x_63, x_46);
lean_dec(x_52);
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_49);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_47);
lean_inc_ref(x_65);
x_66 = l_Lean_Compiler_LCNF_LCtx_addParam(x_60, x_65);
if (lean_is_scalar(x_62)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_62;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_61);
x_68 = lean_st_ref_set(x_4, x_67, x_59);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_10, x_4, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_st_ref_get(x_2, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_st_ref_get(x_2, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_9, x_2, x_3, x_4, x_5, x_6, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_st_ref_take(x_4, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = 1;
x_31 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_17, x_30, x_11);
lean_dec(x_17);
x_32 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_20, x_12, x_30);
lean_dec(x_20);
lean_ctor_set(x_1, 3, x_32);
lean_ctor_set(x_1, 2, x_31);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_23);
lean_inc_ref(x_1);
x_33 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_29, x_1);
lean_ctor_set(x_26, 0, x_33);
x_34 = lean_st_ref_set(x_4, x_26, x_27);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_1);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
x_41 = 1;
x_42 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_17, x_41, x_11);
lean_dec(x_17);
x_43 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_20, x_12, x_41);
lean_dec(x_20);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_42);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_23);
lean_inc_ref(x_1);
x_44 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_39, x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_st_ref_set(x_4, x_45, x_27);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
x_52 = lean_ctor_get(x_1, 2);
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_1);
x_54 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_51, x_4, x_7);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_st_ref_get(x_2, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_st_ref_get(x_2, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_50, x_2, x_3, x_4, x_5, x_6, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = lean_st_ref_take(x_4, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_71 = x_67;
} else {
 lean_dec_ref(x_67);
 x_71 = lean_box(0);
}
x_72 = 1;
x_73 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_58, x_72, x_52);
lean_dec(x_58);
x_74 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_61, x_53, x_72);
lean_dec(x_61);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_55);
lean_ctor_set(x_75, 2, x_73);
lean_ctor_set(x_75, 3, x_74);
lean_inc_ref(x_75);
x_76 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_69, x_75);
if (lean_is_scalar(x_71)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_71;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_70);
x_78 = lean_st_ref_set(x_4, x_77, x_68);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_17, x_2, x_14);
x_2 = x_19;
x_3 = x_20;
x_9 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_ctor_get(x_1, 4);
x_17 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_13, x_4, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_array_size(x_14);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_20, x_21, x_14, x_2, x_3, x_4, x_5, x_6, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_16, x_2, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_12, x_2, x_3, x_4, x_5, x_6, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_st_ref_take(x_4, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = 1;
x_37 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_9, x_36, x_15);
lean_dec(x_9);
lean_ctor_set(x_1, 4, x_26);
lean_ctor_set(x_1, 3, x_37);
lean_ctor_set(x_1, 2, x_23);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_29);
lean_inc_ref(x_1);
x_38 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_35, x_1);
lean_ctor_set(x_32, 0, x_38);
x_39 = lean_st_ref_set(x_4, x_32, x_33);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_1);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
x_46 = 1;
x_47 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_9, x_46, x_15);
lean_dec(x_9);
lean_ctor_set(x_1, 4, x_26);
lean_ctor_set(x_1, 3, x_47);
lean_ctor_set(x_1, 2, x_23);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_29);
lean_inc_ref(x_1);
x_48 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_44, x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = lean_st_ref_set(x_4, x_49, x_33);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_23);
lean_dec(x_18);
lean_free_object(x_1);
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec(x_9);
x_54 = !lean_is_exclusive(x_25);
if (x_54 == 0)
{
return x_25;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_25, 0);
x_56 = lean_ctor_get(x_25, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_25);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_1, 0);
x_59 = lean_ctor_get(x_1, 1);
x_60 = lean_ctor_get(x_1, 2);
x_61 = lean_ctor_get(x_1, 3);
x_62 = lean_ctor_get(x_1, 4);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_1);
x_63 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_59, x_4, x_10);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = lean_array_size(x_60);
x_67 = 0;
x_68 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_66, x_67, x_60, x_2, x_3, x_4, x_5, x_6, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_62, x_2, x_3, x_4, x_5, x_6, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_58, x_2, x_3, x_4, x_5, x_6, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_st_ref_take(x_4, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = 1;
x_84 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_9, x_83, x_61);
lean_dec(x_9);
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_64);
lean_ctor_set(x_85, 2, x_69);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_72);
lean_inc_ref(x_85);
x_86 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_80, x_85);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
x_88 = lean_st_ref_set(x_4, x_87, x_79);
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
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_69);
lean_dec(x_64);
lean_dec_ref(x_61);
lean_dec(x_58);
lean_dec(x_9);
x_92 = lean_ctor_get(x_71, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_71, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_94 = x_71;
} else {
 lean_dec_ref(x_71);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0___redArg(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_10, x_12, x_1);
lean_dec(x_10);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_14, x_3, x_15);
x_3 = x_17;
x_4 = x_18;
x_6 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_array_size(x_24);
x_27 = 0;
x_28 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_26, x_27, x_24, x_4, x_5, x_6, x_7, x_8, x_9);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_25, x_4, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
lean_ctor_set(x_12, 2, x_32);
lean_ctor_set(x_12, 1, x_29);
x_15 = x_12;
x_16 = x_33;
goto block_21;
}
else
{
uint8_t x_34; 
lean_dec(x_29);
lean_free_object(x_12);
lean_dec(x_23);
lean_dec_ref(x_14);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
x_40 = lean_ctor_get(x_12, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_41 = lean_array_size(x_39);
x_42 = 0;
x_43 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_41, x_42, x_39, x_4, x_5, x_6, x_7, x_8, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_40, x_4, x_5, x_6, x_7, x_8, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_47);
x_15 = x_49;
x_16 = x_48;
goto block_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_44);
lean_dec(x_38);
lean_dec_ref(x_14);
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_52 = x_46;
} else {
 lean_dec_ref(x_46);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_55, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
lean_ctor_set(x_12, 0, x_57);
x_15 = x_12;
x_16 = x_58;
goto block_21;
}
else
{
uint8_t x_59; 
lean_free_object(x_12);
lean_dec_ref(x_14);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_12, 0);
lean_inc(x_63);
lean_dec(x_12);
x_64 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_63, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_15 = x_67;
x_16 = x_66;
goto block_21;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_14);
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_70 = x_64;
} else {
 lean_dec_ref(x_64);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
block_21:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_14, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
x_9 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_array_size(x_24);
x_27 = 0;
x_28 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_26, x_27, x_24, x_4, x_5, x_6, x_7, x_8, x_9);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_25, x_4, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
lean_ctor_set(x_12, 2, x_32);
lean_ctor_set(x_12, 1, x_29);
x_15 = x_12;
x_16 = x_33;
goto block_21;
}
else
{
uint8_t x_34; 
lean_dec(x_29);
lean_free_object(x_12);
lean_dec(x_23);
lean_dec_ref(x_14);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
x_40 = lean_ctor_get(x_12, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_41 = lean_array_size(x_39);
x_42 = 0;
x_43 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_41, x_42, x_39, x_4, x_5, x_6, x_7, x_8, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_40, x_4, x_5, x_6, x_7, x_8, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_47);
x_15 = x_49;
x_16 = x_48;
goto block_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_44);
lean_dec(x_38);
lean_dec_ref(x_14);
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_52 = x_46;
} else {
 lean_dec_ref(x_46);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_55, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
lean_ctor_set(x_12, 0, x_57);
x_15 = x_12;
x_16 = x_58;
goto block_21;
}
else
{
uint8_t x_59; 
lean_free_object(x_12);
lean_dec_ref(x_14);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_12, 0);
lean_inc(x_63);
lean_dec(x_12);
x_64 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_63, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_15 = x_67;
x_16 = x_66;
goto block_21;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_14);
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_70 = x_64;
} else {
 lean_dec_ref(x_64);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
block_21:
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_14, x_2, x_15);
x_20 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1_spec__1(x_1, x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_16);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_10, x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_12);
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
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_dec(x_12);
lean_free_object(x_1);
return x_14;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_20, x_2, x_3, x_4, x_5, x_6, x_7);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_21, x_2, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_dec(x_23);
return x_25;
}
}
}
case 1:
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_32, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_33, x_2, x_3, x_4, x_5, x_6, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_ctor_set(x_1, 1, x_39);
lean_ctor_set(x_1, 0, x_35);
lean_ctor_set(x_37, 0, x_1);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_37);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_35);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_dec(x_35);
lean_free_object(x_1);
return x_37;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_1);
lean_dec_ref(x_33);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_34);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_1);
x_49 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_47, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_48, x_2, x_3, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_53);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
else
{
lean_dec(x_50);
return x_52;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_48);
x_58 = lean_ctor_get(x_49, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_60 = x_49;
} else {
 lean_dec_ref(x_49);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
case 2:
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_1);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
x_65 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_63, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_64, x_2, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_68, 0);
lean_ctor_set(x_1, 1, x_70);
lean_ctor_set(x_1, 0, x_66);
lean_ctor_set(x_68, 0, x_1);
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_68, 0);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_68);
lean_ctor_set(x_1, 1, x_71);
lean_ctor_set(x_1, 0, x_66);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
else
{
lean_dec(x_66);
lean_free_object(x_1);
return x_68;
}
}
else
{
uint8_t x_74; 
lean_free_object(x_1);
lean_dec_ref(x_64);
x_74 = !lean_is_exclusive(x_65);
if (x_74 == 0)
{
return x_65;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_65, 0);
x_76 = lean_ctor_get(x_65, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_65);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_1, 0);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_1);
x_80 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_78, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec_ref(x_80);
x_83 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_79, x_2, x_3, x_4, x_5, x_6, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_84);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_dec(x_81);
return x_83;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_79);
x_89 = lean_ctor_get(x_80, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_80, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_91 = x_80;
} else {
 lean_dec_ref(x_80);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
case 3:
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_1);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
x_96 = lean_st_ref_get(x_2, x_7);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec_ref(x_96);
x_99 = 1;
x_100 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_97, x_94, x_99);
lean_dec(x_97);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; uint8_t x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = lean_array_size(x_95);
x_103 = 0;
x_104 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0___redArg(x_99, x_102, x_103, x_95, x_2, x_98);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_104, 0);
lean_ctor_set(x_1, 1, x_106);
lean_ctor_set(x_1, 0, x_101);
lean_ctor_set(x_104, 0, x_1);
return x_104;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_104, 0);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_104);
lean_ctor_set(x_1, 1, x_107);
lean_ctor_set(x_1, 0, x_101);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
else
{
lean_object* x_110; 
lean_free_object(x_1);
lean_dec_ref(x_95);
x_110 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_98);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; 
x_111 = lean_ctor_get(x_1, 0);
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_1);
x_113 = lean_st_ref_get(x_2, x_7);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec_ref(x_113);
x_116 = 1;
x_117 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_114, x_111, x_116);
lean_dec(x_114);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_array_size(x_112);
x_120 = 0;
x_121 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0___redArg(x_116, x_119, x_120, x_112, x_2, x_115);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_122);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
else
{
lean_object* x_127; 
lean_dec_ref(x_112);
x_127 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_115);
return x_127;
}
}
}
case 4:
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_1);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_1, 0);
x_130 = lean_st_ref_get(x_2, x_7);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec_ref(x_130);
x_133 = !lean_is_exclusive(x_129);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_129, 0);
x_135 = lean_ctor_get(x_129, 1);
x_136 = lean_ctor_get(x_129, 2);
x_137 = lean_ctor_get(x_129, 3);
x_138 = 1;
x_139 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_131, x_136, x_138);
lean_dec(x_131);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; size_t x_144; size_t x_145; lean_object* x_146; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = lean_st_ref_get(x_2, x_132);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec_ref(x_141);
x_144 = lean_array_size(x_137);
x_145 = 0;
x_146 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1(x_144, x_145, x_137, x_2, x_3, x_4, x_5, x_6, x_143);
if (lean_obj_tag(x_146) == 0)
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_146, 0);
x_149 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_142, x_138, x_135);
lean_dec(x_142);
lean_ctor_set(x_129, 3, x_148);
lean_ctor_set(x_129, 2, x_140);
lean_ctor_set(x_129, 1, x_149);
lean_ctor_set(x_146, 0, x_1);
return x_146;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_146, 0);
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_146);
x_152 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_142, x_138, x_135);
lean_dec(x_142);
lean_ctor_set(x_129, 3, x_150);
lean_ctor_set(x_129, 2, x_140);
lean_ctor_set(x_129, 1, x_152);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
uint8_t x_154; 
lean_dec(x_142);
lean_dec(x_140);
lean_free_object(x_129);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_free_object(x_1);
x_154 = !lean_is_exclusive(x_146);
if (x_154 == 0)
{
return x_146;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_146, 0);
x_156 = lean_ctor_get(x_146, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_146);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; 
lean_free_object(x_129);
lean_dec_ref(x_137);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_free_object(x_1);
x_158 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_132);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_129, 0);
x_160 = lean_ctor_get(x_129, 1);
x_161 = lean_ctor_get(x_129, 2);
x_162 = lean_ctor_get(x_129, 3);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_129);
x_163 = 1;
x_164 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_131, x_161, x_163);
lean_dec(x_131);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; lean_object* x_171; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec_ref(x_164);
x_166 = lean_st_ref_get(x_2, x_132);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_169 = lean_array_size(x_162);
x_170 = 0;
x_171 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1(x_169, x_170, x_162, x_2, x_3, x_4, x_5, x_6, x_168);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
x_175 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_167, x_163, x_160);
lean_dec(x_167);
x_176 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_176, 0, x_159);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_176, 2, x_165);
lean_ctor_set(x_176, 3, x_172);
lean_ctor_set(x_1, 0, x_176);
if (lean_is_scalar(x_174)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_174;
}
lean_ctor_set(x_177, 0, x_1);
lean_ctor_set(x_177, 1, x_173);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_167);
lean_dec(x_165);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_free_object(x_1);
x_178 = lean_ctor_get(x_171, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_171, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_180 = x_171;
} else {
 lean_dec_ref(x_171);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; 
lean_dec_ref(x_162);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_free_object(x_1);
x_182 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_132);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
x_183 = lean_ctor_get(x_1, 0);
lean_inc(x_183);
lean_dec(x_1);
x_184 = lean_st_ref_get(x_2, x_7);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec_ref(x_184);
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 1);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_183, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_183, 3);
lean_inc_ref(x_190);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 x_191 = x_183;
} else {
 lean_dec_ref(x_183);
 x_191 = lean_box(0);
}
x_192 = 1;
x_193 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_185, x_189, x_192);
lean_dec(x_185);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; size_t x_198; size_t x_199; lean_object* x_200; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = lean_st_ref_get(x_2, x_186);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec_ref(x_195);
x_198 = lean_array_size(x_190);
x_199 = 0;
x_200 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1(x_198, x_199, x_190, x_2, x_3, x_4, x_5, x_6, x_197);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
x_204 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_196, x_192, x_188);
lean_dec(x_196);
if (lean_is_scalar(x_191)) {
 x_205 = lean_alloc_ctor(0, 4, 0);
} else {
 x_205 = x_191;
}
lean_ctor_set(x_205, 0, x_187);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_194);
lean_ctor_set(x_205, 3, x_201);
x_206 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_206, 0, x_205);
if (lean_is_scalar(x_203)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_203;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_202);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_196);
lean_dec(x_194);
lean_dec(x_191);
lean_dec_ref(x_188);
lean_dec(x_187);
x_208 = lean_ctor_get(x_200, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_200, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_210 = x_200;
} else {
 lean_dec_ref(x_200);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
else
{
lean_object* x_212; 
lean_dec(x_191);
lean_dec_ref(x_190);
lean_dec_ref(x_188);
lean_dec(x_187);
x_212 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_186);
return x_212;
}
}
}
case 5:
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_1);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_ctor_get(x_1, 0);
x_215 = lean_st_ref_get(x_2, x_7);
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = lean_ctor_get(x_215, 1);
x_219 = 1;
x_220 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_217, x_214, x_219);
lean_dec(x_217);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set(x_215, 0, x_1);
return x_215;
}
else
{
lean_object* x_222; 
lean_free_object(x_215);
lean_free_object(x_1);
x_222 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_218);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_215, 0);
x_224 = lean_ctor_get(x_215, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_215);
x_225 = 1;
x_226 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_223, x_214, x_225);
lean_dec(x_223);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
lean_ctor_set(x_1, 0, x_227);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_1);
lean_ctor_set(x_228, 1, x_224);
return x_228;
}
else
{
lean_object* x_229; 
lean_free_object(x_1);
x_229 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_224);
return x_229;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; 
x_230 = lean_ctor_get(x_1, 0);
lean_inc(x_230);
lean_dec(x_1);
x_231 = lean_st_ref_get(x_2, x_7);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_234 = x_231;
} else {
 lean_dec_ref(x_231);
 x_234 = lean_box(0);
}
x_235 = 1;
x_236 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_232, x_230, x_235);
lean_dec(x_232);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec_ref(x_236);
x_238 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_238, 0, x_237);
if (lean_is_scalar(x_234)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_234;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_233);
return x_239;
}
else
{
lean_object* x_240; 
lean_dec(x_234);
x_240 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_233);
return x_240;
}
}
}
default: 
{
uint8_t x_241; 
x_241 = !lean_is_exclusive(x_1);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_242 = lean_ctor_get(x_1, 0);
x_243 = lean_st_ref_get(x_2, x_7);
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = 1;
x_247 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_245, x_246, x_242);
lean_dec(x_245);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set(x_243, 0, x_1);
return x_243;
}
else
{
lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_243, 0);
x_249 = lean_ctor_get(x_243, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_243);
x_250 = 1;
x_251 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_248, x_250, x_242);
lean_dec(x_248);
lean_ctor_set(x_1, 0, x_251);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_1);
lean_ctor_set(x_252, 1, x_249);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_253 = lean_ctor_get(x_1, 0);
lean_inc(x_253);
lean_dec(x_1);
x_254 = lean_st_ref_get(x_2, x_7);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
x_258 = 1;
x_259 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_255, x_258, x_253);
lean_dec(x_255);
x_260 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_260, 0, x_259);
if (lean_is_scalar(x_257)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_257;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_256);
return x_261;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0___redArg(x_7, x_8, x_9, x_4, x_5, x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__0(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1_spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeCode_spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set(x_10, 0, x_1);
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
lean_ctor_set(x_1, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_16, x_2, x_3, x_4, x_5, x_6, x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
case 1:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_24, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_1, 0, x_27);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_1, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_1);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_35, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
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
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
default: 
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_1);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_47, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_1, 0, x_50);
lean_ctor_set(x_48, 0, x_1);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_48);
lean_ctor_set(x_1, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_free_object(x_1);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
lean_dec(x_1);
x_59 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_58, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_60);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_st_mk_ref(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Code_internalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_internalize_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_apply_7(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_7(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_internalize_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_ctor_get(x_1, 4);
x_17 = lean_ctor_get(x_1, 5);
x_18 = lean_array_size(x_15);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_18, x_19, x_15, x_2, x_3, x_4, x_5, x_6, x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_Compiler_LCNF_Decl_internalize_go___closed__0;
x_24 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_internalize_go_spec__0(x_23, x_16, x_2, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = 1;
x_28 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_9, x_27, x_14);
lean_dec(x_9);
lean_ctor_set(x_1, 4, x_26);
lean_ctor_set(x_1, 3, x_21);
lean_ctor_set(x_1, 2, x_28);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = 1;
x_32 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_9, x_31, x_14);
lean_dec(x_9);
lean_ctor_set(x_1, 4, x_29);
lean_ctor_set(x_1, 3, x_21);
lean_ctor_set(x_1, 2, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_free_object(x_1);
lean_dec(x_17);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_ctor_get(x_1, 2);
x_41 = lean_ctor_get(x_1, 3);
x_42 = lean_ctor_get(x_1, 4);
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_45 = lean_ctor_get(x_1, 5);
lean_inc(x_45);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_1);
x_46 = lean_array_size(x_41);
x_47 = 0;
x_48 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_46, x_47, x_41, x_2, x_3, x_4, x_5, x_6, x_10);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_Lean_Compiler_LCNF_Decl_internalize_go___closed__0;
x_52 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_internalize_go_spec__0(x_51, x_42, x_2, x_3, x_4, x_5, x_6, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = 1;
x_57 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_9, x_56, x_40);
lean_dec(x_9);
x_58 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_58, 0, x_38);
lean_ctor_set(x_58, 1, x_39);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_49);
lean_ctor_set(x_58, 4, x_53);
lean_ctor_set(x_58, 5, x_45);
lean_ctor_set_uint8(x_58, sizeof(void*)*6, x_43);
lean_ctor_set_uint8(x_58, sizeof(void*)*6 + 1, x_44);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_49);
lean_dec(x_45);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_9);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_62 = x_52;
} else {
 lean_dec_ref(x_52);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_st_mk_ref(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc(x_9);
x_11 = l_Lean_Compiler_LCNF_Decl_internalize_go(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_5, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
x_16 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_12, 1, x_16);
x_17 = lean_st_ref_set(x_5, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_array_uget(x_3, x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__4;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_22 = l_Lean_Compiler_LCNF_Decl_internalize(x_19, x_21, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_array_uset(x_3, x_2, x_20);
x_26 = 1;
x_27 = lean_usize_add(x_2, x_26);
x_28 = lean_array_uset(x_25, x_2, x_23);
x_2 = x_27;
x_3 = x_28;
x_8 = x_24;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_st_ref_set(x_5, x_36, x_13);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_array_uget(x_3, x_2);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__4;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_42 = l_Lean_Compiler_LCNF_Decl_internalize(x_39, x_41, x_4, x_5, x_6, x_7, x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_array_uset(x_3, x_2, x_40);
x_46 = 1;
x_47 = lean_usize_add(x_2, x_46);
x_48 = lean_array_uset(x_45, x_2, x_43);
x_2 = x_47;
x_3 = x_48;
x_8 = x_44;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_52 = x_42;
} else {
 lean_dec_ref(x_42);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__4;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Compiler_LCNF_cleanup___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Compiler_LCNF_cleanup___closed__1;
x_10 = lean_st_ref_set(x_3, x_9, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_array_size(x_1);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg(x_12, x_13, x_1, x_2, x_3, x_4, x_5, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 2);
lean_dec(x_9);
lean_ctor_set(x_6, 2, x_2);
x_10 = lean_st_ref_set(x_1, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
x_24 = lean_ctor_get(x_6, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_2);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
x_26 = lean_st_ref_set(x_1, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_st_ref_take(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_9, 2);
lean_dec(x_12);
x_13 = l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2;
lean_ctor_set(x_9, 2, x_13);
x_14 = lean_st_ref_set(x_3, x_9, x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_16);
lean_dec(x_6);
x_17 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__4;
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize), 7, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Compiler_LCNF_cleanup___closed__1;
x_20 = 0;
lean_inc(x_3);
x_21 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_18, x_19, x_20, x_2, x_3, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_3, x_16, x_24, x_23);
lean_dec_ref(x_24);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_22);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec_ref(x_21);
x_32 = lean_box(0);
x_33 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_3, x_16, x_32, x_31);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_30);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
x_40 = lean_ctor_get(x_9, 3);
x_41 = lean_ctor_get(x_9, 4);
x_42 = lean_ctor_get(x_9, 5);
x_43 = lean_ctor_get(x_9, 6);
x_44 = lean_ctor_get(x_9, 7);
x_45 = lean_ctor_get(x_9, 8);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_46 = l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2;
x_47 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_47, 3, x_40);
lean_ctor_set(x_47, 4, x_41);
lean_ctor_set(x_47, 5, x_42);
lean_ctor_set(x_47, 6, x_43);
lean_ctor_set(x_47, 7, x_44);
lean_ctor_set(x_47, 8, x_45);
x_48 = lean_st_ref_set(x_3, x_47, x_10);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_50);
lean_dec(x_6);
x_51 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__4;
x_52 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize), 7, 2);
lean_closure_set(x_52, 0, x_1);
lean_closure_set(x_52, 1, x_51);
x_53 = l_Lean_Compiler_LCNF_cleanup___closed__1;
x_54 = 0;
lean_inc(x_3);
x_55 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_52, x_53, x_54, x_2, x_3, x_49);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
lean_inc(x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
x_59 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_3, x_50, x_58, x_57);
lean_dec_ref(x_58);
lean_dec(x_3);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
lean_dec_ref(x_55);
x_65 = lean_box(0);
x_66 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_3, x_50, x_65, x_64);
lean_dec(x_3);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
 lean_ctor_set_tag(x_69, 1);
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Bind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__2 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__2);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__3 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__3);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__4 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__4);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__5 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__5);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__6 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__6);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__7 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__7);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__8 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__8);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__9 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__9);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__11 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__11);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM);
l_Lean_Compiler_LCNF_Decl_internalize_go___closed__0 = _init_l_Lean_Compiler_LCNF_Decl_internalize_go___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_internalize_go___closed__0);
l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__0 = _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__0);
l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__1 = _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__1);
l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__2 = _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__2);
l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__3 = _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__3);
l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__4 = _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_cleanup_spec__0___redArg___closed__4);
l_Lean_Compiler_LCNF_cleanup___closed__0 = _init_l_Lean_Compiler_LCNF_cleanup___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_cleanup___closed__0);
l_Lean_Compiler_LCNF_cleanup___closed__1 = _init_l_Lean_Compiler_LCNF_cleanup___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_cleanup___closed__1);
l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0 = _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0);
l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1 = _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1);
l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2 = _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
