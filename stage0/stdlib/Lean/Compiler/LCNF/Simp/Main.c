// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Main
// Imports: public import Lean.Compiler.LCNF.Simp.InlineCandidate public import Lean.Compiler.LCNF.Simp.InlineProj public import Lean.Compiler.LCNF.Simp.Used public import Lean.Compiler.LCNF.Simp.DefaultAlt public import Lean.Compiler.LCNF.Simp.SimpValue public import Lean.Compiler.LCNF.Simp.ConstantFold
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
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
uint8_t l_Lean_Compiler_LCNF_instBEqLetDecl_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_hasLocalInst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___boxed(lean_object**);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqLetValue_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getCode(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0;
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_object* l_Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_2;
goto _start;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_1 = x_4;
goto _start;
}
case 4:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec_ref(x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_7, x_12);
lean_dec_ref(x_7);
x_14 = l_Lean_Compiler_LCNF_Alt_getCode(x_13);
lean_dec_ref(x_13);
x_1 = x_14;
goto _start;
}
}
case 5:
{
uint8_t x_16; 
lean_dec_ref(x_1);
x_16 = 1;
return x_16;
}
default: 
{
uint8_t x_17; 
lean_dec_ref(x_1);
x_17 = 0;
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_instBEqFVarId_beq(x_4, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_instHashableFVarId_hash(x_4);
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
x_26 = l_Lean_instHashableFVarId_hash(x_22);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object* x_1) {
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
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_instBEqFVarId_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(x_1, x_2, x_7);
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
x_13 = l_Lean_instBEqFVarId_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_instHashableFVarId_hash(x_2);
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
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_instHashableFVarId_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
uint8_t x_16; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_17 = lean_ctor_get(x_9, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_9, 0);
lean_dec(x_19);
x_20 = lean_array_uget(x_1, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_array_fget(x_11, x_12);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_9, 1, x_24);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_10, x_21, x_22);
lean_ctor_set(x_4, 1, x_25);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_9);
x_29 = lean_array_uget(x_1, x_3);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_array_fget(x_11, x_12);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_12, x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_11);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_13);
x_35 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_10, x_30, x_31);
lean_ctor_set(x_4, 1, x_35);
lean_ctor_set(x_4, 0, x_34);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_3 = x_37;
goto _start;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_39, 2);
x_44 = lean_nat_dec_lt(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
lean_inc(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
x_48 = lean_array_uget(x_1, x_3);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_array_fget(x_41, x_42);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_42, x_51);
lean_dec(x_42);
if (lean_is_scalar(x_47)) {
 x_53 = lean_alloc_ctor(0, 3, 0);
} else {
 x_53 = x_47;
}
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_43);
x_54 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_40, x_49, x_50);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_3, x_56);
x_3 = x_57;
x_4 = x_55;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_3, x_4, x_5, x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_nat_dec_lt(x_15, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_3);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_array_fget_borrowed(x_19, x_15);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get(x_22, 2);
lean_inc_ref(x_24);
x_25 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_24, x_21, x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = 0;
x_28 = l_Lean_Compiler_LCNF_mkAuxParam(x_26, x_27, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_15, x_31);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_32);
x_33 = lean_array_push(x_20, x_29);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_30);
lean_inc(x_23);
x_35 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_21, x_23, x_34);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_3, 0, x_33);
goto _start;
}
else
{
uint8_t x_37; 
lean_free_object(x_3);
lean_dec(x_21);
lean_dec(x_20);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_free_object(x_3);
lean_dec(x_21);
lean_dec(x_20);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
lean_dec(x_25);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_46 = lean_array_fget_borrowed(x_43, x_15);
x_47 = lean_ctor_get(x_46, 0);
x_48 = lean_ctor_get(x_46, 2);
lean_inc_ref(x_48);
x_49 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_48, x_45, x_16);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = 0;
x_52 = l_Lean_Compiler_LCNF_mkAuxParam(x_50, x_51, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_15, x_55);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_56);
x_57 = lean_array_push(x_44, x_53);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_54);
lean_inc(x_47);
x_59 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_45, x_47, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_3 = x_60;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_45);
lean_dec(x_44);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_63 = x_52;
} else {
 lean_dec_ref(x_52);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_45);
lean_dec(x_44);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_65 = lean_ctor_get(x_49, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_66 = x_49;
} else {
 lean_dec_ref(x_49);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_9, 0);
lean_inc(x_68);
lean_dec(x_9);
x_69 = lean_nat_dec_lt(x_68, x_12);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_68);
lean_free_object(x_2);
lean_dec(x_12);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_3);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_1, 0);
x_72 = lean_ctor_get(x_3, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_3, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_74 = x_3;
} else {
 lean_dec_ref(x_3);
 x_74 = lean_box(0);
}
x_75 = lean_array_fget_borrowed(x_71, x_68);
x_76 = lean_ctor_get(x_75, 0);
x_77 = lean_ctor_get(x_75, 2);
lean_inc_ref(x_77);
x_78 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_77, x_73, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = 0;
x_81 = l_Lean_Compiler_LCNF_mkAuxParam(x_79, x_80, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_68, x_84);
lean_dec(x_68);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_2, 0, x_86);
x_87 = lean_array_push(x_72, x_82);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_83);
lean_inc(x_76);
x_89 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_73, x_76, x_88);
if (lean_is_scalar(x_74)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_74;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_3 = x_90;
goto _start;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_68);
lean_free_object(x_2);
lean_dec(x_12);
x_92 = lean_ctor_get(x_81, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_93 = x_81;
} else {
 lean_dec_ref(x_81);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_68);
lean_free_object(x_2);
lean_dec(x_12);
x_95 = lean_ctor_get(x_78, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_96 = x_78;
} else {
 lean_dec_ref(x_78);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_95);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
lean_dec(x_2);
x_99 = lean_ctor_get(x_9, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_100 = x_9;
} else {
 lean_dec_ref(x_9);
 x_100 = lean_box(0);
}
x_101 = lean_nat_dec_lt(x_99, x_98);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_3);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_103 = lean_ctor_get(x_1, 0);
x_104 = lean_ctor_get(x_3, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_3, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_106 = x_3;
} else {
 lean_dec_ref(x_3);
 x_106 = lean_box(0);
}
x_107 = lean_array_fget_borrowed(x_103, x_99);
x_108 = lean_ctor_get(x_107, 0);
x_109 = lean_ctor_get(x_107, 2);
lean_inc_ref(x_109);
x_110 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_109, x_105, x_101);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = 0;
x_113 = l_Lean_Compiler_LCNF_mkAuxParam(x_111, x_112, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unsigned_to_nat(1u);
x_117 = lean_nat_add(x_99, x_116);
lean_dec(x_99);
if (lean_is_scalar(x_100)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_100;
}
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_98);
x_120 = lean_array_push(x_104, x_114);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_115);
lean_inc(x_108);
x_122 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_105, x_108, x_121);
if (lean_is_scalar(x_106)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_106;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_2 = x_119;
x_3 = x_123;
goto _start;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_125 = lean_ctor_get(x_113, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_126 = x_113;
} else {
 lean_dec_ref(x_113);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_128 = lean_ctor_get(x_110, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_129 = x_110;
} else {
 lean_dec_ref(x_110);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 1, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_128);
return x_130;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_1, x_6, x_7, x_13, x_14, x_15, x_16);
return x_18;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_f", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_54; uint8_t x_55; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_15 = lean_array_get_size(x_12);
lean_inc(x_15);
x_16 = l_Array_toSubarray___redArg(x_12, x_13, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_array_size(x_10);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_10, x_18, x_19, x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
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
x_25 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
x_54 = lean_array_get_size(x_10);
x_55 = lean_nat_dec_le(x_15, x_13);
if (x_55 == 0)
{
x_26 = x_15;
x_27 = x_54;
goto block_53;
}
else
{
lean_dec(x_15);
x_26 = x_13;
x_27 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l_Array_toSubarray___redArg(x_10, x_26, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 2);
lean_inc(x_30);
if (lean_is_scalar(x_24)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_24;
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_23);
if (lean_is_scalar(x_22)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_22;
 lean_ctor_set_tag(x_32, 1);
}
lean_ctor_set(x_32, 0, x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_34 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_28, x_33, x_31, x_5, x_6, x_7, x_8);
lean_dec_ref(x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_38 = l_Lean_Compiler_LCNF_Code_internalize(x_11, x_37, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = 0;
lean_inc(x_39);
x_41 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_39, x_40, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_41);
x_42 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_43 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_36, x_39, x_42, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_36);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_50 = !lean_is_exclusive(x_34);
if (x_50 == 0)
{
return x_34;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_34, 0);
lean_inc(x_51);
lean_dec(x_34);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(x_1, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
uint8_t x_15; 
lean_free_object(x_11);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_16, x_4, x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; 
lean_free_object(x_17);
x_22 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
lean_dec_ref(x_22);
x_23 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_24);
lean_dec(x_16);
x_25 = 0;
x_26 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_23, x_24, x_2, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_13, 0, x_28);
lean_ctor_set(x_26, 0, x_13);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_13, 0, x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_13);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_13);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
lean_dec(x_17);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
lean_dec_ref(x_41);
x_42 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_43);
lean_dec(x_16);
x_44 = 0;
x_45 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_42, x_43, x_2, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
lean_ctor_set(x_13, 0, x_46);
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_13);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_13);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_50 = x_45;
} else {
 lean_dec_ref(x_45);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_53 = x_41;
} else {
 lean_dec_ref(x_41);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_55 = !lean_is_exclusive(x_17);
if (x_55 == 0)
{
return x_17;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_17, 0);
lean_inc(x_56);
lean_dec(x_17);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_13, 0);
lean_inc(x_58);
lean_dec(x_13);
x_59 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_58, x_4, x_6);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_unbox(x_60);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_63 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
else
{
lean_object* x_65; 
lean_dec(x_61);
x_65 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
lean_dec_ref(x_65);
x_66 = lean_ctor_get(x_58, 2);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_58, 4);
lean_inc_ref(x_67);
lean_dec(x_58);
x_68 = 0;
x_69 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_66, x_67, x_2, x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_70);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_77 = lean_ctor_get(x_65, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_78 = x_65;
} else {
 lean_dec_ref(x_65);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_80 = lean_ctor_get(x_59, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_81 = x_59;
} else {
 lean_dec_ref(x_59);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
}
}
}
else
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_11, 0);
lean_inc(x_83);
lean_dec(x_11);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_87 = x_83;
} else {
 lean_dec_ref(x_83);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_86, x_4, x_6);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_unbox(x_89);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_92 = lean_box(0);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
else
{
lean_object* x_94; 
lean_dec(x_90);
x_94 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
lean_dec_ref(x_94);
x_95 = lean_ctor_get(x_86, 2);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_86, 4);
lean_inc_ref(x_96);
lean_dec(x_86);
x_97 = 0;
x_98 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_95, x_96, x_2, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_87;
}
lean_ctor_set(x_101, 0, x_99);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 1, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_87);
x_103 = lean_ctor_get(x_98, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_104 = x_98;
} else {
 lean_dec_ref(x_98);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_106 = lean_ctor_get(x_94, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_107 = x_94;
} else {
 lean_dec_ref(x_94);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_109 = lean_ctor_get(x_88, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_110 = x_88;
} else {
 lean_dec_ref(x_88);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_109);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_112 = !lean_is_exclusive(x_11);
if (x_112 == 0)
{
return x_11;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_11, 0);
lean_inc(x_113);
lean_dec(x_11);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_x", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_9, 0);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 3)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_ctor_get(x_13, 2);
x_20 = lean_st_ref_get(x_7);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_20);
x_22 = 0;
lean_inc(x_17);
x_23 = l_Lean_Environment_find_x3f(x_21, x_17, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = l_Lean_ConstantInfo_type(x_27);
lean_dec(x_27);
x_29 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_28, x_7);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; 
lean_free_object(x_29);
x_34 = l_Lean_Meta_isInstance___redArg(x_17, x_7);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_free_object(x_34);
lean_inc(x_17);
x_38 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_array_get_size(x_19);
x_45 = l_Lean_Compiler_LCNF_Decl_getArity(x_43);
lean_dec(x_43);
x_46 = lean_nat_dec_lt(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_free_object(x_40);
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_47 = lean_box(0);
lean_ctor_set(x_38, 0, x_47);
return x_38;
}
else
{
lean_object* x_48; 
lean_free_object(x_38);
lean_inc_ref(x_16);
x_48 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_array_size(x_49);
x_51 = 0;
lean_inc(x_49);
x_52 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_50, x_51, x_49);
x_53 = l_Array_append___redArg(x_19, x_52);
lean_dec_ref(x_52);
lean_ctor_set(x_13, 2, x_53);
x_54 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_55 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_54, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_ctor_set_tag(x_23, 5);
lean_ctor_set(x_23, 0, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_23);
x_59 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_60 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_49, x_58, x_59, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_inc(x_15);
x_63 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_62, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec_ref(x_63);
x_64 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_40, 0, x_61);
lean_ctor_set(x_64, 0, x_40);
return x_64;
}
else
{
lean_object* x_67; 
lean_dec(x_64);
lean_ctor_set(x_40, 0, x_61);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_40);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_61);
lean_free_object(x_40);
x_68 = !lean_is_exclusive(x_64);
if (x_68 == 0)
{
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_61);
lean_free_object(x_40);
lean_dec(x_5);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_63);
if (x_71 == 0)
{
return x_63;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
lean_dec(x_63);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_free_object(x_40);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_60);
if (x_74 == 0)
{
return x_60;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_60, 0);
lean_inc(x_75);
lean_dec(x_60);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_49);
lean_free_object(x_40);
lean_free_object(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_55);
if (x_77 == 0)
{
return x_55;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_55, 0);
lean_inc(x_78);
lean_dec(x_55);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_free_object(x_40);
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_48);
if (x_80 == 0)
{
return x_48;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_48, 0);
lean_inc(x_81);
lean_dec(x_48);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_40, 0);
lean_inc(x_83);
lean_dec(x_40);
x_84 = lean_array_get_size(x_19);
x_85 = l_Lean_Compiler_LCNF_Decl_getArity(x_83);
lean_dec(x_83);
x_86 = lean_nat_dec_lt(x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
if (x_86 == 0)
{
lean_object* x_87; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_87 = lean_box(0);
lean_ctor_set(x_38, 0, x_87);
return x_38;
}
else
{
lean_object* x_88; 
lean_free_object(x_38);
lean_inc_ref(x_16);
x_88 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = lean_array_size(x_89);
x_91 = 0;
lean_inc(x_89);
x_92 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_90, x_91, x_89);
x_93 = l_Array_append___redArg(x_19, x_92);
lean_dec_ref(x_92);
lean_ctor_set(x_13, 2, x_93);
x_94 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_95 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_94, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_ctor_set_tag(x_23, 5);
lean_ctor_set(x_23, 0, x_97);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_23);
x_99 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_100 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_89, x_98, x_99, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_inc(x_15);
x_103 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_102, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
lean_dec_ref(x_103);
x_104 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_105 = x_104;
} else {
 lean_dec_ref(x_104);
 x_105 = lean_box(0);
}
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 1, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_101);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_109 = x_104;
} else {
 lean_dec_ref(x_104);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_101);
lean_dec(x_5);
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_103, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_112 = x_103;
} else {
 lean_dec_ref(x_103);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_114 = lean_ctor_get(x_100, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_115 = x_100;
} else {
 lean_dec_ref(x_100);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_89);
lean_free_object(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_117 = lean_ctor_get(x_95, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_118 = x_95;
} else {
 lean_dec_ref(x_95);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_120 = lean_ctor_get(x_88, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_121 = x_88;
} else {
 lean_dec_ref(x_88);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
}
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_38, 0);
lean_inc(x_123);
lean_dec(x_38);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
x_128 = lean_array_get_size(x_19);
x_129 = l_Lean_Compiler_LCNF_Decl_getArity(x_126);
lean_dec(x_126);
x_130 = lean_nat_dec_lt(x_128, x_129);
lean_dec(x_129);
lean_dec(x_128);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_127);
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
else
{
lean_object* x_133; 
lean_inc_ref(x_16);
x_133 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; size_t x_135; size_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_array_size(x_134);
x_136 = 0;
lean_inc(x_134);
x_137 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_135, x_136, x_134);
x_138 = l_Array_append___redArg(x_19, x_137);
lean_dec_ref(x_137);
lean_ctor_set(x_13, 2, x_138);
x_139 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_140 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_139, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_ctor_set_tag(x_23, 5);
lean_ctor_set(x_23, 0, x_142);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_23);
x_144 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_145 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_134, x_143, x_144, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_inc(x_15);
x_148 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_147, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
lean_dec_ref(x_148);
x_149 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_150 = x_149;
} else {
 lean_dec_ref(x_149);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_127;
}
lean_ctor_set(x_151, 0, x_146);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 1, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_146);
lean_dec(x_127);
x_153 = lean_ctor_get(x_149, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_154 = x_149;
} else {
 lean_dec_ref(x_149);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_146);
lean_dec(x_127);
lean_dec(x_5);
lean_dec_ref(x_1);
x_156 = lean_ctor_get(x_148, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_157 = x_148;
} else {
 lean_dec_ref(x_148);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_127);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_159 = lean_ctor_get(x_145, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_160 = x_145;
} else {
 lean_dec_ref(x_145);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_134);
lean_dec(x_127);
lean_free_object(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_162 = lean_ctor_get(x_140, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_163 = x_140;
} else {
 lean_dec_ref(x_140);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_127);
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_165 = lean_ctor_get(x_133, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_166 = x_133;
} else {
 lean_dec_ref(x_133);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_165);
return x_167;
}
}
}
}
}
else
{
uint8_t x_168; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_168 = !lean_is_exclusive(x_38);
if (x_168 == 0)
{
return x_38;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_38, 0);
lean_inc(x_169);
lean_dec(x_38);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
}
else
{
lean_object* x_171; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_171 = lean_box(0);
lean_ctor_set(x_34, 0, x_171);
return x_34;
}
}
else
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_34, 0);
lean_inc(x_172);
lean_dec(x_34);
x_173 = lean_unbox(x_172);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; 
lean_inc(x_17);
x_174 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_177; lean_object* x_178; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_177 = lean_box(0);
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(0, 1, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_179 = lean_ctor_get(x_175, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_180 = x_175;
} else {
 lean_dec_ref(x_175);
 x_180 = lean_box(0);
}
x_181 = lean_array_get_size(x_19);
x_182 = l_Lean_Compiler_LCNF_Decl_getArity(x_179);
lean_dec(x_179);
x_183 = lean_nat_dec_lt(x_181, x_182);
lean_dec(x_182);
lean_dec(x_181);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_180);
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_184 = lean_box(0);
if (lean_is_scalar(x_176)) {
 x_185 = lean_alloc_ctor(0, 1, 0);
} else {
 x_185 = x_176;
}
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
else
{
lean_object* x_186; 
lean_dec(x_176);
lean_inc_ref(x_16);
x_186 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; size_t x_188; size_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec_ref(x_186);
x_188 = lean_array_size(x_187);
x_189 = 0;
lean_inc(x_187);
x_190 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_188, x_189, x_187);
x_191 = l_Array_append___redArg(x_19, x_190);
lean_dec_ref(x_190);
lean_ctor_set(x_13, 2, x_191);
x_192 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_193 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_192, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_ctor_set_tag(x_23, 5);
lean_ctor_set(x_23, 0, x_195);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_23);
x_197 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_198 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_187, x_196, x_197, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec_ref(x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
lean_inc(x_15);
x_201 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_200, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; 
lean_dec_ref(x_201);
x_202 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_203 = x_202;
} else {
 lean_dec_ref(x_202);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_180;
}
lean_ctor_set(x_204, 0, x_199);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 1, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_199);
lean_dec(x_180);
x_206 = lean_ctor_get(x_202, 0);
lean_inc(x_206);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_207 = x_202;
} else {
 lean_dec_ref(x_202);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 1, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_199);
lean_dec(x_180);
lean_dec(x_5);
lean_dec_ref(x_1);
x_209 = lean_ctor_get(x_201, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_210 = x_201;
} else {
 lean_dec_ref(x_201);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 1, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_209);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_180);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_212 = lean_ctor_get(x_198, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_213 = x_198;
} else {
 lean_dec_ref(x_198);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 1, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_187);
lean_dec(x_180);
lean_free_object(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_215 = lean_ctor_get(x_193, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_216 = x_193;
} else {
 lean_dec_ref(x_193);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_180);
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_218 = lean_ctor_get(x_186, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_219 = x_186;
} else {
 lean_dec_ref(x_186);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 1, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_218);
return x_220;
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_221 = lean_ctor_get(x_174, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_222 = x_174;
} else {
 lean_dec_ref(x_174);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_221);
return x_223;
}
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_224 = lean_box(0);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_224);
return x_225;
}
}
}
else
{
uint8_t x_226; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_226 = !lean_is_exclusive(x_34);
if (x_226 == 0)
{
return x_34;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_34, 0);
lean_inc(x_227);
lean_dec(x_34);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_227);
return x_228;
}
}
}
}
else
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_ctor_get(x_29, 0);
lean_inc(x_229);
lean_dec(x_29);
x_230 = lean_unbox(x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_231 = lean_box(0);
x_232 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_232, 0, x_231);
return x_232;
}
else
{
lean_object* x_233; 
x_233 = l_Lean_Meta_isInstance___redArg(x_17, x_7);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 x_235 = x_233;
} else {
 lean_dec_ref(x_233);
 x_235 = lean_box(0);
}
x_236 = lean_unbox(x_234);
lean_dec(x_234);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec(x_235);
lean_inc(x_17);
x_237 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_240 = lean_box(0);
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(0, 1, 0);
} else {
 x_241 = x_239;
}
lean_ctor_set(x_241, 0, x_240);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_242 = lean_ctor_get(x_238, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 x_243 = x_238;
} else {
 lean_dec_ref(x_238);
 x_243 = lean_box(0);
}
x_244 = lean_array_get_size(x_19);
x_245 = l_Lean_Compiler_LCNF_Decl_getArity(x_242);
lean_dec(x_242);
x_246 = lean_nat_dec_lt(x_244, x_245);
lean_dec(x_245);
lean_dec(x_244);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
lean_dec(x_243);
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_247 = lean_box(0);
if (lean_is_scalar(x_239)) {
 x_248 = lean_alloc_ctor(0, 1, 0);
} else {
 x_248 = x_239;
}
lean_ctor_set(x_248, 0, x_247);
return x_248;
}
else
{
lean_object* x_249; 
lean_dec(x_239);
lean_inc_ref(x_16);
x_249 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; size_t x_251; size_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = lean_array_size(x_250);
x_252 = 0;
lean_inc(x_250);
x_253 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_251, x_252, x_250);
x_254 = l_Array_append___redArg(x_19, x_253);
lean_dec_ref(x_253);
lean_ctor_set(x_13, 2, x_254);
x_255 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_256 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_255, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_ctor_set_tag(x_23, 5);
lean_ctor_set(x_23, 0, x_258);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_23);
x_260 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_261 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_250, x_259, x_260, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_inc(x_15);
x_264 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_263, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; 
lean_dec_ref(x_264);
x_265 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_266 = x_265;
} else {
 lean_dec_ref(x_265);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_267 = lean_alloc_ctor(1, 1, 0);
} else {
 x_267 = x_243;
}
lean_ctor_set(x_267, 0, x_262);
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(0, 1, 0);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_267);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_262);
lean_dec(x_243);
x_269 = lean_ctor_get(x_265, 0);
lean_inc(x_269);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_270 = x_265;
} else {
 lean_dec_ref(x_265);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 1, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_269);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_262);
lean_dec(x_243);
lean_dec(x_5);
lean_dec_ref(x_1);
x_272 = lean_ctor_get(x_264, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 x_273 = x_264;
} else {
 lean_dec_ref(x_264);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 1, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_243);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_275 = lean_ctor_get(x_261, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_276 = x_261;
} else {
 lean_dec_ref(x_261);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_275);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_250);
lean_dec(x_243);
lean_free_object(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_278 = lean_ctor_get(x_256, 0);
lean_inc(x_278);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_279 = x_256;
} else {
 lean_dec_ref(x_256);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 1, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_243);
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_281 = lean_ctor_get(x_249, 0);
lean_inc(x_281);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 x_282 = x_249;
} else {
 lean_dec_ref(x_249);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 1, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_281);
return x_283;
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_284 = lean_ctor_get(x_237, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_285 = x_237;
} else {
 lean_dec_ref(x_237);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 1, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_284);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_287 = lean_box(0);
if (lean_is_scalar(x_235)) {
 x_288 = lean_alloc_ctor(0, 1, 0);
} else {
 x_288 = x_235;
}
lean_ctor_set(x_288, 0, x_287);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_289 = lean_ctor_get(x_233, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 x_290 = x_233;
} else {
 lean_dec_ref(x_233);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_289);
return x_291;
}
}
}
}
else
{
uint8_t x_292; 
lean_free_object(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_292 = !lean_is_exclusive(x_29);
if (x_292 == 0)
{
return x_29;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_29, 0);
lean_inc(x_293);
lean_dec(x_29);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_23, 0);
lean_inc(x_295);
lean_dec(x_23);
x_296 = l_Lean_ConstantInfo_type(x_295);
lean_dec(x_295);
x_297 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_296, x_7);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 x_299 = x_297;
} else {
 lean_dec_ref(x_297);
 x_299 = lean_box(0);
}
x_300 = lean_unbox(x_298);
lean_dec(x_298);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_301 = lean_box(0);
if (lean_is_scalar(x_299)) {
 x_302 = lean_alloc_ctor(0, 1, 0);
} else {
 x_302 = x_299;
}
lean_ctor_set(x_302, 0, x_301);
return x_302;
}
else
{
lean_object* x_303; 
lean_dec(x_299);
x_303 = l_Lean_Meta_isInstance___redArg(x_17, x_7);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 x_305 = x_303;
} else {
 lean_dec_ref(x_303);
 x_305 = lean_box(0);
}
x_306 = lean_unbox(x_304);
lean_dec(x_304);
if (x_306 == 0)
{
lean_object* x_307; 
lean_dec(x_305);
lean_inc(x_17);
x_307 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_309 = x_307;
} else {
 lean_dec_ref(x_307);
 x_309 = lean_box(0);
}
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_310; lean_object* x_311; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_310 = lean_box(0);
if (lean_is_scalar(x_309)) {
 x_311 = lean_alloc_ctor(0, 1, 0);
} else {
 x_311 = x_309;
}
lean_ctor_set(x_311, 0, x_310);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_308, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 x_313 = x_308;
} else {
 lean_dec_ref(x_308);
 x_313 = lean_box(0);
}
x_314 = lean_array_get_size(x_19);
x_315 = l_Lean_Compiler_LCNF_Decl_getArity(x_312);
lean_dec(x_312);
x_316 = lean_nat_dec_lt(x_314, x_315);
lean_dec(x_315);
lean_dec(x_314);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
lean_dec(x_313);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_317 = lean_box(0);
if (lean_is_scalar(x_309)) {
 x_318 = lean_alloc_ctor(0, 1, 0);
} else {
 x_318 = x_309;
}
lean_ctor_set(x_318, 0, x_317);
return x_318;
}
else
{
lean_object* x_319; 
lean_dec(x_309);
lean_inc_ref(x_16);
x_319 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; size_t x_321; size_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
lean_dec_ref(x_319);
x_321 = lean_array_size(x_320);
x_322 = 0;
lean_inc(x_320);
x_323 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_321, x_322, x_320);
x_324 = l_Array_append___redArg(x_19, x_323);
lean_dec_ref(x_323);
lean_ctor_set(x_13, 2, x_324);
x_325 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_326 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_325, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
lean_dec_ref(x_326);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_329, 0, x_328);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_329);
x_331 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_332 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_320, x_330, x_331, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
lean_dec_ref(x_332);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
lean_inc(x_15);
x_335 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_334, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; 
lean_dec_ref(x_335);
x_336 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_337 = x_336;
} else {
 lean_dec_ref(x_336);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_338 = lean_alloc_ctor(1, 1, 0);
} else {
 x_338 = x_313;
}
lean_ctor_set(x_338, 0, x_333);
if (lean_is_scalar(x_337)) {
 x_339 = lean_alloc_ctor(0, 1, 0);
} else {
 x_339 = x_337;
}
lean_ctor_set(x_339, 0, x_338);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_333);
lean_dec(x_313);
x_340 = lean_ctor_get(x_336, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_341 = x_336;
} else {
 lean_dec_ref(x_336);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 1, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_340);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_333);
lean_dec(x_313);
lean_dec(x_5);
lean_dec_ref(x_1);
x_343 = lean_ctor_get(x_335, 0);
lean_inc(x_343);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_344 = x_335;
} else {
 lean_dec_ref(x_335);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(1, 1, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_343);
return x_345;
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_313);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_346 = lean_ctor_get(x_332, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 x_347 = x_332;
} else {
 lean_dec_ref(x_332);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 1, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_346);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_320);
lean_dec(x_313);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_349 = lean_ctor_get(x_326, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_350 = x_326;
} else {
 lean_dec_ref(x_326);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 1, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_349);
return x_351;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_313);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_352 = lean_ctor_get(x_319, 0);
lean_inc(x_352);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 x_353 = x_319;
} else {
 lean_dec_ref(x_319);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 1, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_352);
return x_354;
}
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_355 = lean_ctor_get(x_307, 0);
lean_inc(x_355);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_356 = x_307;
} else {
 lean_dec_ref(x_307);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 1, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_355);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_358 = lean_box(0);
if (lean_is_scalar(x_305)) {
 x_359 = lean_alloc_ctor(0, 1, 0);
} else {
 x_359 = x_305;
}
lean_ctor_set(x_359, 0, x_358);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_360 = lean_ctor_get(x_303, 0);
lean_inc(x_360);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 x_361 = x_303;
} else {
 lean_dec_ref(x_303);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 1, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_360);
return x_362;
}
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_363 = lean_ctor_get(x_297, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 x_364 = x_297;
} else {
 lean_dec_ref(x_297);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 1, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_363);
return x_365;
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; 
x_366 = lean_ctor_get(x_1, 0);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_13, 0);
x_369 = lean_ctor_get(x_13, 1);
x_370 = lean_ctor_get(x_13, 2);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_13);
x_371 = lean_st_ref_get(x_7);
x_372 = lean_ctor_get(x_371, 0);
lean_inc_ref(x_372);
lean_dec_ref(x_371);
x_373 = 0;
lean_inc(x_368);
x_374 = l_Lean_Environment_find_x3f(x_372, x_368, x_373);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; 
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_375 = lean_box(0);
x_376 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_376, 0, x_375);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_377 = lean_ctor_get(x_374, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_378 = x_374;
} else {
 lean_dec_ref(x_374);
 x_378 = lean_box(0);
}
x_379 = l_Lean_ConstantInfo_type(x_377);
lean_dec(x_377);
x_380 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_379, x_7);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 x_382 = x_380;
} else {
 lean_dec_ref(x_380);
 x_382 = lean_box(0);
}
x_383 = lean_unbox(x_381);
lean_dec(x_381);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_378);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_384 = lean_box(0);
if (lean_is_scalar(x_382)) {
 x_385 = lean_alloc_ctor(0, 1, 0);
} else {
 x_385 = x_382;
}
lean_ctor_set(x_385, 0, x_384);
return x_385;
}
else
{
lean_object* x_386; 
lean_dec(x_382);
x_386 = l_Lean_Meta_isInstance___redArg(x_368, x_7);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 x_388 = x_386;
} else {
 lean_dec_ref(x_386);
 x_388 = lean_box(0);
}
x_389 = lean_unbox(x_387);
lean_dec(x_387);
if (x_389 == 0)
{
lean_object* x_390; 
lean_dec(x_388);
lean_inc(x_368);
x_390 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_368, x_4, x_7);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_392 = x_390;
} else {
 lean_dec_ref(x_390);
 x_392 = lean_box(0);
}
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_393; lean_object* x_394; 
lean_dec(x_378);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_393 = lean_box(0);
if (lean_is_scalar(x_392)) {
 x_394 = lean_alloc_ctor(0, 1, 0);
} else {
 x_394 = x_392;
}
lean_ctor_set(x_394, 0, x_393);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_395 = lean_ctor_get(x_391, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 x_396 = x_391;
} else {
 lean_dec_ref(x_391);
 x_396 = lean_box(0);
}
x_397 = lean_array_get_size(x_370);
x_398 = l_Lean_Compiler_LCNF_Decl_getArity(x_395);
lean_dec(x_395);
x_399 = lean_nat_dec_lt(x_397, x_398);
lean_dec(x_398);
lean_dec(x_397);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; 
lean_dec(x_396);
lean_dec(x_378);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_400 = lean_box(0);
if (lean_is_scalar(x_392)) {
 x_401 = lean_alloc_ctor(0, 1, 0);
} else {
 x_401 = x_392;
}
lean_ctor_set(x_401, 0, x_400);
return x_401;
}
else
{
lean_object* x_402; 
lean_dec(x_392);
lean_inc_ref(x_367);
x_402 = l_Lean_Compiler_LCNF_mkNewParams(x_367, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; size_t x_404; size_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
lean_dec_ref(x_402);
x_404 = lean_array_size(x_403);
x_405 = 0;
lean_inc(x_403);
x_406 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_404, x_405, x_403);
x_407 = l_Array_append___redArg(x_370, x_406);
lean_dec_ref(x_406);
x_408 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_408, 0, x_368);
lean_ctor_set(x_408, 1, x_369);
lean_ctor_set(x_408, 2, x_407);
x_409 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_410 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_408, x_409, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
lean_dec_ref(x_410);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
if (lean_is_scalar(x_378)) {
 x_413 = lean_alloc_ctor(5, 1, 0);
} else {
 x_413 = x_378;
 lean_ctor_set_tag(x_413, 5);
}
lean_ctor_set(x_413, 0, x_412);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_413);
x_415 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_416 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_403, x_414, x_415, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
lean_dec_ref(x_416);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
lean_inc(x_366);
x_419 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_366, x_418, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; 
lean_dec_ref(x_419);
x_420 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 x_421 = x_420;
} else {
 lean_dec_ref(x_420);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_422 = lean_alloc_ctor(1, 1, 0);
} else {
 x_422 = x_396;
}
lean_ctor_set(x_422, 0, x_417);
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(0, 1, 0);
} else {
 x_423 = x_421;
}
lean_ctor_set(x_423, 0, x_422);
return x_423;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_417);
lean_dec(x_396);
x_424 = lean_ctor_get(x_420, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 x_425 = x_420;
} else {
 lean_dec_ref(x_420);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 1, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_424);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_417);
lean_dec(x_396);
lean_dec(x_5);
lean_dec_ref(x_1);
x_427 = lean_ctor_get(x_419, 0);
lean_inc(x_427);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 x_428 = x_419;
} else {
 lean_dec_ref(x_419);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 1, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_427);
return x_429;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_396);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_430 = lean_ctor_get(x_416, 0);
lean_inc(x_430);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_431 = x_416;
} else {
 lean_dec_ref(x_416);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 1, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_430);
return x_432;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_403);
lean_dec(x_396);
lean_dec(x_378);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_433 = lean_ctor_get(x_410, 0);
lean_inc(x_433);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 x_434 = x_410;
} else {
 lean_dec_ref(x_410);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 1, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_433);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_396);
lean_dec(x_378);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_436 = lean_ctor_get(x_402, 0);
lean_inc(x_436);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 x_437 = x_402;
} else {
 lean_dec_ref(x_402);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 1, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_436);
return x_438;
}
}
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_378);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_439 = lean_ctor_get(x_390, 0);
lean_inc(x_439);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_440 = x_390;
} else {
 lean_dec_ref(x_390);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 1, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; 
lean_dec(x_378);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_442 = lean_box(0);
if (lean_is_scalar(x_388)) {
 x_443 = lean_alloc_ctor(0, 1, 0);
} else {
 x_443 = x_388;
}
lean_ctor_set(x_443, 0, x_442);
return x_443;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_378);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_444 = lean_ctor_get(x_386, 0);
lean_inc(x_444);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 x_445 = x_386;
} else {
 lean_dec_ref(x_386);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(1, 1, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_444);
return x_446;
}
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_378);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_447 = lean_ctor_get(x_380, 0);
lean_inc(x_447);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 x_448 = x_380;
} else {
 lean_dec_ref(x_380);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 1, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_447);
return x_449;
}
}
}
}
else
{
lean_object* x_450; lean_object* x_451; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_450 = lean_box(0);
x_451 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_451, 0, x_450);
return x_451;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_st_ref_get(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = 0;
x_10 = l_Lean_Compiler_LCNF_normFVarImp(x_8, x_6, x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_free_object(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_instBEqFVarId_beq(x_12, x_2);
lean_dec(x_12);
x_14 = lean_box(x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_instBEqFVarId_beq(x_15, x_2);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_box(x_9);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_st_ref_get(x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_21);
x_23 = 0;
x_24 = l_Lean_Compiler_LCNF_normFVarImp(x_22, x_20, x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = l_Lean_instBEqFVarId_beq(x_25, x_2);
lean_dec(x_25);
x_28 = lean_box(x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(x_23);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_1);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(x_1, x_2, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_isReturnOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
x_3 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
x_3 = lean_box(0);
goto block_6;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = lean_name_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = lean_name_eq(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Name_hash___override(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_name_eq(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_name_eq(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_34; 
x_34 = lean_nat_dec_lt(x_1, x_2);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3, x_6, x_8, x_11, x_12, x_13);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec_ref(x_35);
x_36 = l_Lean_Compiler_LCNF_Simp_simp(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_le(x_1, x_40);
if (x_41 == 0)
{
x_15 = x_1;
x_16 = x_2;
goto block_33;
}
else
{
lean_dec(x_1);
x_15 = x_40;
x_16 = x_2;
goto block_33;
}
}
block_33:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Array_toSubarray___redArg(x_5, x_15, x_16);
x_18 = l_Array_ofSubarray___redArg(x_17);
lean_dec_ref(x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_21 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_19, x_20, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3, x_23, x_8, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_4);
x_26 = l_Lean_Compiler_LCNF_Simp_simp(x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_mk_empty_array_with_capacity(x_2);
x_12 = lean_array_push(x_11, x_10);
lean_inc(x_9);
x_13 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_5, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_11);
x_12 = lean_apply_9(x_2, x_5, x_3, x_1, x_4, x_6, x_7, x_8, x_9, lean_box(0));
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_jp", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec_ref(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_free_object(x_13);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 2);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_ctor_get_uint8(x_17, sizeof(void*)*4 + 2);
x_24 = lean_array_get_size(x_22);
x_25 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_17);
lean_inc_ref(x_22);
lean_inc_ref(x_2);
lean_inc(x_11);
lean_inc(x_24);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 14, 5);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_24);
lean_closure_set(x_26, 2, x_11);
lean_closure_set(x_26, 3, x_2);
lean_closure_set(x_26, 4, x_22);
x_27 = lean_nat_dec_lt(x_24, x_25);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_12, 0);
lean_inc(x_203);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_203);
x_204 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(x_23, x_203, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = !lean_is_exclusive(x_3);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_3, 2);
x_208 = lean_ctor_get(x_3, 3);
lean_inc(x_203);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_203);
lean_ctor_set(x_209, 1, x_207);
x_210 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_208, x_203, x_205);
lean_ctor_set(x_3, 3, x_210);
lean_ctor_set(x_3, 2, x_209);
x_166 = x_3;
x_167 = x_4;
x_168 = x_5;
x_169 = x_6;
x_170 = x_7;
x_171 = x_8;
x_172 = x_9;
x_173 = lean_box(0);
goto block_202;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_211 = lean_ctor_get(x_3, 0);
x_212 = lean_ctor_get(x_3, 1);
x_213 = lean_ctor_get(x_3, 2);
x_214 = lean_ctor_get(x_3, 3);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_3);
lean_inc(x_203);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_203);
lean_ctor_set(x_215, 1, x_213);
x_216 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_214, x_203, x_205);
x_217 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_217, 0, x_211);
lean_ctor_set(x_217, 1, x_212);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_216);
x_166 = x_217;
x_167 = x_4;
x_168 = x_5;
x_169 = x_6;
x_170 = x_7;
x_171 = x_8;
x_172 = x_9;
x_173 = lean_box(0);
goto block_202;
}
}
else
{
uint8_t x_218; 
lean_dec(x_203);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_218 = !lean_is_exclusive(x_204);
if (x_218 == 0)
{
return x_204;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_204, 0);
lean_inc(x_219);
lean_dec(x_204);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
}
}
else
{
lean_dec(x_12);
x_166 = x_3;
x_167 = x_4;
x_168 = x_5;
x_169 = x_6;
x_170 = x_7;
x_171 = x_8;
x_172 = x_9;
x_173 = lean_box(0);
goto block_202;
}
block_130:
{
lean_object* x_39; 
lean_inc(x_36);
lean_inc_ref(x_33);
lean_inc(x_37);
lean_inc_ref(x_34);
lean_inc_ref(x_38);
lean_inc(x_28);
lean_inc_ref(x_29);
x_39 = l_Lean_Compiler_LCNF_Simp_simp(x_30, x_29, x_28, x_38, x_34, x_37, x_33, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_28);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec_ref(x_41);
lean_inc(x_40);
x_42 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec_ref(x_31);
x_43 = l_Lean_Compiler_LCNF_inferAppType(x_21, x_35, x_34, x_37, x_33, x_36);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
lean_inc(x_44);
x_45 = l_Lean_Expr_headBeta(x_44);
x_46 = l_Lean_Expr_isForall(x_45);
lean_dec_ref(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = l_Lean_Compiler_LCNF_mkAuxParam(x_44, x_27, x_34, x_37, x_33, x_36);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_36);
lean_inc_ref(x_33);
lean_inc(x_37);
lean_inc_ref(x_34);
lean_inc(x_49);
x_50 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_25, x_24, x_11, x_2, x_22, x_49, x_29, x_28, x_38, x_34, x_37, x_33, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_unsigned_to_nat(1u);
x_53 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_54 = lean_array_push(x_53, x_48);
x_55 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_56 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_54, x_51, x_55, x_34, x_37, x_33, x_36);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
lean_inc(x_57);
x_58 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_58, 0, x_57);
lean_closure_set(x_58, 1, x_52);
x_59 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_58, x_34, x_37, x_33, x_36);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_18)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_18;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_59, 0, x_63);
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_18)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_18;
}
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_57);
lean_dec(x_18);
x_68 = !lean_is_exclusive(x_59);
if (x_68 == 0)
{
return x_59;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec(x_59);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_18);
x_71 = !lean_is_exclusive(x_56);
if (x_71 == 0)
{
return x_56;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_56, 0);
lean_inc(x_72);
lean_dec(x_56);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_18);
x_74 = !lean_is_exclusive(x_50);
if (x_74 == 0)
{
return x_50;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_50, 0);
lean_inc(x_75);
lean_dec(x_50);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_40);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec(x_18);
lean_dec(x_11);
lean_dec_ref(x_2);
x_77 = !lean_is_exclusive(x_47);
if (x_77 == 0)
{
return x_47;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_47, 0);
lean_inc(x_78);
lean_dec(x_47);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_44);
x_80 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
x_81 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_82 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_80, x_40, x_81, x_34, x_37, x_33, x_36);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc(x_36);
lean_inc_ref(x_33);
lean_inc(x_37);
lean_inc_ref(x_34);
x_84 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_83, x_34, x_37, x_33, x_36);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_36);
lean_inc_ref(x_33);
lean_inc(x_37);
lean_inc_ref(x_34);
lean_inc_ref(x_38);
lean_inc(x_28);
lean_inc_ref(x_29);
lean_inc(x_86);
x_87 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_25, x_24, x_11, x_2, x_22, x_86, x_29, x_28, x_38, x_34, x_37, x_33, x_36);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_85);
x_90 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_91 = lean_array_push(x_90, x_89);
x_92 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_91, x_88, x_29, x_28, x_38, x_34, x_37, x_33, x_36);
lean_dec(x_36);
lean_dec_ref(x_33);
lean_dec(x_37);
lean_dec_ref(x_34);
lean_dec_ref(x_38);
lean_dec(x_28);
lean_dec_ref(x_29);
lean_dec_ref(x_91);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
if (lean_is_scalar(x_18)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_18;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_92, 0, x_95);
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
lean_dec(x_92);
if (lean_is_scalar(x_18)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_18;
}
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_18);
x_99 = !lean_is_exclusive(x_92);
if (x_99 == 0)
{
return x_92;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_92, 0);
lean_inc(x_100);
lean_dec(x_92);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_85);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_18);
x_102 = !lean_is_exclusive(x_87);
if (x_102 == 0)
{
return x_87;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_87, 0);
lean_inc(x_103);
lean_dec(x_87);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec(x_18);
lean_dec(x_11);
lean_dec_ref(x_2);
x_105 = !lean_is_exclusive(x_84);
if (x_105 == 0)
{
return x_84;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_84, 0);
lean_inc(x_106);
lean_dec(x_84);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec(x_18);
lean_dec(x_11);
lean_dec_ref(x_2);
x_108 = !lean_is_exclusive(x_82);
if (x_108 == 0)
{
return x_82;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_82, 0);
lean_inc(x_109);
lean_dec(x_82);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_40);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec(x_18);
lean_dec(x_11);
lean_dec_ref(x_2);
x_111 = !lean_is_exclusive(x_43);
if (x_111 == 0)
{
return x_43;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_43, 0);
lean_inc(x_112);
lean_dec(x_43);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; 
lean_dec_ref(x_38);
lean_dec_ref(x_35);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_11);
lean_dec_ref(x_2);
x_114 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_31, x_34, x_37, x_33, x_36);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
if (lean_is_scalar(x_18)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_18;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_114, 0, x_117);
return x_114;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
lean_dec(x_114);
if (lean_is_scalar(x_18)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_18;
}
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_dec(x_18);
x_121 = !lean_is_exclusive(x_114);
if (x_121 == 0)
{
return x_114;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_114, 0);
lean_inc(x_122);
lean_dec(x_114);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_40);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_11);
lean_dec_ref(x_2);
x_124 = !lean_is_exclusive(x_41);
if (x_124 == 0)
{
return x_41;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_41, 0);
lean_inc(x_125);
lean_dec(x_41);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_11);
lean_dec_ref(x_2);
x_127 = !lean_is_exclusive(x_39);
if (x_127 == 0)
{
return x_39;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_39, 0);
lean_inc(x_128);
lean_dec(x_39);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
block_165:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_inc_ref(x_22);
x_142 = l_Array_toSubarray___redArg(x_22, x_140, x_141);
x_143 = l_Array_ofSubarray___redArg(x_142);
lean_dec_ref(x_142);
lean_inc(x_137);
lean_inc_ref(x_135);
lean_inc(x_138);
lean_inc_ref(x_136);
lean_inc_ref(x_143);
x_144 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_19, x_20, x_143, x_27, x_132, x_131, x_139, x_136, x_138, x_135, x_137);
lean_dec_ref(x_19);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_11);
if (x_146 == 0)
{
x_28 = x_131;
x_29 = x_132;
x_30 = x_145;
x_31 = x_133;
x_32 = lean_box(0);
x_33 = x_135;
x_34 = x_136;
x_35 = x_143;
x_36 = x_137;
x_37 = x_138;
x_38 = x_139;
goto block_130;
}
else
{
uint8_t x_147; 
x_147 = lean_nat_dec_eq(x_24, x_25);
if (x_147 == 0)
{
x_28 = x_131;
x_29 = x_132;
x_30 = x_145;
x_31 = x_133;
x_32 = lean_box(0);
x_33 = x_135;
x_34 = x_136;
x_35 = x_143;
x_36 = x_137;
x_37 = x_138;
x_38 = x_139;
goto block_130;
}
else
{
lean_object* x_148; 
lean_dec_ref(x_143);
lean_dec_ref(x_133);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_11);
lean_dec_ref(x_2);
x_148 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_131);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
lean_dec_ref(x_148);
x_149 = l_Lean_Compiler_LCNF_Simp_simp(x_145, x_132, x_131, x_139, x_136, x_138, x_135, x_137);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_149, 0);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_149, 0, x_152);
return x_149;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_149, 0);
lean_inc(x_153);
lean_dec(x_149);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
else
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_149);
if (x_156 == 0)
{
return x_149;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_149, 0);
lean_inc(x_157);
lean_dec(x_149);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_145);
lean_dec_ref(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec_ref(x_135);
lean_dec_ref(x_132);
lean_dec(x_131);
x_159 = !lean_is_exclusive(x_148);
if (x_159 == 0)
{
return x_148;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_148, 0);
lean_inc(x_160);
lean_dec(x_148);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
}
}
else
{
uint8_t x_162; 
lean_dec_ref(x_143);
lean_dec_ref(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec_ref(x_135);
lean_dec_ref(x_133);
lean_dec_ref(x_132);
lean_dec(x_131);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_11);
lean_dec_ref(x_2);
x_162 = !lean_is_exclusive(x_144);
if (x_162 == 0)
{
return x_144;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_144, 0);
lean_inc(x_163);
lean_dec(x_144);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
}
}
block_202:
{
if (x_27 == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
lean_inc_ref(x_22);
lean_inc_ref(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_19);
lean_dec(x_17);
lean_inc_ref(x_168);
lean_inc_ref(x_166);
lean_inc(x_167);
x_174 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(x_174, 0, x_167);
lean_closure_set(x_174, 1, x_26);
lean_closure_set(x_174, 2, x_166);
lean_closure_set(x_174, 3, x_168);
x_175 = lean_unsigned_to_nat(0u);
x_176 = lean_nat_dec_le(x_25, x_24);
if (x_176 == 0)
{
lean_inc(x_24);
x_131 = x_167;
x_132 = x_166;
x_133 = x_174;
x_134 = lean_box(0);
x_135 = x_171;
x_136 = x_169;
x_137 = x_172;
x_138 = x_170;
x_139 = x_168;
x_140 = x_175;
x_141 = x_24;
goto block_165;
}
else
{
lean_inc(x_25);
x_131 = x_167;
x_132 = x_166;
x_133 = x_174;
x_134 = lean_box(0);
x_135 = x_171;
x_136 = x_169;
x_137 = x_172;
x_138 = x_170;
x_139 = x_168;
x_140 = x_175;
x_141 = x_25;
goto block_165;
}
}
else
{
lean_object* x_177; 
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_inc(x_172);
lean_inc_ref(x_171);
lean_inc(x_170);
lean_inc_ref(x_169);
x_177 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_17, x_166, x_167, x_168, x_169, x_170, x_171, x_172);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_179, x_167, x_170, x_171, x_172);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
lean_dec_ref(x_180);
x_181 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_167);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec_ref(x_181);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_2);
x_183 = l_Lean_Compiler_LCNF_Simp_simp(x_182, x_166, x_167, x_168, x_169, x_170, x_171, x_172);
if (lean_obj_tag(x_183) == 0)
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_183, 0);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_183, 0, x_186);
return x_183;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
lean_dec(x_183);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_188);
return x_189;
}
}
else
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_183);
if (x_190 == 0)
{
return x_183;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_183, 0);
lean_inc(x_191);
lean_dec(x_183);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_178);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec(x_170);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec(x_167);
lean_dec_ref(x_166);
lean_dec_ref(x_2);
x_193 = !lean_is_exclusive(x_181);
if (x_193 == 0)
{
return x_181;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_181, 0);
lean_inc(x_194);
lean_dec(x_181);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_178);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec(x_170);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec(x_167);
lean_dec_ref(x_166);
lean_dec_ref(x_2);
x_196 = !lean_is_exclusive(x_180);
if (x_196 == 0)
{
return x_180;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_180, 0);
lean_inc(x_197);
lean_dec(x_180);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec(x_170);
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_dec(x_167);
lean_dec_ref(x_166);
lean_dec(x_11);
lean_dec_ref(x_2);
x_199 = !lean_is_exclusive(x_177);
if (x_199 == 0)
{
return x_177;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_177, 0);
lean_inc(x_200);
lean_dec(x_177);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
}
}
}
else
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_13, 0);
lean_inc(x_221);
lean_dec(x_13);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_222 = lean_box(0);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_222);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_224 = lean_ctor_get(x_221, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_225 = x_221;
} else {
 lean_dec_ref(x_221);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_224, 0);
x_227 = lean_ctor_get(x_224, 1);
x_228 = lean_ctor_get(x_224, 2);
x_229 = lean_ctor_get(x_224, 3);
x_230 = lean_ctor_get_uint8(x_224, sizeof(void*)*4 + 2);
x_231 = lean_array_get_size(x_229);
x_232 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_224);
lean_inc_ref(x_229);
lean_inc_ref(x_2);
lean_inc(x_11);
lean_inc(x_231);
lean_inc(x_232);
x_233 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 14, 5);
lean_closure_set(x_233, 0, x_232);
lean_closure_set(x_233, 1, x_231);
lean_closure_set(x_233, 2, x_11);
lean_closure_set(x_233, 3, x_2);
lean_closure_set(x_233, 4, x_229);
x_234 = lean_nat_dec_lt(x_231, x_232);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_12, 0);
lean_inc(x_399);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_399);
x_400 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(x_230, x_399, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
x_402 = lean_ctor_get(x_3, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_403);
x_404 = lean_ctor_get(x_3, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_405);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_406 = x_3;
} else {
 lean_dec_ref(x_3);
 x_406 = lean_box(0);
}
lean_inc(x_399);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_399);
lean_ctor_set(x_407, 1, x_404);
x_408 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_405, x_399, x_401);
if (lean_is_scalar(x_406)) {
 x_409 = lean_alloc_ctor(0, 4, 0);
} else {
 x_409 = x_406;
}
lean_ctor_set(x_409, 0, x_402);
lean_ctor_set(x_409, 1, x_403);
lean_ctor_set(x_409, 2, x_407);
lean_ctor_set(x_409, 3, x_408);
x_364 = x_409;
x_365 = x_4;
x_366 = x_5;
x_367 = x_6;
x_368 = x_7;
x_369 = x_8;
x_370 = x_9;
x_371 = lean_box(0);
goto block_398;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_399);
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_410 = lean_ctor_get(x_400, 0);
lean_inc(x_410);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 x_411 = x_400;
} else {
 lean_dec_ref(x_400);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 1, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_410);
return x_412;
}
}
else
{
lean_dec(x_12);
x_364 = x_3;
x_365 = x_4;
x_366 = x_5;
x_367 = x_6;
x_368 = x_7;
x_369 = x_8;
x_370 = x_9;
x_371 = lean_box(0);
goto block_398;
}
block_330:
{
lean_object* x_246; 
lean_inc(x_243);
lean_inc_ref(x_240);
lean_inc(x_244);
lean_inc_ref(x_241);
lean_inc_ref(x_245);
lean_inc(x_235);
lean_inc_ref(x_236);
x_246 = l_Lean_Compiler_LCNF_Simp_simp(x_237, x_236, x_235, x_245, x_241, x_244, x_240, x_243);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_248 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_235);
if (lean_obj_tag(x_248) == 0)
{
uint8_t x_249; 
lean_dec_ref(x_248);
lean_inc(x_247);
x_249 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_247);
if (x_249 == 0)
{
lean_object* x_250; 
lean_dec_ref(x_238);
x_250 = l_Lean_Compiler_LCNF_inferAppType(x_228, x_242, x_241, x_244, x_240, x_243);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
lean_inc(x_251);
x_252 = l_Lean_Expr_headBeta(x_251);
x_253 = l_Lean_Expr_isForall(x_252);
lean_dec_ref(x_252);
if (x_253 == 0)
{
lean_object* x_254; 
x_254 = l_Lean_Compiler_LCNF_mkAuxParam(x_251, x_234, x_241, x_244, x_240, x_243);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_243);
lean_inc_ref(x_240);
lean_inc(x_244);
lean_inc_ref(x_241);
lean_inc(x_256);
x_257 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_232, x_231, x_11, x_2, x_229, x_256, x_236, x_235, x_245, x_241, x_244, x_240, x_243);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec_ref(x_257);
x_259 = lean_unsigned_to_nat(1u);
x_260 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_261 = lean_array_push(x_260, x_255);
x_262 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_263 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_261, x_258, x_262, x_241, x_244, x_240, x_243);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
lean_inc(x_264);
x_265 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_265, 0, x_264);
lean_closure_set(x_265, 1, x_259);
x_266 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_247, x_265, x_241, x_244, x_240, x_243);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 x_268 = x_266;
} else {
 lean_dec_ref(x_266);
 x_268 = lean_box(0);
}
x_269 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_269, 0, x_264);
lean_ctor_set(x_269, 1, x_267);
if (lean_is_scalar(x_225)) {
 x_270 = lean_alloc_ctor(1, 1, 0);
} else {
 x_270 = x_225;
}
lean_ctor_set(x_270, 0, x_269);
if (lean_is_scalar(x_268)) {
 x_271 = lean_alloc_ctor(0, 1, 0);
} else {
 x_271 = x_268;
}
lean_ctor_set(x_271, 0, x_270);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_264);
lean_dec(x_225);
x_272 = lean_ctor_get(x_266, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 x_273 = x_266;
} else {
 lean_dec_ref(x_266);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 1, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_247);
lean_dec(x_244);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec(x_225);
x_275 = lean_ctor_get(x_263, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_276 = x_263;
} else {
 lean_dec_ref(x_263);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_275);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_255);
lean_dec(x_247);
lean_dec(x_244);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec(x_225);
x_278 = lean_ctor_get(x_257, 0);
lean_inc(x_278);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_279 = x_257;
} else {
 lean_dec_ref(x_257);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 1, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_247);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec(x_225);
lean_dec(x_11);
lean_dec_ref(x_2);
x_281 = lean_ctor_get(x_254, 0);
lean_inc(x_281);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_282 = x_254;
} else {
 lean_dec_ref(x_254);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 1, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_281);
return x_283;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_251);
x_284 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
x_285 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_286 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_284, x_247, x_285, x_241, x_244, x_240, x_243);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec_ref(x_286);
lean_inc(x_243);
lean_inc_ref(x_240);
lean_inc(x_244);
lean_inc_ref(x_241);
x_288 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_287, x_241, x_244, x_240, x_243);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec_ref(x_288);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_243);
lean_inc_ref(x_240);
lean_inc(x_244);
lean_inc_ref(x_241);
lean_inc_ref(x_245);
lean_inc(x_235);
lean_inc_ref(x_236);
lean_inc(x_290);
x_291 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_232, x_231, x_11, x_2, x_229, x_290, x_236, x_235, x_245, x_241, x_244, x_240, x_243);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_289);
x_294 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_295 = lean_array_push(x_294, x_293);
x_296 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_295, x_292, x_236, x_235, x_245, x_241, x_244, x_240, x_243);
lean_dec(x_243);
lean_dec_ref(x_240);
lean_dec(x_244);
lean_dec_ref(x_241);
lean_dec_ref(x_245);
lean_dec(x_235);
lean_dec_ref(x_236);
lean_dec_ref(x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 x_298 = x_296;
} else {
 lean_dec_ref(x_296);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_299 = x_225;
}
lean_ctor_set(x_299, 0, x_297);
if (lean_is_scalar(x_298)) {
 x_300 = lean_alloc_ctor(0, 1, 0);
} else {
 x_300 = x_298;
}
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_225);
x_301 = lean_ctor_get(x_296, 0);
lean_inc(x_301);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 x_302 = x_296;
} else {
 lean_dec_ref(x_296);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 1, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_301);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_289);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_225);
x_304 = lean_ctor_get(x_291, 0);
lean_inc(x_304);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_305 = x_291;
} else {
 lean_dec_ref(x_291);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 1, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_304);
return x_306;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec(x_225);
lean_dec(x_11);
lean_dec_ref(x_2);
x_307 = lean_ctor_get(x_288, 0);
lean_inc(x_307);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 x_308 = x_288;
} else {
 lean_dec_ref(x_288);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 1, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_307);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec(x_225);
lean_dec(x_11);
lean_dec_ref(x_2);
x_310 = lean_ctor_get(x_286, 0);
lean_inc(x_310);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 x_311 = x_286;
} else {
 lean_dec_ref(x_286);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 1, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_310);
return x_312;
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_247);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec(x_225);
lean_dec(x_11);
lean_dec_ref(x_2);
x_313 = lean_ctor_get(x_250, 0);
lean_inc(x_313);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_314 = x_250;
} else {
 lean_dec_ref(x_250);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 1, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_313);
return x_315;
}
}
else
{
lean_object* x_316; 
lean_dec_ref(x_245);
lean_dec_ref(x_242);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec(x_11);
lean_dec_ref(x_2);
x_316 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_247, x_238, x_241, x_244, x_240, x_243);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 x_318 = x_316;
} else {
 lean_dec_ref(x_316);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_319 = lean_alloc_ctor(1, 1, 0);
} else {
 x_319 = x_225;
}
lean_ctor_set(x_319, 0, x_317);
if (lean_is_scalar(x_318)) {
 x_320 = lean_alloc_ctor(0, 1, 0);
} else {
 x_320 = x_318;
}
lean_ctor_set(x_320, 0, x_319);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_225);
x_321 = lean_ctor_get(x_316, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 x_322 = x_316;
} else {
 lean_dec_ref(x_316);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 1, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_321);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_247);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_238);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec(x_225);
lean_dec(x_11);
lean_dec_ref(x_2);
x_324 = lean_ctor_get(x_248, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_325 = x_248;
} else {
 lean_dec_ref(x_248);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 1, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_324);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_238);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec(x_225);
lean_dec(x_11);
lean_dec_ref(x_2);
x_327 = lean_ctor_get(x_246, 0);
lean_inc(x_327);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_328 = x_246;
} else {
 lean_dec_ref(x_246);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 1, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_327);
return x_329;
}
}
block_363:
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_inc_ref(x_229);
x_342 = l_Array_toSubarray___redArg(x_229, x_340, x_341);
x_343 = l_Array_ofSubarray___redArg(x_342);
lean_dec_ref(x_342);
lean_inc(x_337);
lean_inc_ref(x_335);
lean_inc(x_338);
lean_inc_ref(x_336);
lean_inc_ref(x_343);
x_344 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_226, x_227, x_343, x_234, x_332, x_331, x_339, x_336, x_338, x_335, x_337);
lean_dec_ref(x_226);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; uint8_t x_346; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
lean_dec_ref(x_344);
x_346 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_11);
if (x_346 == 0)
{
x_235 = x_331;
x_236 = x_332;
x_237 = x_345;
x_238 = x_333;
x_239 = lean_box(0);
x_240 = x_335;
x_241 = x_336;
x_242 = x_343;
x_243 = x_337;
x_244 = x_338;
x_245 = x_339;
goto block_330;
}
else
{
uint8_t x_347; 
x_347 = lean_nat_dec_eq(x_231, x_232);
if (x_347 == 0)
{
x_235 = x_331;
x_236 = x_332;
x_237 = x_345;
x_238 = x_333;
x_239 = lean_box(0);
x_240 = x_335;
x_241 = x_336;
x_242 = x_343;
x_243 = x_337;
x_244 = x_338;
x_245 = x_339;
goto block_330;
}
else
{
lean_object* x_348; 
lean_dec_ref(x_343);
lean_dec_ref(x_333);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec(x_225);
lean_dec(x_11);
lean_dec_ref(x_2);
x_348 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_331);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; 
lean_dec_ref(x_348);
x_349 = l_Lean_Compiler_LCNF_Simp_simp(x_345, x_332, x_331, x_339, x_336, x_338, x_335, x_337);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 x_351 = x_349;
} else {
 lean_dec_ref(x_349);
 x_351 = lean_box(0);
}
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_350);
if (lean_is_scalar(x_351)) {
 x_353 = lean_alloc_ctor(0, 1, 0);
} else {
 x_353 = x_351;
}
lean_ctor_set(x_353, 0, x_352);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_349, 0);
lean_inc(x_354);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 x_355 = x_349;
} else {
 lean_dec_ref(x_349);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_354);
return x_356;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_345);
lean_dec_ref(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_332);
lean_dec(x_331);
x_357 = lean_ctor_get(x_348, 0);
lean_inc(x_357);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 x_358 = x_348;
} else {
 lean_dec_ref(x_348);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 1, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_357);
return x_359;
}
}
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec_ref(x_343);
lean_dec_ref(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_333);
lean_dec_ref(x_332);
lean_dec(x_331);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec(x_225);
lean_dec(x_11);
lean_dec_ref(x_2);
x_360 = lean_ctor_get(x_344, 0);
lean_inc(x_360);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 x_361 = x_344;
} else {
 lean_dec_ref(x_344);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 1, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_360);
return x_362;
}
}
block_398:
{
if (x_234 == 0)
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; 
lean_inc_ref(x_229);
lean_inc_ref(x_228);
lean_inc_ref(x_227);
lean_inc_ref(x_226);
lean_dec(x_224);
lean_inc_ref(x_366);
lean_inc_ref(x_364);
lean_inc(x_365);
x_372 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(x_372, 0, x_365);
lean_closure_set(x_372, 1, x_233);
lean_closure_set(x_372, 2, x_364);
lean_closure_set(x_372, 3, x_366);
x_373 = lean_unsigned_to_nat(0u);
x_374 = lean_nat_dec_le(x_232, x_231);
if (x_374 == 0)
{
lean_inc(x_231);
x_331 = x_365;
x_332 = x_364;
x_333 = x_372;
x_334 = lean_box(0);
x_335 = x_369;
x_336 = x_367;
x_337 = x_370;
x_338 = x_368;
x_339 = x_366;
x_340 = x_373;
x_341 = x_231;
goto block_363;
}
else
{
lean_inc(x_232);
x_331 = x_365;
x_332 = x_364;
x_333 = x_372;
x_334 = lean_box(0);
x_335 = x_369;
x_336 = x_367;
x_337 = x_370;
x_338 = x_368;
x_339 = x_366;
x_340 = x_373;
x_341 = x_232;
goto block_363;
}
}
else
{
lean_object* x_375; 
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_225);
lean_inc(x_370);
lean_inc_ref(x_369);
lean_inc(x_368);
lean_inc_ref(x_367);
x_375 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_224, x_364, x_365, x_366, x_367, x_368, x_369, x_370);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
lean_dec_ref(x_375);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_377, x_365, x_368, x_369, x_370);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
lean_dec_ref(x_378);
x_379 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_365);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; 
lean_dec_ref(x_379);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_376);
lean_ctor_set(x_380, 1, x_2);
x_381 = l_Lean_Compiler_LCNF_Simp_simp(x_380, x_364, x_365, x_366, x_367, x_368, x_369, x_370);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 x_383 = x_381;
} else {
 lean_dec_ref(x_381);
 x_383 = lean_box(0);
}
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_382);
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(0, 1, 0);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_384);
return x_385;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_381, 0);
lean_inc(x_386);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 x_387 = x_381;
} else {
 lean_dec_ref(x_381);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 1, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_386);
return x_388;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_376);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_dec_ref(x_367);
lean_dec_ref(x_366);
lean_dec(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_2);
x_389 = lean_ctor_get(x_379, 0);
lean_inc(x_389);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_390 = x_379;
} else {
 lean_dec_ref(x_379);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 1, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_389);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_376);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_dec_ref(x_367);
lean_dec_ref(x_366);
lean_dec(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_2);
x_392 = lean_ctor_get(x_378, 0);
lean_inc(x_392);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 x_393 = x_378;
} else {
 lean_dec_ref(x_378);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 1, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_392);
return x_394;
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_dec_ref(x_367);
lean_dec_ref(x_366);
lean_dec(x_365);
lean_dec_ref(x_364);
lean_dec(x_11);
lean_dec_ref(x_2);
x_395 = lean_ctor_get(x_375, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 x_396 = x_375;
} else {
 lean_dec_ref(x_375);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 1, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_395);
return x_397;
}
}
}
}
}
}
else
{
uint8_t x_413; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_413 = !lean_is_exclusive(x_13);
if (x_413 == 0)
{
return x_13;
}
else
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_ctor_get(x_13, 0);
lean_inc(x_414);
lean_dec(x_13);
x_415 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_415, 0, x_414);
return x_415;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_st_ref_get(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = lean_st_ref_get(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
lean_inc_ref(x_6);
x_12 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_9, x_1, x_6);
lean_dec_ref(x_9);
lean_inc(x_7);
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_11, x_7, x_1);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(x_2, x_12, x_13, x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_1, x_2, x_4, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_6, x_2, x_1);
lean_dec_ref(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1, x_2, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1, x_2, x_3, x_4, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(x_8, x_4);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
lean_free_object(x_9);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
size_t x_18; size_t x_19; 
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_16);
return x_21;
}
}
}
else
{
return x_9;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_2, x_3, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget_borrowed(x_4, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_46; uint8_t x_47; uint8_t x_64; lean_object* x_65; uint8_t x_67; lean_object* x_68; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
x_32 = lean_ctor_get(x_16, 2);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_array_get_size(x_31);
x_72 = lean_nat_dec_lt(x_70, x_71);
if (x_72 == 0)
{
lean_dec(x_71);
x_67 = x_2;
x_68 = lean_box(0);
goto block_69;
}
else
{
if (x_72 == 0)
{
lean_dec(x_71);
x_67 = x_2;
x_68 = lean_box(0);
goto block_69;
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_75 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_31, x_73, x_74, x_11);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
x_67 = x_77;
x_68 = lean_box(0);
goto block_69;
}
else
{
uint8_t x_78; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
block_45:
{
lean_object* x_34; 
lean_inc_ref(x_10);
lean_inc_ref(x_7);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc(x_1);
x_34 = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_30, x_31, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_32);
x_36 = l_Lean_Compiler_LCNF_Simp_simp(x_32, x_5, x_6, x_35, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc_ref(x_16);
x_38 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_37);
x_17 = x_38;
x_18 = lean_box(0);
goto block_29;
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
block_63:
{
if (x_47 == 0)
{
x_33 = lean_box(0);
goto block_45;
}
else
{
lean_object* x_48; 
lean_inc_ref(x_32);
x_48 = l_Lean_Compiler_LCNF_Code_inferType(x_32, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_32, x_9);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec_ref(x_50);
x_51 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_6);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_51);
x_52 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_52, 0, x_49);
lean_inc_ref(x_16);
x_53 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_52);
x_17 = x_53;
x_18 = lean_box(0);
goto block_29;
}
else
{
uint8_t x_54; 
lean_dec(x_49);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_49);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
return x_48;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_48, 0);
lean_inc(x_61);
lean_dec(x_48);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
block_66:
{
if (x_2 == 0)
{
x_33 = lean_box(0);
goto block_45;
}
else
{
x_46 = lean_box(0);
x_47 = x_64;
goto block_63;
}
}
block_69:
{
if (lean_obj_tag(x_32) == 6)
{
x_64 = x_67;
x_65 = lean_box(0);
goto block_66;
}
else
{
if (x_2 == 0)
{
x_46 = lean_box(0);
x_47 = x_67;
goto block_63;
}
else
{
x_64 = x_67;
x_65 = lean_box(0);
goto block_66;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_16, 0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_81);
x_82 = l_Lean_Compiler_LCNF_Simp_simp(x_81, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc_ref(x_16);
x_84 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_83);
x_17 = x_84;
x_18 = lean_box(0);
goto block_29;
}
else
{
uint8_t x_85; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
block_29:
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_16);
x_20 = lean_ptr_addr(x_17);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
x_24 = lean_array_fset(x_4, x_3, x_17);
lean_dec(x_3);
x_3 = x_23;
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
lean_dec(x_3);
x_3 = x_27;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget_borrowed(x_4, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_46; uint8_t x_47; uint8_t x_64; lean_object* x_65; uint8_t x_67; lean_object* x_68; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
x_32 = lean_ctor_get(x_16, 2);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_array_get_size(x_31);
x_72 = lean_nat_dec_lt(x_70, x_71);
if (x_72 == 0)
{
lean_dec(x_71);
x_67 = x_2;
x_68 = lean_box(0);
goto block_69;
}
else
{
if (x_72 == 0)
{
lean_dec(x_71);
x_67 = x_2;
x_68 = lean_box(0);
goto block_69;
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_75 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_31, x_73, x_74, x_11);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
x_67 = x_77;
x_68 = lean_box(0);
goto block_69;
}
else
{
uint8_t x_78; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
block_45:
{
lean_object* x_34; 
lean_inc_ref(x_10);
lean_inc_ref(x_7);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc(x_1);
x_34 = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_30, x_31, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_32);
x_36 = l_Lean_Compiler_LCNF_Simp_simp(x_32, x_5, x_6, x_35, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc_ref(x_16);
x_38 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_37);
x_17 = x_38;
x_18 = lean_box(0);
goto block_29;
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
block_63:
{
if (x_47 == 0)
{
x_33 = lean_box(0);
goto block_45;
}
else
{
lean_object* x_48; 
lean_inc_ref(x_32);
x_48 = l_Lean_Compiler_LCNF_Code_inferType(x_32, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_32, x_9);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec_ref(x_50);
x_51 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_6);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_51);
x_52 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_52, 0, x_49);
lean_inc_ref(x_16);
x_53 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_52);
x_17 = x_53;
x_18 = lean_box(0);
goto block_29;
}
else
{
uint8_t x_54; 
lean_dec(x_49);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_49);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
return x_48;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_48, 0);
lean_inc(x_61);
lean_dec(x_48);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
block_66:
{
if (x_2 == 0)
{
x_33 = lean_box(0);
goto block_45;
}
else
{
x_46 = lean_box(0);
x_47 = x_64;
goto block_63;
}
}
block_69:
{
if (lean_obj_tag(x_32) == 6)
{
x_64 = x_67;
x_65 = lean_box(0);
goto block_66;
}
else
{
if (x_2 == 0)
{
x_46 = lean_box(0);
x_47 = x_67;
goto block_63;
}
else
{
x_64 = x_67;
x_65 = lean_box(0);
goto block_66;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_16, 0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_81);
x_82 = l_Lean_Compiler_LCNF_Simp_simp(x_81, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc_ref(x_16);
x_84 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_83);
x_17 = x_84;
x_18 = lean_box(0);
goto block_29;
}
else
{
uint8_t x_85; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
block_29:
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_16);
x_20 = lean_ptr_addr(x_17);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
x_24 = lean_array_fset(x_4, x_3, x_17);
x_25 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(x_1, x_2, x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(x_1, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_8, x_5);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1, x_2, x_3, x_4, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_8, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
lean_free_object(x_9);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
size_t x_18; size_t x_19; 
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_16);
return x_21;
}
}
}
else
{
return x_9;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_2, x_3, x_5);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Simp_simp___closed__2;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(316u);
x_4 = l_Lean_Compiler_LCNF_Simp_simp___closed__1;
x_5 = l_Lean_Compiler_LCNF_Simp_simp___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; uint8_t x_122; 
x_106 = lean_ctor_get(x_7, 0);
x_107 = lean_ctor_get(x_7, 1);
x_108 = lean_ctor_get(x_7, 2);
x_109 = lean_ctor_get(x_7, 3);
x_110 = lean_ctor_get(x_7, 4);
x_111 = lean_ctor_get(x_7, 5);
x_112 = lean_ctor_get(x_7, 6);
x_113 = lean_ctor_get(x_7, 7);
x_114 = lean_ctor_get(x_7, 8);
x_115 = lean_ctor_get(x_7, 9);
x_116 = lean_ctor_get(x_7, 10);
x_117 = lean_ctor_get(x_7, 11);
x_118 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_119 = lean_ctor_get(x_7, 12);
x_120 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_121 = lean_ctor_get(x_7, 13);
x_122 = lean_nat_dec_eq(x_109, x_110);
if (x_122 == 0)
{
uint8_t x_123; 
lean_inc_ref(x_121);
lean_inc(x_119);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc_ref(x_107);
lean_inc_ref(x_106);
x_123 = !lean_is_exclusive(x_7);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_124 = lean_ctor_get(x_7, 13);
lean_dec(x_124);
x_125 = lean_ctor_get(x_7, 12);
lean_dec(x_125);
x_126 = lean_ctor_get(x_7, 11);
lean_dec(x_126);
x_127 = lean_ctor_get(x_7, 10);
lean_dec(x_127);
x_128 = lean_ctor_get(x_7, 9);
lean_dec(x_128);
x_129 = lean_ctor_get(x_7, 8);
lean_dec(x_129);
x_130 = lean_ctor_get(x_7, 7);
lean_dec(x_130);
x_131 = lean_ctor_get(x_7, 6);
lean_dec(x_131);
x_132 = lean_ctor_get(x_7, 5);
lean_dec(x_132);
x_133 = lean_ctor_get(x_7, 4);
lean_dec(x_133);
x_134 = lean_ctor_get(x_7, 3);
lean_dec(x_134);
x_135 = lean_ctor_get(x_7, 2);
lean_dec(x_135);
x_136 = lean_ctor_get(x_7, 1);
lean_dec(x_136);
x_137 = lean_ctor_get(x_7, 0);
lean_dec(x_137);
x_138 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_189; lean_object* x_190; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
x_189 = lean_unsigned_to_nat(1u);
x_190 = lean_nat_add(x_109, x_189);
lean_dec(x_109);
lean_ctor_set(x_7, 3, x_190);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_346; 
lean_free_object(x_138);
x_191 = lean_ctor_get(x_1, 0);
x_192 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_191);
x_346 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_122, x_191, x_3, x_6);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_381; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
lean_dec_ref(x_346);
x_381 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_191, x_347);
if (x_381 == 0)
{
goto block_380;
}
else
{
if (x_122 == 0)
{
x_348 = x_2;
x_349 = x_3;
x_350 = x_4;
x_351 = x_5;
x_352 = x_6;
x_353 = x_7;
x_354 = x_8;
x_355 = lean_box(0);
goto block_375;
}
else
{
goto block_380;
}
}
block_375:
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_347, 2);
x_357 = lean_ctor_get(x_347, 3);
lean_inc(x_354);
lean_inc_ref(x_353);
lean_inc(x_352);
lean_inc_ref(x_351);
lean_inc_ref(x_350);
lean_inc(x_357);
x_358 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_357, x_348, x_350, x_351, x_352, x_353, x_354);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
lean_dec_ref(x_358);
if (lean_obj_tag(x_359) == 0)
{
lean_inc(x_357);
lean_inc_ref(x_356);
x_331 = x_347;
x_332 = x_356;
x_333 = x_357;
x_334 = x_348;
x_335 = x_349;
x_336 = x_350;
x_337 = x_351;
x_338 = x_352;
x_339 = x_353;
x_340 = x_354;
x_341 = lean_box(0);
goto block_345;
}
else
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
lean_dec_ref(x_359);
x_361 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_349);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
lean_dec_ref(x_361);
x_362 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_347, x_360, x_352);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec_ref(x_362);
x_364 = lean_ctor_get(x_363, 2);
lean_inc_ref(x_364);
x_365 = lean_ctor_get(x_363, 3);
lean_inc(x_365);
x_331 = x_363;
x_332 = x_364;
x_333 = x_365;
x_334 = x_348;
x_335 = x_349;
x_336 = x_350;
x_337 = x_351;
x_338 = x_352;
x_339 = x_353;
x_340 = x_354;
x_341 = lean_box(0);
goto block_345;
}
else
{
uint8_t x_366; 
lean_dec(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_351);
lean_dec_ref(x_350);
lean_dec(x_349);
lean_dec_ref(x_348);
lean_dec_ref(x_1);
x_366 = !lean_is_exclusive(x_362);
if (x_366 == 0)
{
return x_362;
}
else
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_362, 0);
lean_inc(x_367);
lean_dec(x_362);
x_368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_368, 0, x_367);
return x_368;
}
}
}
else
{
uint8_t x_369; 
lean_dec(x_360);
lean_dec(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_351);
lean_dec_ref(x_350);
lean_dec(x_349);
lean_dec_ref(x_348);
lean_dec(x_347);
lean_dec_ref(x_1);
x_369 = !lean_is_exclusive(x_361);
if (x_369 == 0)
{
return x_361;
}
else
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_361, 0);
lean_inc(x_370);
lean_dec(x_361);
x_371 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_371, 0, x_370);
return x_371;
}
}
}
}
else
{
uint8_t x_372; 
lean_dec(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_351);
lean_dec_ref(x_350);
lean_dec(x_349);
lean_dec_ref(x_348);
lean_dec(x_347);
lean_dec_ref(x_1);
x_372 = !lean_is_exclusive(x_358);
if (x_372 == 0)
{
return x_358;
}
else
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_358, 0);
lean_inc(x_373);
lean_dec(x_358);
x_374 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_374, 0, x_373);
return x_374;
}
}
}
block_380:
{
lean_object* x_376; 
x_376 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_376) == 0)
{
lean_dec_ref(x_376);
x_348 = x_2;
x_349 = x_3;
x_350 = x_4;
x_351 = x_5;
x_352 = x_6;
x_353 = x_7;
x_354 = x_8;
x_355 = lean_box(0);
goto block_375;
}
else
{
uint8_t x_377; 
lean_dec(x_347);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_377 = !lean_is_exclusive(x_376);
if (x_377 == 0)
{
return x_376;
}
else
{
lean_object* x_378; lean_object* x_379; 
x_378 = lean_ctor_get(x_376, 0);
lean_inc(x_378);
lean_dec(x_376);
x_379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_379, 0, x_378);
return x_379;
}
}
}
}
else
{
uint8_t x_382; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_382 = !lean_is_exclusive(x_346);
if (x_382 == 0)
{
return x_346;
}
else
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_346, 0);
lean_inc(x_383);
lean_dec(x_346);
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_383);
return x_384;
}
}
block_330:
{
if (x_202 == 0)
{
lean_object* x_203; 
lean_inc(x_193);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_197);
lean_inc_ref(x_194);
x_203 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_194, x_197, x_195, x_201, x_193);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
lean_inc(x_193);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_197);
lean_inc_ref(x_194);
x_205 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_194, x_200, x_199, x_197, x_195, x_201, x_193);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec_ref(x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_194, 0);
x_208 = lean_ctor_get(x_194, 3);
x_209 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_208);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
lean_inc(x_193);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_197);
lean_inc_ref(x_198);
lean_inc(x_199);
lean_inc_ref(x_200);
lean_inc_ref(x_192);
lean_inc_ref(x_194);
x_211 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_194, x_192, x_200, x_199, x_198, x_197, x_195, x_201, x_193);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
lean_inc(x_193);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_197);
lean_inc_ref(x_198);
lean_inc(x_199);
lean_inc_ref(x_200);
lean_inc(x_208);
x_213 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_208, x_200, x_199, x_198, x_197, x_195, x_201, x_193);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
lean_inc(x_193);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_197);
lean_inc_ref(x_198);
lean_inc(x_199);
lean_inc_ref(x_200);
lean_inc_ref(x_192);
x_215 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_200, x_199, x_198, x_197, x_195, x_201, x_193);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec_ref(x_215);
x_217 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_207, x_199);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
lean_dec_ref(x_217);
x_219 = lean_unbox(x_218);
lean_dec(x_218);
if (x_219 == 0)
{
lean_object* x_220; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_193);
lean_dec_ref(x_1);
x_220 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_194, x_199, x_195);
lean_dec(x_195);
lean_dec(x_199);
lean_dec_ref(x_194);
if (lean_obj_tag(x_220) == 0)
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_220, 0);
lean_dec(x_222);
lean_ctor_set(x_220, 0, x_216);
return x_220;
}
else
{
lean_object* x_223; 
lean_dec(x_220);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_216);
return x_223;
}
}
else
{
uint8_t x_224; 
lean_dec(x_216);
x_224 = !lean_is_exclusive(x_220);
if (x_224 == 0)
{
return x_220;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_220, 0);
lean_inc(x_225);
lean_dec(x_220);
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_225);
return x_226;
}
}
}
else
{
lean_object* x_227; 
lean_inc_ref(x_194);
x_227 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_194, x_200, x_199, x_198, x_197, x_195, x_201, x_193);
lean_dec(x_193);
lean_dec_ref(x_201);
lean_dec(x_195);
lean_dec_ref(x_197);
lean_dec_ref(x_198);
lean_dec(x_199);
lean_dec_ref(x_200);
if (lean_obj_tag(x_227) == 0)
{
size_t x_228; size_t x_229; uint8_t x_230; 
lean_dec_ref(x_227);
x_228 = lean_ptr_addr(x_192);
x_229 = lean_ptr_addr(x_216);
x_230 = lean_usize_dec_eq(x_228, x_229);
if (x_230 == 0)
{
x_10 = x_194;
x_11 = lean_box(0);
x_12 = x_216;
x_13 = x_230;
goto block_17;
}
else
{
size_t x_231; size_t x_232; uint8_t x_233; 
x_231 = lean_ptr_addr(x_191);
x_232 = lean_ptr_addr(x_194);
x_233 = lean_usize_dec_eq(x_231, x_232);
x_10 = x_194;
x_11 = lean_box(0);
x_12 = x_216;
x_13 = x_233;
goto block_17;
}
}
else
{
uint8_t x_234; 
lean_dec(x_216);
lean_dec_ref(x_194);
lean_dec_ref(x_1);
x_234 = !lean_is_exclusive(x_227);
if (x_234 == 0)
{
return x_227;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_227, 0);
lean_inc(x_235);
lean_dec(x_227);
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_235);
return x_236;
}
}
}
}
else
{
uint8_t x_237; 
lean_dec(x_216);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_1);
x_237 = !lean_is_exclusive(x_217);
if (x_237 == 0)
{
return x_217;
}
else
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_217, 0);
lean_inc(x_238);
lean_dec(x_217);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_238);
return x_239;
}
}
}
else
{
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_1);
return x_215;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_inc_ref(x_192);
lean_dec_ref(x_1);
x_240 = lean_ctor_get(x_214, 0);
lean_inc(x_240);
lean_dec_ref(x_214);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
lean_inc(x_207);
x_243 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_207, x_242, x_199, x_195, x_201, x_193);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; 
lean_dec_ref(x_243);
x_244 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_194, x_199, x_195);
lean_dec_ref(x_194);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
lean_dec_ref(x_244);
lean_inc(x_193);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_197);
lean_inc_ref(x_198);
lean_inc(x_199);
lean_inc_ref(x_200);
x_245 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_200, x_199, x_198, x_197, x_195, x_201, x_193);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_247 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_241, x_246, x_200, x_199, x_198, x_197, x_195, x_201, x_193);
lean_dec(x_193);
lean_dec_ref(x_201);
lean_dec(x_195);
lean_dec_ref(x_197);
lean_dec_ref(x_198);
lean_dec(x_199);
lean_dec_ref(x_200);
lean_dec(x_241);
return x_247;
}
else
{
lean_dec(x_241);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec(x_193);
return x_245;
}
}
else
{
uint8_t x_248; 
lean_dec(x_241);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec(x_193);
lean_dec_ref(x_192);
x_248 = !lean_is_exclusive(x_244);
if (x_248 == 0)
{
return x_244;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_244, 0);
lean_inc(x_249);
lean_dec(x_244);
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_249);
return x_250;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_241);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_192);
x_251 = !lean_is_exclusive(x_243);
if (x_251 == 0)
{
return x_243;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_243, 0);
lean_inc(x_252);
lean_dec(x_243);
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_252);
return x_253;
}
}
}
}
else
{
uint8_t x_254; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_1);
x_254 = !lean_is_exclusive(x_213);
if (x_254 == 0)
{
return x_213;
}
else
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_213, 0);
lean_inc(x_255);
lean_dec(x_213);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
return x_256;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_193);
lean_dec_ref(x_1);
x_257 = lean_ctor_get(x_212, 0);
lean_inc(x_257);
lean_dec_ref(x_212);
x_258 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_194, x_199, x_195);
lean_dec(x_195);
lean_dec(x_199);
lean_dec_ref(x_194);
if (lean_obj_tag(x_258) == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_258, 0);
lean_dec(x_260);
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
else
{
lean_object* x_261; 
lean_dec(x_258);
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_257);
return x_261;
}
}
else
{
uint8_t x_262; 
lean_dec(x_257);
x_262 = !lean_is_exclusive(x_258);
if (x_262 == 0)
{
return x_258;
}
else
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_258, 0);
lean_inc(x_263);
lean_dec(x_258);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_263);
return x_264;
}
}
}
}
else
{
uint8_t x_265; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_1);
x_265 = !lean_is_exclusive(x_211);
if (x_265 == 0)
{
return x_211;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_211, 0);
lean_inc(x_266);
lean_dec(x_211);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_266);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_inc_ref(x_192);
lean_dec_ref(x_1);
x_268 = lean_ctor_get(x_210, 0);
lean_inc(x_268);
lean_dec_ref(x_210);
lean_inc(x_207);
x_269 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_207, x_268, x_199, x_195, x_201, x_193);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
lean_dec_ref(x_269);
x_270 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_194, x_199, x_195);
lean_dec_ref(x_194);
if (lean_obj_tag(x_270) == 0)
{
lean_dec_ref(x_270);
x_1 = x_192;
x_2 = x_200;
x_3 = x_199;
x_4 = x_198;
x_5 = x_197;
x_6 = x_195;
x_7 = x_201;
x_8 = x_193;
goto _start;
}
else
{
uint8_t x_272; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec(x_193);
lean_dec_ref(x_192);
x_272 = !lean_is_exclusive(x_270);
if (x_272 == 0)
{
return x_270;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_270, 0);
lean_inc(x_273);
lean_dec(x_270);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
}
}
else
{
uint8_t x_275; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_192);
x_275 = !lean_is_exclusive(x_269);
if (x_275 == 0)
{
return x_269;
}
else
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_269, 0);
lean_inc(x_276);
lean_dec(x_269);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_276);
return x_277;
}
}
}
}
else
{
uint8_t x_278; 
lean_dec_ref(x_194);
lean_inc_ref(x_192);
x_278 = !lean_is_exclusive(x_1);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_1, 1);
lean_dec(x_279);
x_280 = lean_ctor_get(x_1, 0);
lean_dec(x_280);
x_281 = lean_ctor_get(x_206, 0);
lean_inc(x_281);
lean_dec_ref(x_206);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_281);
x_2 = x_200;
x_3 = x_199;
x_4 = x_198;
x_5 = x_197;
x_6 = x_195;
x_7 = x_201;
x_8 = x_193;
goto _start;
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_1);
x_283 = lean_ctor_get(x_206, 0);
lean_inc(x_283);
lean_dec_ref(x_206);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_192);
x_1 = x_284;
x_2 = x_200;
x_3 = x_199;
x_4 = x_198;
x_5 = x_197;
x_6 = x_195;
x_7 = x_201;
x_8 = x_193;
goto _start;
}
}
}
else
{
uint8_t x_286; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_1);
x_286 = !lean_is_exclusive(x_205);
if (x_286 == 0)
{
return x_205;
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_205, 0);
lean_inc(x_287);
lean_dec(x_205);
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_287);
return x_288;
}
}
}
else
{
lean_object* x_289; lean_object* x_290; 
lean_dec_ref(x_194);
lean_inc_ref(x_192);
lean_dec_ref(x_1);
x_289 = lean_ctor_get(x_204, 0);
lean_inc(x_289);
lean_dec_ref(x_204);
x_290 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_199);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; 
lean_dec_ref(x_290);
lean_inc(x_193);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_197);
lean_inc_ref(x_198);
lean_inc(x_199);
lean_inc_ref(x_200);
x_291 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_200, x_199, x_198, x_197, x_195, x_201, x_193);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
x_293 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_289, x_292, x_200, x_199, x_198, x_197, x_195, x_201, x_193);
lean_dec(x_193);
lean_dec_ref(x_201);
lean_dec(x_195);
lean_dec_ref(x_197);
lean_dec_ref(x_198);
lean_dec(x_199);
lean_dec_ref(x_200);
lean_dec(x_289);
return x_293;
}
else
{
lean_dec(x_289);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec(x_193);
return x_291;
}
}
else
{
uint8_t x_294; 
lean_dec(x_289);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec(x_193);
lean_dec_ref(x_192);
x_294 = !lean_is_exclusive(x_290);
if (x_294 == 0)
{
return x_290;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_290, 0);
lean_inc(x_295);
lean_dec(x_290);
x_296 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_296, 0, x_295);
return x_296;
}
}
}
}
else
{
uint8_t x_297; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_1);
x_297 = !lean_is_exclusive(x_203);
if (x_297 == 0)
{
return x_203;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_203, 0);
lean_inc(x_298);
lean_dec(x_203);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_298);
return x_299;
}
}
}
else
{
lean_object* x_300; uint8_t x_301; 
lean_inc_ref(x_192);
lean_dec_ref(x_1);
x_300 = lean_st_ref_take(x_199);
x_301 = !lean_is_exclusive(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_302 = lean_ctor_get(x_194, 0);
x_303 = lean_ctor_get(x_300, 0);
x_304 = lean_box(0);
lean_inc(x_302);
x_305 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_303, x_302, x_304);
lean_ctor_set(x_300, 0, x_305);
x_306 = lean_st_ref_set(x_199, x_300);
x_307 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_194, x_199, x_195);
lean_dec_ref(x_194);
if (lean_obj_tag(x_307) == 0)
{
lean_dec_ref(x_307);
x_1 = x_192;
x_2 = x_200;
x_3 = x_199;
x_4 = x_198;
x_5 = x_197;
x_6 = x_195;
x_7 = x_201;
x_8 = x_193;
goto _start;
}
else
{
uint8_t x_309; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec(x_193);
lean_dec_ref(x_192);
x_309 = !lean_is_exclusive(x_307);
if (x_309 == 0)
{
return x_307;
}
else
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_307, 0);
lean_inc(x_310);
lean_dec(x_307);
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_310);
return x_311;
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_312 = lean_ctor_get(x_194, 0);
x_313 = lean_ctor_get(x_300, 0);
x_314 = lean_ctor_get(x_300, 1);
x_315 = lean_ctor_get(x_300, 2);
x_316 = lean_ctor_get(x_300, 3);
x_317 = lean_ctor_get_uint8(x_300, sizeof(void*)*7);
x_318 = lean_ctor_get(x_300, 4);
x_319 = lean_ctor_get(x_300, 5);
x_320 = lean_ctor_get(x_300, 6);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_316);
lean_inc(x_315);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_300);
x_321 = lean_box(0);
lean_inc(x_312);
x_322 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_313, x_312, x_321);
x_323 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_314);
lean_ctor_set(x_323, 2, x_315);
lean_ctor_set(x_323, 3, x_316);
lean_ctor_set(x_323, 4, x_318);
lean_ctor_set(x_323, 5, x_319);
lean_ctor_set(x_323, 6, x_320);
lean_ctor_set_uint8(x_323, sizeof(void*)*7, x_317);
x_324 = lean_st_ref_set(x_199, x_323);
x_325 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_194, x_199, x_195);
lean_dec_ref(x_194);
if (lean_obj_tag(x_325) == 0)
{
lean_dec_ref(x_325);
x_1 = x_192;
x_2 = x_200;
x_3 = x_199;
x_4 = x_198;
x_5 = x_197;
x_6 = x_195;
x_7 = x_201;
x_8 = x_193;
goto _start;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec(x_193);
lean_dec_ref(x_192);
x_327 = lean_ctor_get(x_325, 0);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 1, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_327);
return x_329;
}
}
}
}
block_345:
{
uint8_t x_342; 
x_342 = l_Lean_Expr_isErased(x_332);
lean_dec_ref(x_332);
if (x_342 == 0)
{
lean_dec(x_333);
x_193 = x_340;
x_194 = x_331;
x_195 = x_338;
x_196 = lean_box(0);
x_197 = x_337;
x_198 = x_336;
x_199 = x_335;
x_200 = x_334;
x_201 = x_339;
x_202 = x_122;
goto block_330;
}
else
{
lean_object* x_343; uint8_t x_344; 
x_343 = lean_box(1);
x_344 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_333, x_343);
lean_dec(x_333);
if (x_344 == 0)
{
x_193 = x_340;
x_194 = x_331;
x_195 = x_338;
x_196 = lean_box(0);
x_197 = x_337;
x_198 = x_336;
x_199 = x_335;
x_200 = x_334;
x_201 = x_339;
x_202 = x_342;
goto block_330;
}
else
{
x_193 = x_340;
x_194 = x_331;
x_195 = x_338;
x_196 = lean_box(0);
x_197 = x_337;
x_198 = x_336;
x_199 = x_335;
x_200 = x_334;
x_201 = x_339;
x_202 = x_122;
goto block_330;
}
}
}
}
case 3:
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_free_object(x_138);
x_385 = lean_ctor_get(x_1, 0);
x_386 = lean_ctor_get(x_1, 1);
x_387 = lean_st_ref_get(x_3);
x_388 = lean_ctor_get(x_387, 0);
lean_inc_ref(x_388);
lean_dec_ref(x_387);
lean_inc(x_385);
x_389 = l_Lean_Compiler_LCNF_normFVarImp(x_388, x_385, x_122);
lean_dec_ref(x_388);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; lean_object* x_404; lean_object* x_410; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec_ref(x_389);
lean_inc_ref(x_386);
x_391 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_122, x_386, x_3);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 x_393 = x_391;
} else {
 lean_dec_ref(x_391);
 x_393 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_392);
x_410 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_390, x_392, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
lean_dec_ref(x_410);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_390);
x_412 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_390, x_3);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; 
lean_dec_ref(x_412);
x_413 = lean_unsigned_to_nat(0u);
x_414 = lean_array_get_size(x_392);
x_415 = lean_nat_dec_lt(x_413, x_414);
if (x_415 == 0)
{
lean_dec(x_414);
lean_dec(x_3);
x_404 = lean_box(0);
goto block_409;
}
else
{
uint8_t x_416; 
x_416 = lean_nat_dec_le(x_414, x_414);
if (x_416 == 0)
{
lean_dec(x_414);
lean_dec(x_3);
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_417; size_t x_418; size_t x_419; lean_object* x_420; 
x_417 = lean_box(0);
x_418 = 0;
x_419 = lean_usize_of_nat(x_414);
lean_dec(x_414);
x_420 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_392, x_418, x_419, x_417, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_420) == 0)
{
lean_dec_ref(x_420);
x_404 = lean_box(0);
goto block_409;
}
else
{
uint8_t x_421; 
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_390);
lean_dec_ref(x_1);
x_421 = !lean_is_exclusive(x_420);
if (x_421 == 0)
{
return x_420;
}
else
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_420, 0);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_423, 0, x_422);
return x_423;
}
}
}
}
}
else
{
uint8_t x_424; 
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_390);
lean_dec(x_3);
lean_dec_ref(x_1);
x_424 = !lean_is_exclusive(x_412);
if (x_424 == 0)
{
return x_412;
}
else
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_412, 0);
lean_inc(x_425);
lean_dec(x_412);
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_425);
return x_426;
}
}
}
else
{
lean_object* x_427; 
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_390);
lean_dec_ref(x_1);
x_427 = lean_ctor_get(x_411, 0);
lean_inc(x_427);
lean_dec_ref(x_411);
x_1 = x_427;
goto _start;
}
}
else
{
uint8_t x_429; 
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_390);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_429 = !lean_is_exclusive(x_410);
if (x_429 == 0)
{
return x_410;
}
else
{
lean_object* x_430; lean_object* x_431; 
x_430 = lean_ctor_get(x_410, 0);
lean_inc(x_430);
lean_dec(x_410);
x_431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_431, 0, x_430);
return x_431;
}
}
block_403:
{
if (x_395 == 0)
{
uint8_t x_396; 
x_396 = !lean_is_exclusive(x_1);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_1, 1);
lean_dec(x_397);
x_398 = lean_ctor_get(x_1, 0);
lean_dec(x_398);
lean_ctor_set(x_1, 1, x_392);
lean_ctor_set(x_1, 0, x_390);
if (lean_is_scalar(x_393)) {
 x_399 = lean_alloc_ctor(0, 1, 0);
} else {
 x_399 = x_393;
}
lean_ctor_set(x_399, 0, x_1);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; 
lean_dec(x_1);
x_400 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_400, 0, x_390);
lean_ctor_set(x_400, 1, x_392);
if (lean_is_scalar(x_393)) {
 x_401 = lean_alloc_ctor(0, 1, 0);
} else {
 x_401 = x_393;
}
lean_ctor_set(x_401, 0, x_400);
return x_401;
}
}
else
{
lean_object* x_402; 
lean_dec(x_392);
lean_dec(x_390);
if (lean_is_scalar(x_393)) {
 x_402 = lean_alloc_ctor(0, 1, 0);
} else {
 x_402 = x_393;
}
lean_ctor_set(x_402, 0, x_1);
return x_402;
}
}
block_409:
{
uint8_t x_405; 
x_405 = l_Lean_instBEqFVarId_beq(x_385, x_390);
if (x_405 == 0)
{
x_394 = lean_box(0);
x_395 = x_405;
goto block_403;
}
else
{
size_t x_406; size_t x_407; uint8_t x_408; 
x_406 = lean_ptr_addr(x_386);
x_407 = lean_ptr_addr(x_392);
x_408 = lean_usize_dec_eq(x_406, x_407);
x_394 = lean_box(0);
x_395 = x_408;
goto block_403;
}
}
}
else
{
lean_object* x_432; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_432 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_432;
}
}
case 4:
{
lean_object* x_433; lean_object* x_434; 
lean_free_object(x_138);
x_433 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_433);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_433);
x_434 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_433, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_434) == 0)
{
uint8_t x_435; 
x_435 = !lean_is_exclusive(x_434);
if (x_435 == 0)
{
lean_object* x_436; 
x_436 = lean_ctor_get(x_434, 0);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_437 = lean_st_ref_get(x_3);
x_438 = lean_ctor_get(x_433, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_433, 1);
lean_inc_ref(x_439);
x_440 = lean_ctor_get(x_433, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_433, 3);
lean_inc_ref(x_441);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_442 = x_433;
} else {
 lean_dec_ref(x_433);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_437, 0);
lean_inc_ref(x_443);
lean_dec_ref(x_437);
lean_inc(x_440);
x_444 = l_Lean_Compiler_LCNF_normFVarImp(x_443, x_440, x_122);
lean_dec_ref(x_443);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 x_446 = x_444;
} else {
 lean_dec_ref(x_444);
 x_446 = lean_box(0);
}
x_447 = lean_st_ref_get(x_3);
x_448 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_441);
lean_inc(x_445);
x_449 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_445, x_122, x_448, x_441, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 x_451 = x_449;
} else {
 lean_dec_ref(x_449);
 x_451 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_452 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_450, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_462; uint8_t x_463; lean_object* x_467; lean_object* x_468; lean_object* x_480; uint8_t x_481; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 x_454 = x_452;
} else {
 lean_dec_ref(x_452);
 x_454 = lean_box(0);
}
x_455 = lean_ctor_get(x_447, 0);
lean_inc_ref(x_455);
lean_dec_ref(x_447);
lean_inc_ref(x_439);
x_456 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_455, x_122, x_439);
lean_dec_ref(x_455);
x_480 = lean_array_get_size(x_453);
x_481 = lean_nat_dec_eq(x_480, x_189);
lean_dec(x_480);
if (x_481 == 0)
{
lean_free_object(x_434);
lean_dec(x_6);
x_467 = x_3;
x_468 = lean_box(0);
goto block_479;
}
else
{
lean_object* x_482; 
x_482 = lean_array_fget_borrowed(x_453, x_448);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_494; lean_object* x_495; uint8_t x_506; lean_object* x_507; uint8_t x_509; 
lean_free_object(x_434);
x_483 = lean_ctor_get(x_482, 1);
x_484 = lean_ctor_get(x_482, 2);
x_494 = lean_array_get_size(x_483);
x_509 = lean_nat_dec_lt(x_448, x_494);
if (x_509 == 0)
{
x_506 = x_122;
x_507 = lean_box(0);
goto block_508;
}
else
{
if (x_509 == 0)
{
x_506 = x_122;
x_507 = lean_box(0);
goto block_508;
}
else
{
size_t x_510; size_t x_511; lean_object* x_512; 
x_510 = 0;
x_511 = lean_usize_of_nat(x_494);
x_512 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_483, x_510, x_511, x_3);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; uint8_t x_514; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
lean_dec_ref(x_512);
x_514 = lean_unbox(x_513);
lean_dec(x_513);
x_506 = x_514;
x_507 = lean_box(0);
goto block_508;
}
else
{
uint8_t x_515; 
lean_dec(x_494);
lean_dec_ref(x_456);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec_ref(x_439);
lean_dec(x_438);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_515 = !lean_is_exclusive(x_512);
if (x_515 == 0)
{
return x_512;
}
else
{
lean_object* x_516; lean_object* x_517; 
x_516 = lean_ctor_get(x_512, 0);
lean_inc(x_516);
lean_dec(x_512);
x_517 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_517, 0, x_516);
return x_517;
}
}
}
}
block_493:
{
lean_object* x_486; 
x_486 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_486) == 0)
{
uint8_t x_487; 
x_487 = !lean_is_exclusive(x_486);
if (x_487 == 0)
{
lean_object* x_488; 
x_488 = lean_ctor_get(x_486, 0);
lean_dec(x_488);
lean_ctor_set(x_486, 0, x_484);
return x_486;
}
else
{
lean_object* x_489; 
lean_dec(x_486);
x_489 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_489, 0, x_484);
return x_489;
}
}
else
{
uint8_t x_490; 
lean_dec_ref(x_484);
x_490 = !lean_is_exclusive(x_486);
if (x_490 == 0)
{
return x_486;
}
else
{
lean_object* x_491; lean_object* x_492; 
x_491 = lean_ctor_get(x_486, 0);
lean_inc(x_491);
lean_dec(x_486);
x_492 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_492, 0, x_491);
return x_492;
}
}
}
block_505:
{
uint8_t x_496; 
x_496 = lean_nat_dec_lt(x_448, x_494);
if (x_496 == 0)
{
lean_dec(x_494);
lean_dec_ref(x_483);
lean_dec(x_6);
x_485 = lean_box(0);
goto block_493;
}
else
{
uint8_t x_497; 
x_497 = lean_nat_dec_le(x_494, x_494);
if (x_497 == 0)
{
lean_dec(x_494);
lean_dec_ref(x_483);
lean_dec(x_6);
x_485 = lean_box(0);
goto block_493;
}
else
{
lean_object* x_498; size_t x_499; size_t x_500; lean_object* x_501; 
x_498 = lean_box(0);
x_499 = 0;
x_500 = lean_usize_of_nat(x_494);
lean_dec(x_494);
x_501 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_483, x_499, x_500, x_498, x_6);
lean_dec(x_6);
lean_dec_ref(x_483);
if (lean_obj_tag(x_501) == 0)
{
lean_dec_ref(x_501);
x_485 = lean_box(0);
goto block_493;
}
else
{
uint8_t x_502; 
lean_dec_ref(x_484);
lean_dec(x_3);
x_502 = !lean_is_exclusive(x_501);
if (x_502 == 0)
{
return x_501;
}
else
{
lean_object* x_503; lean_object* x_504; 
x_503 = lean_ctor_get(x_501, 0);
lean_inc(x_503);
lean_dec(x_501);
x_504 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_504, 0, x_503);
return x_504;
}
}
}
}
}
block_508:
{
if (x_506 == 0)
{
lean_inc_ref(x_484);
lean_inc_ref(x_483);
lean_dec_ref(x_456);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec_ref(x_439);
lean_dec(x_438);
lean_dec_ref(x_1);
x_495 = lean_box(0);
goto block_505;
}
else
{
if (x_122 == 0)
{
lean_dec(x_494);
lean_dec(x_6);
x_467 = x_3;
x_468 = lean_box(0);
goto block_479;
}
else
{
lean_inc_ref(x_484);
lean_inc_ref(x_483);
lean_dec_ref(x_456);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec_ref(x_439);
lean_dec(x_438);
lean_dec_ref(x_1);
x_495 = lean_box(0);
goto block_505;
}
}
}
}
else
{
lean_object* x_518; 
lean_inc_ref(x_482);
lean_dec_ref(x_456);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec_ref(x_439);
lean_dec(x_438);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_518 = lean_ctor_get(x_482, 0);
lean_inc_ref(x_518);
lean_dec_ref(x_482);
lean_ctor_set(x_434, 0, x_518);
return x_434;
}
}
block_461:
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
if (lean_is_scalar(x_442)) {
 x_458 = lean_alloc_ctor(0, 4, 0);
} else {
 x_458 = x_442;
}
lean_ctor_set(x_458, 0, x_438);
lean_ctor_set(x_458, 1, x_456);
lean_ctor_set(x_458, 2, x_445);
lean_ctor_set(x_458, 3, x_453);
if (lean_is_scalar(x_446)) {
 x_459 = lean_alloc_ctor(4, 1, 0);
} else {
 x_459 = x_446;
 lean_ctor_set_tag(x_459, 4);
}
lean_ctor_set(x_459, 0, x_458);
if (lean_is_scalar(x_454)) {
 x_460 = lean_alloc_ctor(0, 1, 0);
} else {
 x_460 = x_454;
}
lean_ctor_set(x_460, 0, x_459);
return x_460;
}
block_466:
{
if (x_463 == 0)
{
lean_dec(x_451);
lean_dec(x_440);
lean_dec_ref(x_1);
x_457 = lean_box(0);
goto block_461;
}
else
{
uint8_t x_464; 
x_464 = l_Lean_instBEqFVarId_beq(x_440, x_445);
lean_dec(x_440);
if (x_464 == 0)
{
lean_dec(x_451);
lean_dec_ref(x_1);
x_457 = lean_box(0);
goto block_461;
}
else
{
lean_object* x_465; 
lean_dec_ref(x_456);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_442);
lean_dec(x_438);
if (lean_is_scalar(x_451)) {
 x_465 = lean_alloc_ctor(0, 1, 0);
} else {
 x_465 = x_451;
}
lean_ctor_set(x_465, 0, x_1);
return x_465;
}
}
}
block_479:
{
lean_object* x_469; 
lean_inc(x_445);
x_469 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_445, x_467);
lean_dec(x_467);
if (lean_obj_tag(x_469) == 0)
{
size_t x_470; size_t x_471; uint8_t x_472; 
lean_dec_ref(x_469);
x_470 = lean_ptr_addr(x_441);
lean_dec_ref(x_441);
x_471 = lean_ptr_addr(x_453);
x_472 = lean_usize_dec_eq(x_470, x_471);
if (x_472 == 0)
{
lean_dec_ref(x_439);
x_462 = lean_box(0);
x_463 = x_472;
goto block_466;
}
else
{
size_t x_473; size_t x_474; uint8_t x_475; 
x_473 = lean_ptr_addr(x_439);
lean_dec_ref(x_439);
x_474 = lean_ptr_addr(x_456);
x_475 = lean_usize_dec_eq(x_473, x_474);
x_462 = lean_box(0);
x_463 = x_475;
goto block_466;
}
}
else
{
uint8_t x_476; 
lean_dec_ref(x_456);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec_ref(x_439);
lean_dec(x_438);
lean_dec_ref(x_1);
x_476 = !lean_is_exclusive(x_469);
if (x_476 == 0)
{
return x_469;
}
else
{
lean_object* x_477; lean_object* x_478; 
x_477 = lean_ctor_get(x_469, 0);
lean_inc(x_477);
lean_dec(x_469);
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_477);
return x_478;
}
}
}
}
else
{
uint8_t x_519; 
lean_dec(x_451);
lean_dec_ref(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec_ref(x_439);
lean_dec(x_438);
lean_free_object(x_434);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_519 = !lean_is_exclusive(x_452);
if (x_519 == 0)
{
return x_452;
}
else
{
lean_object* x_520; lean_object* x_521; 
x_520 = lean_ctor_get(x_452, 0);
lean_inc(x_520);
lean_dec(x_452);
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_520);
return x_521;
}
}
}
else
{
uint8_t x_522; 
lean_dec_ref(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec_ref(x_439);
lean_dec(x_438);
lean_free_object(x_434);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_522 = !lean_is_exclusive(x_449);
if (x_522 == 0)
{
return x_449;
}
else
{
lean_object* x_523; lean_object* x_524; 
x_523 = lean_ctor_get(x_449, 0);
lean_inc(x_523);
lean_dec(x_449);
x_524 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_524, 0, x_523);
return x_524;
}
}
}
else
{
lean_object* x_525; 
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec_ref(x_439);
lean_dec(x_438);
lean_free_object(x_434);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_525 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_525;
}
}
else
{
lean_object* x_526; 
lean_dec_ref(x_433);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_526 = lean_ctor_get(x_436, 0);
lean_inc(x_526);
lean_dec_ref(x_436);
lean_ctor_set(x_434, 0, x_526);
return x_434;
}
}
else
{
lean_object* x_527; 
x_527 = lean_ctor_get(x_434, 0);
lean_inc(x_527);
lean_dec(x_434);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_528 = lean_st_ref_get(x_3);
x_529 = lean_ctor_get(x_433, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_433, 1);
lean_inc_ref(x_530);
x_531 = lean_ctor_get(x_433, 2);
lean_inc(x_531);
x_532 = lean_ctor_get(x_433, 3);
lean_inc_ref(x_532);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_533 = x_433;
} else {
 lean_dec_ref(x_433);
 x_533 = lean_box(0);
}
x_534 = lean_ctor_get(x_528, 0);
lean_inc_ref(x_534);
lean_dec_ref(x_528);
lean_inc(x_531);
x_535 = l_Lean_Compiler_LCNF_normFVarImp(x_534, x_531, x_122);
lean_dec_ref(x_534);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 x_537 = x_535;
} else {
 lean_dec_ref(x_535);
 x_537 = lean_box(0);
}
x_538 = lean_st_ref_get(x_3);
x_539 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_532);
lean_inc(x_536);
x_540 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_536, x_122, x_539, x_532, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 x_542 = x_540;
} else {
 lean_dec_ref(x_540);
 x_542 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_543 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_541, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_543) == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_553; uint8_t x_554; lean_object* x_558; lean_object* x_559; lean_object* x_571; uint8_t x_572; 
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
if (lean_is_exclusive(x_543)) {
 lean_ctor_release(x_543, 0);
 x_545 = x_543;
} else {
 lean_dec_ref(x_543);
 x_545 = lean_box(0);
}
x_546 = lean_ctor_get(x_538, 0);
lean_inc_ref(x_546);
lean_dec_ref(x_538);
lean_inc_ref(x_530);
x_547 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_546, x_122, x_530);
lean_dec_ref(x_546);
x_571 = lean_array_get_size(x_544);
x_572 = lean_nat_dec_eq(x_571, x_189);
lean_dec(x_571);
if (x_572 == 0)
{
lean_dec(x_6);
x_558 = x_3;
x_559 = lean_box(0);
goto block_570;
}
else
{
lean_object* x_573; 
x_573 = lean_array_fget_borrowed(x_544, x_539);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_584; lean_object* x_585; uint8_t x_596; lean_object* x_597; uint8_t x_599; 
x_574 = lean_ctor_get(x_573, 1);
x_575 = lean_ctor_get(x_573, 2);
x_584 = lean_array_get_size(x_574);
x_599 = lean_nat_dec_lt(x_539, x_584);
if (x_599 == 0)
{
x_596 = x_122;
x_597 = lean_box(0);
goto block_598;
}
else
{
if (x_599 == 0)
{
x_596 = x_122;
x_597 = lean_box(0);
goto block_598;
}
else
{
size_t x_600; size_t x_601; lean_object* x_602; 
x_600 = 0;
x_601 = lean_usize_of_nat(x_584);
x_602 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_574, x_600, x_601, x_3);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; uint8_t x_604; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
lean_dec_ref(x_602);
x_604 = lean_unbox(x_603);
lean_dec(x_603);
x_596 = x_604;
x_597 = lean_box(0);
goto block_598;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_584);
lean_dec_ref(x_547);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_542);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_605 = lean_ctor_get(x_602, 0);
lean_inc(x_605);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 x_606 = x_602;
} else {
 lean_dec_ref(x_602);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_606)) {
 x_607 = lean_alloc_ctor(1, 1, 0);
} else {
 x_607 = x_606;
}
lean_ctor_set(x_607, 0, x_605);
return x_607;
}
}
}
block_583:
{
lean_object* x_577; 
x_577 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; 
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 x_578 = x_577;
} else {
 lean_dec_ref(x_577);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(0, 1, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_575);
return x_579;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_dec_ref(x_575);
x_580 = lean_ctor_get(x_577, 0);
lean_inc(x_580);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 x_581 = x_577;
} else {
 lean_dec_ref(x_577);
 x_581 = lean_box(0);
}
if (lean_is_scalar(x_581)) {
 x_582 = lean_alloc_ctor(1, 1, 0);
} else {
 x_582 = x_581;
}
lean_ctor_set(x_582, 0, x_580);
return x_582;
}
}
block_595:
{
uint8_t x_586; 
x_586 = lean_nat_dec_lt(x_539, x_584);
if (x_586 == 0)
{
lean_dec(x_584);
lean_dec_ref(x_574);
lean_dec(x_6);
x_576 = lean_box(0);
goto block_583;
}
else
{
uint8_t x_587; 
x_587 = lean_nat_dec_le(x_584, x_584);
if (x_587 == 0)
{
lean_dec(x_584);
lean_dec_ref(x_574);
lean_dec(x_6);
x_576 = lean_box(0);
goto block_583;
}
else
{
lean_object* x_588; size_t x_589; size_t x_590; lean_object* x_591; 
x_588 = lean_box(0);
x_589 = 0;
x_590 = lean_usize_of_nat(x_584);
lean_dec(x_584);
x_591 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_574, x_589, x_590, x_588, x_6);
lean_dec(x_6);
lean_dec_ref(x_574);
if (lean_obj_tag(x_591) == 0)
{
lean_dec_ref(x_591);
x_576 = lean_box(0);
goto block_583;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec_ref(x_575);
lean_dec(x_3);
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 x_593 = x_591;
} else {
 lean_dec_ref(x_591);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(1, 1, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_592);
return x_594;
}
}
}
}
block_598:
{
if (x_596 == 0)
{
lean_inc_ref(x_575);
lean_inc_ref(x_574);
lean_dec_ref(x_547);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_542);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec_ref(x_1);
x_585 = lean_box(0);
goto block_595;
}
else
{
if (x_122 == 0)
{
lean_dec(x_584);
lean_dec(x_6);
x_558 = x_3;
x_559 = lean_box(0);
goto block_570;
}
else
{
lean_inc_ref(x_575);
lean_inc_ref(x_574);
lean_dec_ref(x_547);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_542);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec_ref(x_1);
x_585 = lean_box(0);
goto block_595;
}
}
}
}
else
{
lean_object* x_608; lean_object* x_609; 
lean_inc_ref(x_573);
lean_dec_ref(x_547);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_542);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_608 = lean_ctor_get(x_573, 0);
lean_inc_ref(x_608);
lean_dec_ref(x_573);
x_609 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_609, 0, x_608);
return x_609;
}
}
block_552:
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
if (lean_is_scalar(x_533)) {
 x_549 = lean_alloc_ctor(0, 4, 0);
} else {
 x_549 = x_533;
}
lean_ctor_set(x_549, 0, x_529);
lean_ctor_set(x_549, 1, x_547);
lean_ctor_set(x_549, 2, x_536);
lean_ctor_set(x_549, 3, x_544);
if (lean_is_scalar(x_537)) {
 x_550 = lean_alloc_ctor(4, 1, 0);
} else {
 x_550 = x_537;
 lean_ctor_set_tag(x_550, 4);
}
lean_ctor_set(x_550, 0, x_549);
if (lean_is_scalar(x_545)) {
 x_551 = lean_alloc_ctor(0, 1, 0);
} else {
 x_551 = x_545;
}
lean_ctor_set(x_551, 0, x_550);
return x_551;
}
block_557:
{
if (x_554 == 0)
{
lean_dec(x_542);
lean_dec(x_531);
lean_dec_ref(x_1);
x_548 = lean_box(0);
goto block_552;
}
else
{
uint8_t x_555; 
x_555 = l_Lean_instBEqFVarId_beq(x_531, x_536);
lean_dec(x_531);
if (x_555 == 0)
{
lean_dec(x_542);
lean_dec_ref(x_1);
x_548 = lean_box(0);
goto block_552;
}
else
{
lean_object* x_556; 
lean_dec_ref(x_547);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_533);
lean_dec(x_529);
if (lean_is_scalar(x_542)) {
 x_556 = lean_alloc_ctor(0, 1, 0);
} else {
 x_556 = x_542;
}
lean_ctor_set(x_556, 0, x_1);
return x_556;
}
}
}
block_570:
{
lean_object* x_560; 
lean_inc(x_536);
x_560 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_536, x_558);
lean_dec(x_558);
if (lean_obj_tag(x_560) == 0)
{
size_t x_561; size_t x_562; uint8_t x_563; 
lean_dec_ref(x_560);
x_561 = lean_ptr_addr(x_532);
lean_dec_ref(x_532);
x_562 = lean_ptr_addr(x_544);
x_563 = lean_usize_dec_eq(x_561, x_562);
if (x_563 == 0)
{
lean_dec_ref(x_530);
x_553 = lean_box(0);
x_554 = x_563;
goto block_557;
}
else
{
size_t x_564; size_t x_565; uint8_t x_566; 
x_564 = lean_ptr_addr(x_530);
lean_dec_ref(x_530);
x_565 = lean_ptr_addr(x_547);
x_566 = lean_usize_dec_eq(x_564, x_565);
x_553 = lean_box(0);
x_554 = x_566;
goto block_557;
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec_ref(x_547);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_542);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec_ref(x_1);
x_567 = lean_ctor_get(x_560, 0);
lean_inc(x_567);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 x_568 = x_560;
} else {
 lean_dec_ref(x_560);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(1, 1, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_567);
return x_569;
}
}
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_542);
lean_dec_ref(x_538);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_610 = lean_ctor_get(x_543, 0);
lean_inc(x_610);
if (lean_is_exclusive(x_543)) {
 lean_ctor_release(x_543, 0);
 x_611 = x_543;
} else {
 lean_dec_ref(x_543);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(1, 1, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_610);
return x_612;
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec_ref(x_538);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_613 = lean_ctor_get(x_540, 0);
lean_inc(x_613);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 x_614 = x_540;
} else {
 lean_dec_ref(x_540);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_614)) {
 x_615 = lean_alloc_ctor(1, 1, 0);
} else {
 x_615 = x_614;
}
lean_ctor_set(x_615, 0, x_613);
return x_615;
}
}
else
{
lean_object* x_616; 
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_616 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_616;
}
}
else
{
lean_object* x_617; lean_object* x_618; 
lean_dec_ref(x_433);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_617 = lean_ctor_get(x_527, 0);
lean_inc(x_617);
lean_dec_ref(x_527);
x_618 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_618, 0, x_617);
return x_618;
}
}
}
else
{
uint8_t x_619; 
lean_dec_ref(x_433);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_619 = !lean_is_exclusive(x_434);
if (x_619 == 0)
{
return x_434;
}
else
{
lean_object* x_620; lean_object* x_621; 
x_620 = lean_ctor_get(x_434, 0);
lean_inc(x_620);
lean_dec(x_434);
x_621 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_621, 0, x_620);
return x_621;
}
}
}
case 5:
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_free_object(x_138);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_622 = lean_ctor_get(x_1, 0);
x_623 = lean_st_ref_get(x_3);
x_624 = lean_ctor_get(x_623, 0);
lean_inc_ref(x_624);
lean_dec_ref(x_623);
lean_inc(x_622);
x_625 = l_Lean_Compiler_LCNF_normFVarImp(x_624, x_622, x_122);
lean_dec_ref(x_624);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
lean_dec_ref(x_625);
lean_inc(x_626);
x_627 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_626, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_627) == 0)
{
uint8_t x_628; 
x_628 = !lean_is_exclusive(x_627);
if (x_628 == 0)
{
lean_object* x_629; uint8_t x_630; 
x_629 = lean_ctor_get(x_627, 0);
lean_dec(x_629);
x_630 = l_Lean_instBEqFVarId_beq(x_622, x_626);
if (x_630 == 0)
{
uint8_t x_631; 
x_631 = !lean_is_exclusive(x_1);
if (x_631 == 0)
{
lean_object* x_632; 
x_632 = lean_ctor_get(x_1, 0);
lean_dec(x_632);
lean_ctor_set(x_1, 0, x_626);
lean_ctor_set(x_627, 0, x_1);
return x_627;
}
else
{
lean_object* x_633; 
lean_dec(x_1);
x_633 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_633, 0, x_626);
lean_ctor_set(x_627, 0, x_633);
return x_627;
}
}
else
{
lean_dec(x_626);
lean_ctor_set(x_627, 0, x_1);
return x_627;
}
}
else
{
uint8_t x_634; 
lean_dec(x_627);
x_634 = l_Lean_instBEqFVarId_beq(x_622, x_626);
if (x_634 == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_635 = x_1;
} else {
 lean_dec_ref(x_1);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(5, 1, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_626);
x_637 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_637, 0, x_636);
return x_637;
}
else
{
lean_object* x_638; 
lean_dec(x_626);
x_638 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_638, 0, x_1);
return x_638;
}
}
}
else
{
uint8_t x_639; 
lean_dec(x_626);
lean_dec_ref(x_1);
x_639 = !lean_is_exclusive(x_627);
if (x_639 == 0)
{
return x_627;
}
else
{
lean_object* x_640; lean_object* x_641; 
x_640 = lean_ctor_get(x_627, 0);
lean_inc(x_640);
lean_dec(x_627);
x_641 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_641, 0, x_640);
return x_641;
}
}
}
else
{
lean_object* x_642; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_642 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_642;
}
}
case 6:
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; size_t x_647; size_t x_648; uint8_t x_649; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_643 = lean_ctor_get(x_1, 0);
x_644 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_645 = lean_ctor_get(x_644, 0);
lean_inc_ref(x_645);
lean_dec_ref(x_644);
lean_inc_ref(x_643);
x_646 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_645, x_122, x_643);
lean_dec_ref(x_645);
x_647 = lean_ptr_addr(x_643);
x_648 = lean_ptr_addr(x_646);
x_649 = lean_usize_dec_eq(x_647, x_648);
if (x_649 == 0)
{
uint8_t x_650; 
x_650 = !lean_is_exclusive(x_1);
if (x_650 == 0)
{
lean_object* x_651; 
x_651 = lean_ctor_get(x_1, 0);
lean_dec(x_651);
lean_ctor_set(x_1, 0, x_646);
lean_ctor_set(x_138, 0, x_1);
return x_138;
}
else
{
lean_object* x_652; 
lean_dec(x_1);
x_652 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_652, 0, x_646);
lean_ctor_set(x_138, 0, x_652);
return x_138;
}
}
else
{
lean_dec_ref(x_646);
lean_ctor_set(x_138, 0, x_1);
return x_138;
}
}
default: 
{
lean_object* x_653; lean_object* x_654; 
lean_free_object(x_138);
x_653 = lean_ctor_get(x_1, 0);
x_654 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_654);
lean_inc_ref(x_653);
x_141 = x_653;
x_142 = x_654;
x_143 = x_2;
x_144 = x_3;
x_145 = x_4;
x_146 = x_5;
x_147 = x_6;
x_148 = x_7;
x_149 = x_8;
goto block_188;
}
}
block_188:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_141, 0);
x_151 = lean_ctor_get(x_141, 2);
x_152 = lean_ctor_get(x_141, 3);
x_153 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_150, x_144);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; uint8_t x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = lean_unbox(x_154);
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = lean_unbox(x_154);
lean_dec(x_154);
x_89 = x_157;
x_90 = x_142;
x_91 = x_141;
x_92 = x_143;
x_93 = x_144;
x_94 = x_145;
x_95 = x_146;
x_96 = x_147;
x_97 = x_148;
x_98 = x_149;
x_99 = lean_box(0);
goto block_105;
}
else
{
uint8_t x_158; 
lean_inc_ref(x_152);
x_158 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_152, x_151);
if (x_158 == 0)
{
uint8_t x_159; 
x_159 = lean_unbox(x_154);
lean_dec(x_154);
x_89 = x_159;
x_90 = x_142;
x_91 = x_141;
x_92 = x_143;
x_93 = x_144;
x_94 = x_145;
x_95 = x_146;
x_96 = x_147;
x_97 = x_148;
x_98 = x_149;
x_99 = lean_box(0);
goto block_105;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_st_ref_get(x_144);
x_161 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_161);
lean_dec_ref(x_160);
x_162 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_141, x_161, x_146, x_147, x_148, x_149);
lean_dec_ref(x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec_ref(x_162);
lean_inc(x_149);
lean_inc_ref(x_148);
lean_inc(x_147);
lean_inc_ref(x_146);
x_164 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_163, x_146, x_147, x_148, x_149);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec_ref(x_164);
x_166 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_144);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
lean_dec_ref(x_166);
x_167 = lean_unbox(x_154);
lean_dec(x_154);
x_89 = x_167;
x_90 = x_142;
x_91 = x_165;
x_92 = x_143;
x_93 = x_144;
x_94 = x_145;
x_95 = x_146;
x_96 = x_147;
x_97 = x_148;
x_98 = x_149;
x_99 = lean_box(0);
goto block_105;
}
else
{
uint8_t x_168; 
lean_dec(x_165);
lean_dec(x_154);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_1);
x_168 = !lean_is_exclusive(x_166);
if (x_168 == 0)
{
return x_166;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_154);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_1);
x_171 = !lean_is_exclusive(x_164);
if (x_171 == 0)
{
return x_164;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_164, 0);
lean_inc(x_172);
lean_dec(x_164);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_154);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_1);
x_174 = !lean_is_exclusive(x_162);
if (x_174 == 0)
{
return x_162;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_162, 0);
lean_inc(x_175);
lean_dec(x_162);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
return x_176;
}
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_st_ref_get(x_144);
x_178 = lean_ctor_get(x_177, 0);
lean_inc_ref(x_178);
lean_dec_ref(x_177);
x_179 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_141, x_178, x_146, x_147, x_148, x_149);
lean_dec_ref(x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; uint8_t x_181; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
x_181 = lean_unbox(x_154);
lean_dec(x_154);
x_57 = x_181;
x_58 = x_142;
x_59 = x_180;
x_60 = x_143;
x_61 = x_144;
x_62 = x_145;
x_63 = x_146;
x_64 = x_147;
x_65 = x_148;
x_66 = x_149;
x_67 = lean_box(0);
goto block_88;
}
else
{
uint8_t x_182; 
lean_dec(x_154);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_1);
x_182 = !lean_is_exclusive(x_179);
if (x_182 == 0)
{
return x_179;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_179, 0);
lean_inc(x_183);
lean_dec(x_179);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_1);
x_185 = !lean_is_exclusive(x_153);
if (x_185 == 0)
{
return x_153;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_153, 0);
lean_inc(x_186);
lean_dec(x_153);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
return x_187;
}
}
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_703; lean_object* x_704; 
lean_dec(x_138);
x_703 = lean_unsigned_to_nat(1u);
x_704 = lean_nat_add(x_109, x_703);
lean_dec(x_109);
lean_ctor_set(x_7, 3, x_704);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_844; 
x_705 = lean_ctor_get(x_1, 0);
x_706 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_705);
x_844 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_122, x_705, x_3, x_6);
if (lean_obj_tag(x_844) == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; uint8_t x_879; 
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
lean_dec_ref(x_844);
x_879 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_705, x_845);
if (x_879 == 0)
{
goto block_878;
}
else
{
if (x_122 == 0)
{
x_846 = x_2;
x_847 = x_3;
x_848 = x_4;
x_849 = x_5;
x_850 = x_6;
x_851 = x_7;
x_852 = x_8;
x_853 = lean_box(0);
goto block_873;
}
else
{
goto block_878;
}
}
block_873:
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; 
x_854 = lean_ctor_get(x_845, 2);
x_855 = lean_ctor_get(x_845, 3);
lean_inc(x_852);
lean_inc_ref(x_851);
lean_inc(x_850);
lean_inc_ref(x_849);
lean_inc_ref(x_848);
lean_inc(x_855);
x_856 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_855, x_846, x_848, x_849, x_850, x_851, x_852);
if (lean_obj_tag(x_856) == 0)
{
lean_object* x_857; 
x_857 = lean_ctor_get(x_856, 0);
lean_inc(x_857);
lean_dec_ref(x_856);
if (lean_obj_tag(x_857) == 0)
{
lean_inc(x_855);
lean_inc_ref(x_854);
x_829 = x_845;
x_830 = x_854;
x_831 = x_855;
x_832 = x_846;
x_833 = x_847;
x_834 = x_848;
x_835 = x_849;
x_836 = x_850;
x_837 = x_851;
x_838 = x_852;
x_839 = lean_box(0);
goto block_843;
}
else
{
lean_object* x_858; lean_object* x_859; 
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
lean_dec_ref(x_857);
x_859 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_847);
if (lean_obj_tag(x_859) == 0)
{
lean_object* x_860; 
lean_dec_ref(x_859);
x_860 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_845, x_858, x_850);
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
lean_dec_ref(x_860);
x_862 = lean_ctor_get(x_861, 2);
lean_inc_ref(x_862);
x_863 = lean_ctor_get(x_861, 3);
lean_inc(x_863);
x_829 = x_861;
x_830 = x_862;
x_831 = x_863;
x_832 = x_846;
x_833 = x_847;
x_834 = x_848;
x_835 = x_849;
x_836 = x_850;
x_837 = x_851;
x_838 = x_852;
x_839 = lean_box(0);
goto block_843;
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; 
lean_dec(x_852);
lean_dec_ref(x_851);
lean_dec(x_850);
lean_dec_ref(x_849);
lean_dec_ref(x_848);
lean_dec(x_847);
lean_dec_ref(x_846);
lean_dec_ref(x_1);
x_864 = lean_ctor_get(x_860, 0);
lean_inc(x_864);
if (lean_is_exclusive(x_860)) {
 lean_ctor_release(x_860, 0);
 x_865 = x_860;
} else {
 lean_dec_ref(x_860);
 x_865 = lean_box(0);
}
if (lean_is_scalar(x_865)) {
 x_866 = lean_alloc_ctor(1, 1, 0);
} else {
 x_866 = x_865;
}
lean_ctor_set(x_866, 0, x_864);
return x_866;
}
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; 
lean_dec(x_858);
lean_dec(x_852);
lean_dec_ref(x_851);
lean_dec(x_850);
lean_dec_ref(x_849);
lean_dec_ref(x_848);
lean_dec(x_847);
lean_dec_ref(x_846);
lean_dec(x_845);
lean_dec_ref(x_1);
x_867 = lean_ctor_get(x_859, 0);
lean_inc(x_867);
if (lean_is_exclusive(x_859)) {
 lean_ctor_release(x_859, 0);
 x_868 = x_859;
} else {
 lean_dec_ref(x_859);
 x_868 = lean_box(0);
}
if (lean_is_scalar(x_868)) {
 x_869 = lean_alloc_ctor(1, 1, 0);
} else {
 x_869 = x_868;
}
lean_ctor_set(x_869, 0, x_867);
return x_869;
}
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; 
lean_dec(x_852);
lean_dec_ref(x_851);
lean_dec(x_850);
lean_dec_ref(x_849);
lean_dec_ref(x_848);
lean_dec(x_847);
lean_dec_ref(x_846);
lean_dec(x_845);
lean_dec_ref(x_1);
x_870 = lean_ctor_get(x_856, 0);
lean_inc(x_870);
if (lean_is_exclusive(x_856)) {
 lean_ctor_release(x_856, 0);
 x_871 = x_856;
} else {
 lean_dec_ref(x_856);
 x_871 = lean_box(0);
}
if (lean_is_scalar(x_871)) {
 x_872 = lean_alloc_ctor(1, 1, 0);
} else {
 x_872 = x_871;
}
lean_ctor_set(x_872, 0, x_870);
return x_872;
}
}
block_878:
{
lean_object* x_874; 
x_874 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_874) == 0)
{
lean_dec_ref(x_874);
x_846 = x_2;
x_847 = x_3;
x_848 = x_4;
x_849 = x_5;
x_850 = x_6;
x_851 = x_7;
x_852 = x_8;
x_853 = lean_box(0);
goto block_873;
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; 
lean_dec(x_845);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_875 = lean_ctor_get(x_874, 0);
lean_inc(x_875);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 x_876 = x_874;
} else {
 lean_dec_ref(x_874);
 x_876 = lean_box(0);
}
if (lean_is_scalar(x_876)) {
 x_877 = lean_alloc_ctor(1, 1, 0);
} else {
 x_877 = x_876;
}
lean_ctor_set(x_877, 0, x_875);
return x_877;
}
}
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_880 = lean_ctor_get(x_844, 0);
lean_inc(x_880);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 x_881 = x_844;
} else {
 lean_dec_ref(x_844);
 x_881 = lean_box(0);
}
if (lean_is_scalar(x_881)) {
 x_882 = lean_alloc_ctor(1, 1, 0);
} else {
 x_882 = x_881;
}
lean_ctor_set(x_882, 0, x_880);
return x_882;
}
block_828:
{
if (x_716 == 0)
{
lean_object* x_717; 
lean_inc(x_707);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_711);
lean_inc_ref(x_708);
x_717 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_708, x_711, x_709, x_715, x_707);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
lean_dec_ref(x_717);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; 
lean_inc(x_707);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_711);
lean_inc_ref(x_708);
x_719 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_708, x_714, x_713, x_711, x_709, x_715, x_707);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; 
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
lean_dec_ref(x_719);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_721 = lean_ctor_get(x_708, 0);
x_722 = lean_ctor_get(x_708, 3);
x_723 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_722);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
lean_dec_ref(x_723);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; 
lean_inc(x_707);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_711);
lean_inc_ref(x_712);
lean_inc(x_713);
lean_inc_ref(x_714);
lean_inc_ref(x_706);
lean_inc_ref(x_708);
x_725 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_708, x_706, x_714, x_713, x_712, x_711, x_709, x_715, x_707);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; 
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
lean_dec_ref(x_725);
if (lean_obj_tag(x_726) == 0)
{
lean_object* x_727; 
lean_inc(x_707);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_711);
lean_inc_ref(x_712);
lean_inc(x_713);
lean_inc_ref(x_714);
lean_inc(x_722);
x_727 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_722, x_714, x_713, x_712, x_711, x_709, x_715, x_707);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
lean_dec_ref(x_727);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; 
lean_inc(x_707);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_711);
lean_inc_ref(x_712);
lean_inc(x_713);
lean_inc_ref(x_714);
lean_inc_ref(x_706);
x_729 = l_Lean_Compiler_LCNF_Simp_simp(x_706, x_714, x_713, x_712, x_711, x_709, x_715, x_707);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
lean_dec_ref(x_729);
x_731 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_721, x_713);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; uint8_t x_733; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
lean_dec_ref(x_731);
x_733 = lean_unbox(x_732);
lean_dec(x_732);
if (x_733 == 0)
{
lean_object* x_734; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_707);
lean_dec_ref(x_1);
x_734 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_708, x_713, x_709);
lean_dec(x_709);
lean_dec(x_713);
lean_dec_ref(x_708);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; 
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 x_735 = x_734;
} else {
 lean_dec_ref(x_734);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(0, 1, 0);
} else {
 x_736 = x_735;
}
lean_ctor_set(x_736, 0, x_730);
return x_736;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
lean_dec(x_730);
x_737 = lean_ctor_get(x_734, 0);
lean_inc(x_737);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 x_738 = x_734;
} else {
 lean_dec_ref(x_734);
 x_738 = lean_box(0);
}
if (lean_is_scalar(x_738)) {
 x_739 = lean_alloc_ctor(1, 1, 0);
} else {
 x_739 = x_738;
}
lean_ctor_set(x_739, 0, x_737);
return x_739;
}
}
else
{
lean_object* x_740; 
lean_inc_ref(x_708);
x_740 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_708, x_714, x_713, x_712, x_711, x_709, x_715, x_707);
lean_dec(x_707);
lean_dec_ref(x_715);
lean_dec(x_709);
lean_dec_ref(x_711);
lean_dec_ref(x_712);
lean_dec(x_713);
lean_dec_ref(x_714);
if (lean_obj_tag(x_740) == 0)
{
size_t x_741; size_t x_742; uint8_t x_743; 
lean_dec_ref(x_740);
x_741 = lean_ptr_addr(x_706);
x_742 = lean_ptr_addr(x_730);
x_743 = lean_usize_dec_eq(x_741, x_742);
if (x_743 == 0)
{
x_10 = x_708;
x_11 = lean_box(0);
x_12 = x_730;
x_13 = x_743;
goto block_17;
}
else
{
size_t x_744; size_t x_745; uint8_t x_746; 
x_744 = lean_ptr_addr(x_705);
x_745 = lean_ptr_addr(x_708);
x_746 = lean_usize_dec_eq(x_744, x_745);
x_10 = x_708;
x_11 = lean_box(0);
x_12 = x_730;
x_13 = x_746;
goto block_17;
}
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_730);
lean_dec_ref(x_708);
lean_dec_ref(x_1);
x_747 = lean_ctor_get(x_740, 0);
lean_inc(x_747);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 x_748 = x_740;
} else {
 lean_dec_ref(x_740);
 x_748 = lean_box(0);
}
if (lean_is_scalar(x_748)) {
 x_749 = lean_alloc_ctor(1, 1, 0);
} else {
 x_749 = x_748;
}
lean_ctor_set(x_749, 0, x_747);
return x_749;
}
}
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
lean_dec(x_730);
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec_ref(x_708);
lean_dec(x_707);
lean_dec_ref(x_1);
x_750 = lean_ctor_get(x_731, 0);
lean_inc(x_750);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 x_751 = x_731;
} else {
 lean_dec_ref(x_731);
 x_751 = lean_box(0);
}
if (lean_is_scalar(x_751)) {
 x_752 = lean_alloc_ctor(1, 1, 0);
} else {
 x_752 = x_751;
}
lean_ctor_set(x_752, 0, x_750);
return x_752;
}
}
else
{
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec_ref(x_708);
lean_dec(x_707);
lean_dec_ref(x_1);
return x_729;
}
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; 
lean_inc_ref(x_706);
lean_dec_ref(x_1);
x_753 = lean_ctor_get(x_728, 0);
lean_inc(x_753);
lean_dec_ref(x_728);
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_753, 1);
lean_inc(x_755);
lean_dec(x_753);
lean_inc(x_721);
x_756 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_721, x_755, x_713, x_709, x_715, x_707);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; 
lean_dec_ref(x_756);
x_757 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_708, x_713, x_709);
lean_dec_ref(x_708);
if (lean_obj_tag(x_757) == 0)
{
lean_object* x_758; 
lean_dec_ref(x_757);
lean_inc(x_707);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_711);
lean_inc_ref(x_712);
lean_inc(x_713);
lean_inc_ref(x_714);
x_758 = l_Lean_Compiler_LCNF_Simp_simp(x_706, x_714, x_713, x_712, x_711, x_709, x_715, x_707);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
lean_dec_ref(x_758);
x_760 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_754, x_759, x_714, x_713, x_712, x_711, x_709, x_715, x_707);
lean_dec(x_707);
lean_dec_ref(x_715);
lean_dec(x_709);
lean_dec_ref(x_711);
lean_dec_ref(x_712);
lean_dec(x_713);
lean_dec_ref(x_714);
lean_dec(x_754);
return x_760;
}
else
{
lean_dec(x_754);
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec(x_707);
return x_758;
}
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; 
lean_dec(x_754);
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec(x_707);
lean_dec_ref(x_706);
x_761 = lean_ctor_get(x_757, 0);
lean_inc(x_761);
if (lean_is_exclusive(x_757)) {
 lean_ctor_release(x_757, 0);
 x_762 = x_757;
} else {
 lean_dec_ref(x_757);
 x_762 = lean_box(0);
}
if (lean_is_scalar(x_762)) {
 x_763 = lean_alloc_ctor(1, 1, 0);
} else {
 x_763 = x_762;
}
lean_ctor_set(x_763, 0, x_761);
return x_763;
}
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_754);
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec_ref(x_708);
lean_dec(x_707);
lean_dec_ref(x_706);
x_764 = lean_ctor_get(x_756, 0);
lean_inc(x_764);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 x_765 = x_756;
} else {
 lean_dec_ref(x_756);
 x_765 = lean_box(0);
}
if (lean_is_scalar(x_765)) {
 x_766 = lean_alloc_ctor(1, 1, 0);
} else {
 x_766 = x_765;
}
lean_ctor_set(x_766, 0, x_764);
return x_766;
}
}
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec_ref(x_708);
lean_dec(x_707);
lean_dec_ref(x_1);
x_767 = lean_ctor_get(x_727, 0);
lean_inc(x_767);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 x_768 = x_727;
} else {
 lean_dec_ref(x_727);
 x_768 = lean_box(0);
}
if (lean_is_scalar(x_768)) {
 x_769 = lean_alloc_ctor(1, 1, 0);
} else {
 x_769 = x_768;
}
lean_ctor_set(x_769, 0, x_767);
return x_769;
}
}
else
{
lean_object* x_770; lean_object* x_771; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_707);
lean_dec_ref(x_1);
x_770 = lean_ctor_get(x_726, 0);
lean_inc(x_770);
lean_dec_ref(x_726);
x_771 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_708, x_713, x_709);
lean_dec(x_709);
lean_dec(x_713);
lean_dec_ref(x_708);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; 
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 x_772 = x_771;
} else {
 lean_dec_ref(x_771);
 x_772 = lean_box(0);
}
if (lean_is_scalar(x_772)) {
 x_773 = lean_alloc_ctor(0, 1, 0);
} else {
 x_773 = x_772;
}
lean_ctor_set(x_773, 0, x_770);
return x_773;
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_770);
x_774 = lean_ctor_get(x_771, 0);
lean_inc(x_774);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 x_775 = x_771;
} else {
 lean_dec_ref(x_771);
 x_775 = lean_box(0);
}
if (lean_is_scalar(x_775)) {
 x_776 = lean_alloc_ctor(1, 1, 0);
} else {
 x_776 = x_775;
}
lean_ctor_set(x_776, 0, x_774);
return x_776;
}
}
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec_ref(x_708);
lean_dec(x_707);
lean_dec_ref(x_1);
x_777 = lean_ctor_get(x_725, 0);
lean_inc(x_777);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 x_778 = x_725;
} else {
 lean_dec_ref(x_725);
 x_778 = lean_box(0);
}
if (lean_is_scalar(x_778)) {
 x_779 = lean_alloc_ctor(1, 1, 0);
} else {
 x_779 = x_778;
}
lean_ctor_set(x_779, 0, x_777);
return x_779;
}
}
else
{
lean_object* x_780; lean_object* x_781; 
lean_inc_ref(x_706);
lean_dec_ref(x_1);
x_780 = lean_ctor_get(x_724, 0);
lean_inc(x_780);
lean_dec_ref(x_724);
lean_inc(x_721);
x_781 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_721, x_780, x_713, x_709, x_715, x_707);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; 
lean_dec_ref(x_781);
x_782 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_708, x_713, x_709);
lean_dec_ref(x_708);
if (lean_obj_tag(x_782) == 0)
{
lean_dec_ref(x_782);
x_1 = x_706;
x_2 = x_714;
x_3 = x_713;
x_4 = x_712;
x_5 = x_711;
x_6 = x_709;
x_7 = x_715;
x_8 = x_707;
goto _start;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec(x_707);
lean_dec_ref(x_706);
x_784 = lean_ctor_get(x_782, 0);
lean_inc(x_784);
if (lean_is_exclusive(x_782)) {
 lean_ctor_release(x_782, 0);
 x_785 = x_782;
} else {
 lean_dec_ref(x_782);
 x_785 = lean_box(0);
}
if (lean_is_scalar(x_785)) {
 x_786 = lean_alloc_ctor(1, 1, 0);
} else {
 x_786 = x_785;
}
lean_ctor_set(x_786, 0, x_784);
return x_786;
}
}
else
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec_ref(x_708);
lean_dec(x_707);
lean_dec_ref(x_706);
x_787 = lean_ctor_get(x_781, 0);
lean_inc(x_787);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 x_788 = x_781;
} else {
 lean_dec_ref(x_781);
 x_788 = lean_box(0);
}
if (lean_is_scalar(x_788)) {
 x_789 = lean_alloc_ctor(1, 1, 0);
} else {
 x_789 = x_788;
}
lean_ctor_set(x_789, 0, x_787);
return x_789;
}
}
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
lean_dec_ref(x_708);
lean_inc_ref(x_706);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_790 = x_1;
} else {
 lean_dec_ref(x_1);
 x_790 = lean_box(0);
}
x_791 = lean_ctor_get(x_720, 0);
lean_inc(x_791);
lean_dec_ref(x_720);
if (lean_is_scalar(x_790)) {
 x_792 = lean_alloc_ctor(1, 2, 0);
} else {
 x_792 = x_790;
 lean_ctor_set_tag(x_792, 1);
}
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_792, 1, x_706);
x_1 = x_792;
x_2 = x_714;
x_3 = x_713;
x_4 = x_712;
x_5 = x_711;
x_6 = x_709;
x_7 = x_715;
x_8 = x_707;
goto _start;
}
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec_ref(x_708);
lean_dec(x_707);
lean_dec_ref(x_1);
x_794 = lean_ctor_get(x_719, 0);
lean_inc(x_794);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 x_795 = x_719;
} else {
 lean_dec_ref(x_719);
 x_795 = lean_box(0);
}
if (lean_is_scalar(x_795)) {
 x_796 = lean_alloc_ctor(1, 1, 0);
} else {
 x_796 = x_795;
}
lean_ctor_set(x_796, 0, x_794);
return x_796;
}
}
else
{
lean_object* x_797; lean_object* x_798; 
lean_dec_ref(x_708);
lean_inc_ref(x_706);
lean_dec_ref(x_1);
x_797 = lean_ctor_get(x_718, 0);
lean_inc(x_797);
lean_dec_ref(x_718);
x_798 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_713);
if (lean_obj_tag(x_798) == 0)
{
lean_object* x_799; 
lean_dec_ref(x_798);
lean_inc(x_707);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_711);
lean_inc_ref(x_712);
lean_inc(x_713);
lean_inc_ref(x_714);
x_799 = l_Lean_Compiler_LCNF_Simp_simp(x_706, x_714, x_713, x_712, x_711, x_709, x_715, x_707);
if (lean_obj_tag(x_799) == 0)
{
lean_object* x_800; lean_object* x_801; 
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
lean_dec_ref(x_799);
x_801 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_797, x_800, x_714, x_713, x_712, x_711, x_709, x_715, x_707);
lean_dec(x_707);
lean_dec_ref(x_715);
lean_dec(x_709);
lean_dec_ref(x_711);
lean_dec_ref(x_712);
lean_dec(x_713);
lean_dec_ref(x_714);
lean_dec(x_797);
return x_801;
}
else
{
lean_dec(x_797);
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec(x_707);
return x_799;
}
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
lean_dec(x_797);
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec(x_707);
lean_dec_ref(x_706);
x_802 = lean_ctor_get(x_798, 0);
lean_inc(x_802);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 x_803 = x_798;
} else {
 lean_dec_ref(x_798);
 x_803 = lean_box(0);
}
if (lean_is_scalar(x_803)) {
 x_804 = lean_alloc_ctor(1, 1, 0);
} else {
 x_804 = x_803;
}
lean_ctor_set(x_804, 0, x_802);
return x_804;
}
}
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec_ref(x_708);
lean_dec(x_707);
lean_dec_ref(x_1);
x_805 = lean_ctor_get(x_717, 0);
lean_inc(x_805);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 x_806 = x_717;
} else {
 lean_dec_ref(x_717);
 x_806 = lean_box(0);
}
if (lean_is_scalar(x_806)) {
 x_807 = lean_alloc_ctor(1, 1, 0);
} else {
 x_807 = x_806;
}
lean_ctor_set(x_807, 0, x_805);
return x_807;
}
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; uint8_t x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_inc_ref(x_706);
lean_dec_ref(x_1);
x_808 = lean_st_ref_take(x_713);
x_809 = lean_ctor_get(x_708, 0);
x_810 = lean_ctor_get(x_808, 0);
lean_inc_ref(x_810);
x_811 = lean_ctor_get(x_808, 1);
lean_inc_ref(x_811);
x_812 = lean_ctor_get(x_808, 2);
lean_inc(x_812);
x_813 = lean_ctor_get(x_808, 3);
lean_inc_ref(x_813);
x_814 = lean_ctor_get_uint8(x_808, sizeof(void*)*7);
x_815 = lean_ctor_get(x_808, 4);
lean_inc(x_815);
x_816 = lean_ctor_get(x_808, 5);
lean_inc(x_816);
x_817 = lean_ctor_get(x_808, 6);
lean_inc(x_817);
if (lean_is_exclusive(x_808)) {
 lean_ctor_release(x_808, 0);
 lean_ctor_release(x_808, 1);
 lean_ctor_release(x_808, 2);
 lean_ctor_release(x_808, 3);
 lean_ctor_release(x_808, 4);
 lean_ctor_release(x_808, 5);
 lean_ctor_release(x_808, 6);
 x_818 = x_808;
} else {
 lean_dec_ref(x_808);
 x_818 = lean_box(0);
}
x_819 = lean_box(0);
lean_inc(x_809);
x_820 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_810, x_809, x_819);
if (lean_is_scalar(x_818)) {
 x_821 = lean_alloc_ctor(0, 7, 1);
} else {
 x_821 = x_818;
}
lean_ctor_set(x_821, 0, x_820);
lean_ctor_set(x_821, 1, x_811);
lean_ctor_set(x_821, 2, x_812);
lean_ctor_set(x_821, 3, x_813);
lean_ctor_set(x_821, 4, x_815);
lean_ctor_set(x_821, 5, x_816);
lean_ctor_set(x_821, 6, x_817);
lean_ctor_set_uint8(x_821, sizeof(void*)*7, x_814);
x_822 = lean_st_ref_set(x_713, x_821);
x_823 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_708, x_713, x_709);
lean_dec_ref(x_708);
if (lean_obj_tag(x_823) == 0)
{
lean_dec_ref(x_823);
x_1 = x_706;
x_2 = x_714;
x_3 = x_713;
x_4 = x_712;
x_5 = x_711;
x_6 = x_709;
x_7 = x_715;
x_8 = x_707;
goto _start;
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec(x_709);
lean_dec(x_707);
lean_dec_ref(x_706);
x_825 = lean_ctor_get(x_823, 0);
lean_inc(x_825);
if (lean_is_exclusive(x_823)) {
 lean_ctor_release(x_823, 0);
 x_826 = x_823;
} else {
 lean_dec_ref(x_823);
 x_826 = lean_box(0);
}
if (lean_is_scalar(x_826)) {
 x_827 = lean_alloc_ctor(1, 1, 0);
} else {
 x_827 = x_826;
}
lean_ctor_set(x_827, 0, x_825);
return x_827;
}
}
}
block_843:
{
uint8_t x_840; 
x_840 = l_Lean_Expr_isErased(x_830);
lean_dec_ref(x_830);
if (x_840 == 0)
{
lean_dec(x_831);
x_707 = x_838;
x_708 = x_829;
x_709 = x_836;
x_710 = lean_box(0);
x_711 = x_835;
x_712 = x_834;
x_713 = x_833;
x_714 = x_832;
x_715 = x_837;
x_716 = x_122;
goto block_828;
}
else
{
lean_object* x_841; uint8_t x_842; 
x_841 = lean_box(1);
x_842 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_831, x_841);
lean_dec(x_831);
if (x_842 == 0)
{
x_707 = x_838;
x_708 = x_829;
x_709 = x_836;
x_710 = lean_box(0);
x_711 = x_835;
x_712 = x_834;
x_713 = x_833;
x_714 = x_832;
x_715 = x_837;
x_716 = x_840;
goto block_828;
}
else
{
x_707 = x_838;
x_708 = x_829;
x_709 = x_836;
x_710 = lean_box(0);
x_711 = x_835;
x_712 = x_834;
x_713 = x_833;
x_714 = x_832;
x_715 = x_837;
x_716 = x_122;
goto block_828;
}
}
}
}
case 3:
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_883 = lean_ctor_get(x_1, 0);
x_884 = lean_ctor_get(x_1, 1);
x_885 = lean_st_ref_get(x_3);
x_886 = lean_ctor_get(x_885, 0);
lean_inc_ref(x_886);
lean_dec_ref(x_885);
lean_inc(x_883);
x_887 = l_Lean_Compiler_LCNF_normFVarImp(x_886, x_883, x_122);
lean_dec_ref(x_886);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; uint8_t x_893; lean_object* x_899; lean_object* x_905; 
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
lean_dec_ref(x_887);
lean_inc_ref(x_884);
x_889 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_122, x_884, x_3);
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 x_891 = x_889;
} else {
 lean_dec_ref(x_889);
 x_891 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_890);
x_905 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_888, x_890, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_905) == 0)
{
lean_object* x_906; 
x_906 = lean_ctor_get(x_905, 0);
lean_inc(x_906);
lean_dec_ref(x_905);
if (lean_obj_tag(x_906) == 0)
{
lean_object* x_907; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_888);
x_907 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_888, x_3);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; lean_object* x_909; uint8_t x_910; 
lean_dec_ref(x_907);
x_908 = lean_unsigned_to_nat(0u);
x_909 = lean_array_get_size(x_890);
x_910 = lean_nat_dec_lt(x_908, x_909);
if (x_910 == 0)
{
lean_dec(x_909);
lean_dec(x_3);
x_899 = lean_box(0);
goto block_904;
}
else
{
uint8_t x_911; 
x_911 = lean_nat_dec_le(x_909, x_909);
if (x_911 == 0)
{
lean_dec(x_909);
lean_dec(x_3);
x_899 = lean_box(0);
goto block_904;
}
else
{
lean_object* x_912; size_t x_913; size_t x_914; lean_object* x_915; 
x_912 = lean_box(0);
x_913 = 0;
x_914 = lean_usize_of_nat(x_909);
lean_dec(x_909);
x_915 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_890, x_913, x_914, x_912, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_915) == 0)
{
lean_dec_ref(x_915);
x_899 = lean_box(0);
goto block_904;
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_888);
lean_dec_ref(x_1);
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 x_917 = x_915;
} else {
 lean_dec_ref(x_915);
 x_917 = lean_box(0);
}
if (lean_is_scalar(x_917)) {
 x_918 = lean_alloc_ctor(1, 1, 0);
} else {
 x_918 = x_917;
}
lean_ctor_set(x_918, 0, x_916);
return x_918;
}
}
}
}
else
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_888);
lean_dec(x_3);
lean_dec_ref(x_1);
x_919 = lean_ctor_get(x_907, 0);
lean_inc(x_919);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 x_920 = x_907;
} else {
 lean_dec_ref(x_907);
 x_920 = lean_box(0);
}
if (lean_is_scalar(x_920)) {
 x_921 = lean_alloc_ctor(1, 1, 0);
} else {
 x_921 = x_920;
}
lean_ctor_set(x_921, 0, x_919);
return x_921;
}
}
else
{
lean_object* x_922; 
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_888);
lean_dec_ref(x_1);
x_922 = lean_ctor_get(x_906, 0);
lean_inc(x_922);
lean_dec_ref(x_906);
x_1 = x_922;
goto _start;
}
}
else
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; 
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_888);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_924 = lean_ctor_get(x_905, 0);
lean_inc(x_924);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 x_925 = x_905;
} else {
 lean_dec_ref(x_905);
 x_925 = lean_box(0);
}
if (lean_is_scalar(x_925)) {
 x_926 = lean_alloc_ctor(1, 1, 0);
} else {
 x_926 = x_925;
}
lean_ctor_set(x_926, 0, x_924);
return x_926;
}
block_898:
{
if (x_893 == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_894 = x_1;
} else {
 lean_dec_ref(x_1);
 x_894 = lean_box(0);
}
if (lean_is_scalar(x_894)) {
 x_895 = lean_alloc_ctor(3, 2, 0);
} else {
 x_895 = x_894;
}
lean_ctor_set(x_895, 0, x_888);
lean_ctor_set(x_895, 1, x_890);
if (lean_is_scalar(x_891)) {
 x_896 = lean_alloc_ctor(0, 1, 0);
} else {
 x_896 = x_891;
}
lean_ctor_set(x_896, 0, x_895);
return x_896;
}
else
{
lean_object* x_897; 
lean_dec(x_890);
lean_dec(x_888);
if (lean_is_scalar(x_891)) {
 x_897 = lean_alloc_ctor(0, 1, 0);
} else {
 x_897 = x_891;
}
lean_ctor_set(x_897, 0, x_1);
return x_897;
}
}
block_904:
{
uint8_t x_900; 
x_900 = l_Lean_instBEqFVarId_beq(x_883, x_888);
if (x_900 == 0)
{
x_892 = lean_box(0);
x_893 = x_900;
goto block_898;
}
else
{
size_t x_901; size_t x_902; uint8_t x_903; 
x_901 = lean_ptr_addr(x_884);
x_902 = lean_ptr_addr(x_890);
x_903 = lean_usize_dec_eq(x_901, x_902);
x_892 = lean_box(0);
x_893 = x_903;
goto block_898;
}
}
}
else
{
lean_object* x_927; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_927 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_927;
}
}
case 4:
{
lean_object* x_928; lean_object* x_929; 
x_928 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_928);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_928);
x_929 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_928, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; 
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 x_931 = x_929;
} else {
 lean_dec_ref(x_929);
 x_931 = lean_box(0);
}
if (lean_obj_tag(x_930) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; 
x_932 = lean_st_ref_get(x_3);
x_933 = lean_ctor_get(x_928, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_928, 1);
lean_inc_ref(x_934);
x_935 = lean_ctor_get(x_928, 2);
lean_inc(x_935);
x_936 = lean_ctor_get(x_928, 3);
lean_inc_ref(x_936);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 lean_ctor_release(x_928, 2);
 lean_ctor_release(x_928, 3);
 x_937 = x_928;
} else {
 lean_dec_ref(x_928);
 x_937 = lean_box(0);
}
x_938 = lean_ctor_get(x_932, 0);
lean_inc_ref(x_938);
lean_dec_ref(x_932);
lean_inc(x_935);
x_939 = l_Lean_Compiler_LCNF_normFVarImp(x_938, x_935, x_122);
lean_dec_ref(x_938);
if (lean_obj_tag(x_939) == 0)
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_940 = lean_ctor_get(x_939, 0);
lean_inc(x_940);
if (lean_is_exclusive(x_939)) {
 lean_ctor_release(x_939, 0);
 x_941 = x_939;
} else {
 lean_dec_ref(x_939);
 x_941 = lean_box(0);
}
x_942 = lean_st_ref_get(x_3);
x_943 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_936);
lean_inc(x_940);
x_944 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_940, x_122, x_943, x_936, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
if (lean_is_exclusive(x_944)) {
 lean_ctor_release(x_944, 0);
 x_946 = x_944;
} else {
 lean_dec_ref(x_944);
 x_946 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_947 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_945, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_947) == 0)
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_957; uint8_t x_958; lean_object* x_962; lean_object* x_963; lean_object* x_975; uint8_t x_976; 
x_948 = lean_ctor_get(x_947, 0);
lean_inc(x_948);
if (lean_is_exclusive(x_947)) {
 lean_ctor_release(x_947, 0);
 x_949 = x_947;
} else {
 lean_dec_ref(x_947);
 x_949 = lean_box(0);
}
x_950 = lean_ctor_get(x_942, 0);
lean_inc_ref(x_950);
lean_dec_ref(x_942);
lean_inc_ref(x_934);
x_951 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_950, x_122, x_934);
lean_dec_ref(x_950);
x_975 = lean_array_get_size(x_948);
x_976 = lean_nat_dec_eq(x_975, x_703);
lean_dec(x_975);
if (x_976 == 0)
{
lean_dec(x_931);
lean_dec(x_6);
x_962 = x_3;
x_963 = lean_box(0);
goto block_974;
}
else
{
lean_object* x_977; 
x_977 = lean_array_fget_borrowed(x_948, x_943);
if (lean_obj_tag(x_977) == 0)
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_988; lean_object* x_989; uint8_t x_1000; lean_object* x_1001; uint8_t x_1003; 
lean_dec(x_931);
x_978 = lean_ctor_get(x_977, 1);
x_979 = lean_ctor_get(x_977, 2);
x_988 = lean_array_get_size(x_978);
x_1003 = lean_nat_dec_lt(x_943, x_988);
if (x_1003 == 0)
{
x_1000 = x_122;
x_1001 = lean_box(0);
goto block_1002;
}
else
{
if (x_1003 == 0)
{
x_1000 = x_122;
x_1001 = lean_box(0);
goto block_1002;
}
else
{
size_t x_1004; size_t x_1005; lean_object* x_1006; 
x_1004 = 0;
x_1005 = lean_usize_of_nat(x_988);
x_1006 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_978, x_1004, x_1005, x_3);
if (lean_obj_tag(x_1006) == 0)
{
lean_object* x_1007; uint8_t x_1008; 
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
lean_dec_ref(x_1006);
x_1008 = lean_unbox(x_1007);
lean_dec(x_1007);
x_1000 = x_1008;
x_1001 = lean_box(0);
goto block_1002;
}
else
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
lean_dec(x_988);
lean_dec_ref(x_951);
lean_dec(x_949);
lean_dec(x_948);
lean_dec(x_946);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec_ref(x_934);
lean_dec(x_933);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1009 = lean_ctor_get(x_1006, 0);
lean_inc(x_1009);
if (lean_is_exclusive(x_1006)) {
 lean_ctor_release(x_1006, 0);
 x_1010 = x_1006;
} else {
 lean_dec_ref(x_1006);
 x_1010 = lean_box(0);
}
if (lean_is_scalar(x_1010)) {
 x_1011 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1011 = x_1010;
}
lean_ctor_set(x_1011, 0, x_1009);
return x_1011;
}
}
}
block_987:
{
lean_object* x_981; 
x_981 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_981) == 0)
{
lean_object* x_982; lean_object* x_983; 
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 x_982 = x_981;
} else {
 lean_dec_ref(x_981);
 x_982 = lean_box(0);
}
if (lean_is_scalar(x_982)) {
 x_983 = lean_alloc_ctor(0, 1, 0);
} else {
 x_983 = x_982;
}
lean_ctor_set(x_983, 0, x_979);
return x_983;
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; 
lean_dec_ref(x_979);
x_984 = lean_ctor_get(x_981, 0);
lean_inc(x_984);
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 x_985 = x_981;
} else {
 lean_dec_ref(x_981);
 x_985 = lean_box(0);
}
if (lean_is_scalar(x_985)) {
 x_986 = lean_alloc_ctor(1, 1, 0);
} else {
 x_986 = x_985;
}
lean_ctor_set(x_986, 0, x_984);
return x_986;
}
}
block_999:
{
uint8_t x_990; 
x_990 = lean_nat_dec_lt(x_943, x_988);
if (x_990 == 0)
{
lean_dec(x_988);
lean_dec_ref(x_978);
lean_dec(x_6);
x_980 = lean_box(0);
goto block_987;
}
else
{
uint8_t x_991; 
x_991 = lean_nat_dec_le(x_988, x_988);
if (x_991 == 0)
{
lean_dec(x_988);
lean_dec_ref(x_978);
lean_dec(x_6);
x_980 = lean_box(0);
goto block_987;
}
else
{
lean_object* x_992; size_t x_993; size_t x_994; lean_object* x_995; 
x_992 = lean_box(0);
x_993 = 0;
x_994 = lean_usize_of_nat(x_988);
lean_dec(x_988);
x_995 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_978, x_993, x_994, x_992, x_6);
lean_dec(x_6);
lean_dec_ref(x_978);
if (lean_obj_tag(x_995) == 0)
{
lean_dec_ref(x_995);
x_980 = lean_box(0);
goto block_987;
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; 
lean_dec_ref(x_979);
lean_dec(x_3);
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
if (lean_is_exclusive(x_995)) {
 lean_ctor_release(x_995, 0);
 x_997 = x_995;
} else {
 lean_dec_ref(x_995);
 x_997 = lean_box(0);
}
if (lean_is_scalar(x_997)) {
 x_998 = lean_alloc_ctor(1, 1, 0);
} else {
 x_998 = x_997;
}
lean_ctor_set(x_998, 0, x_996);
return x_998;
}
}
}
}
block_1002:
{
if (x_1000 == 0)
{
lean_inc_ref(x_979);
lean_inc_ref(x_978);
lean_dec_ref(x_951);
lean_dec(x_949);
lean_dec(x_948);
lean_dec(x_946);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec_ref(x_934);
lean_dec(x_933);
lean_dec_ref(x_1);
x_989 = lean_box(0);
goto block_999;
}
else
{
if (x_122 == 0)
{
lean_dec(x_988);
lean_dec(x_6);
x_962 = x_3;
x_963 = lean_box(0);
goto block_974;
}
else
{
lean_inc_ref(x_979);
lean_inc_ref(x_978);
lean_dec_ref(x_951);
lean_dec(x_949);
lean_dec(x_948);
lean_dec(x_946);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec_ref(x_934);
lean_dec(x_933);
lean_dec_ref(x_1);
x_989 = lean_box(0);
goto block_999;
}
}
}
}
else
{
lean_object* x_1012; lean_object* x_1013; 
lean_inc_ref(x_977);
lean_dec_ref(x_951);
lean_dec(x_949);
lean_dec(x_948);
lean_dec(x_946);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec_ref(x_934);
lean_dec(x_933);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1012 = lean_ctor_get(x_977, 0);
lean_inc_ref(x_1012);
lean_dec_ref(x_977);
if (lean_is_scalar(x_931)) {
 x_1013 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1013 = x_931;
}
lean_ctor_set(x_1013, 0, x_1012);
return x_1013;
}
}
block_956:
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; 
if (lean_is_scalar(x_937)) {
 x_953 = lean_alloc_ctor(0, 4, 0);
} else {
 x_953 = x_937;
}
lean_ctor_set(x_953, 0, x_933);
lean_ctor_set(x_953, 1, x_951);
lean_ctor_set(x_953, 2, x_940);
lean_ctor_set(x_953, 3, x_948);
if (lean_is_scalar(x_941)) {
 x_954 = lean_alloc_ctor(4, 1, 0);
} else {
 x_954 = x_941;
 lean_ctor_set_tag(x_954, 4);
}
lean_ctor_set(x_954, 0, x_953);
if (lean_is_scalar(x_949)) {
 x_955 = lean_alloc_ctor(0, 1, 0);
} else {
 x_955 = x_949;
}
lean_ctor_set(x_955, 0, x_954);
return x_955;
}
block_961:
{
if (x_958 == 0)
{
lean_dec(x_946);
lean_dec(x_935);
lean_dec_ref(x_1);
x_952 = lean_box(0);
goto block_956;
}
else
{
uint8_t x_959; 
x_959 = l_Lean_instBEqFVarId_beq(x_935, x_940);
lean_dec(x_935);
if (x_959 == 0)
{
lean_dec(x_946);
lean_dec_ref(x_1);
x_952 = lean_box(0);
goto block_956;
}
else
{
lean_object* x_960; 
lean_dec_ref(x_951);
lean_dec(x_949);
lean_dec(x_948);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_937);
lean_dec(x_933);
if (lean_is_scalar(x_946)) {
 x_960 = lean_alloc_ctor(0, 1, 0);
} else {
 x_960 = x_946;
}
lean_ctor_set(x_960, 0, x_1);
return x_960;
}
}
}
block_974:
{
lean_object* x_964; 
lean_inc(x_940);
x_964 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_940, x_962);
lean_dec(x_962);
if (lean_obj_tag(x_964) == 0)
{
size_t x_965; size_t x_966; uint8_t x_967; 
lean_dec_ref(x_964);
x_965 = lean_ptr_addr(x_936);
lean_dec_ref(x_936);
x_966 = lean_ptr_addr(x_948);
x_967 = lean_usize_dec_eq(x_965, x_966);
if (x_967 == 0)
{
lean_dec_ref(x_934);
x_957 = lean_box(0);
x_958 = x_967;
goto block_961;
}
else
{
size_t x_968; size_t x_969; uint8_t x_970; 
x_968 = lean_ptr_addr(x_934);
lean_dec_ref(x_934);
x_969 = lean_ptr_addr(x_951);
x_970 = lean_usize_dec_eq(x_968, x_969);
x_957 = lean_box(0);
x_958 = x_970;
goto block_961;
}
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
lean_dec_ref(x_951);
lean_dec(x_949);
lean_dec(x_948);
lean_dec(x_946);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec_ref(x_934);
lean_dec(x_933);
lean_dec_ref(x_1);
x_971 = lean_ctor_get(x_964, 0);
lean_inc(x_971);
if (lean_is_exclusive(x_964)) {
 lean_ctor_release(x_964, 0);
 x_972 = x_964;
} else {
 lean_dec_ref(x_964);
 x_972 = lean_box(0);
}
if (lean_is_scalar(x_972)) {
 x_973 = lean_alloc_ctor(1, 1, 0);
} else {
 x_973 = x_972;
}
lean_ctor_set(x_973, 0, x_971);
return x_973;
}
}
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
lean_dec(x_946);
lean_dec_ref(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec_ref(x_934);
lean_dec(x_933);
lean_dec(x_931);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1014 = lean_ctor_get(x_947, 0);
lean_inc(x_1014);
if (lean_is_exclusive(x_947)) {
 lean_ctor_release(x_947, 0);
 x_1015 = x_947;
} else {
 lean_dec_ref(x_947);
 x_1015 = lean_box(0);
}
if (lean_is_scalar(x_1015)) {
 x_1016 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1016 = x_1015;
}
lean_ctor_set(x_1016, 0, x_1014);
return x_1016;
}
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
lean_dec_ref(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec_ref(x_934);
lean_dec(x_933);
lean_dec(x_931);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1017 = lean_ctor_get(x_944, 0);
lean_inc(x_1017);
if (lean_is_exclusive(x_944)) {
 lean_ctor_release(x_944, 0);
 x_1018 = x_944;
} else {
 lean_dec_ref(x_944);
 x_1018 = lean_box(0);
}
if (lean_is_scalar(x_1018)) {
 x_1019 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1019 = x_1018;
}
lean_ctor_set(x_1019, 0, x_1017);
return x_1019;
}
}
else
{
lean_object* x_1020; 
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec_ref(x_934);
lean_dec(x_933);
lean_dec(x_931);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1020 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1020;
}
}
else
{
lean_object* x_1021; lean_object* x_1022; 
lean_dec_ref(x_928);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1021 = lean_ctor_get(x_930, 0);
lean_inc(x_1021);
lean_dec_ref(x_930);
if (lean_is_scalar(x_931)) {
 x_1022 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1022 = x_931;
}
lean_ctor_set(x_1022, 0, x_1021);
return x_1022;
}
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
lean_dec_ref(x_928);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1023 = lean_ctor_get(x_929, 0);
lean_inc(x_1023);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 x_1024 = x_929;
} else {
 lean_dec_ref(x_929);
 x_1024 = lean_box(0);
}
if (lean_is_scalar(x_1024)) {
 x_1025 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1025 = x_1024;
}
lean_ctor_set(x_1025, 0, x_1023);
return x_1025;
}
}
case 5:
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1026 = lean_ctor_get(x_1, 0);
x_1027 = lean_st_ref_get(x_3);
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc_ref(x_1028);
lean_dec_ref(x_1027);
lean_inc(x_1026);
x_1029 = l_Lean_Compiler_LCNF_normFVarImp(x_1028, x_1026, x_122);
lean_dec_ref(x_1028);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
lean_dec_ref(x_1029);
lean_inc(x_1030);
x_1031 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1030, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; uint8_t x_1033; 
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 x_1032 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1032 = lean_box(0);
}
x_1033 = l_Lean_instBEqFVarId_beq(x_1026, x_1030);
if (x_1033 == 0)
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1034 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1034 = lean_box(0);
}
if (lean_is_scalar(x_1034)) {
 x_1035 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1035 = x_1034;
}
lean_ctor_set(x_1035, 0, x_1030);
if (lean_is_scalar(x_1032)) {
 x_1036 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1036 = x_1032;
}
lean_ctor_set(x_1036, 0, x_1035);
return x_1036;
}
else
{
lean_object* x_1037; 
lean_dec(x_1030);
if (lean_is_scalar(x_1032)) {
 x_1037 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1037 = x_1032;
}
lean_ctor_set(x_1037, 0, x_1);
return x_1037;
}
}
else
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
lean_dec(x_1030);
lean_dec_ref(x_1);
x_1038 = lean_ctor_get(x_1031, 0);
lean_inc(x_1038);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 x_1039 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1039 = lean_box(0);
}
if (lean_is_scalar(x_1039)) {
 x_1040 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1040 = x_1039;
}
lean_ctor_set(x_1040, 0, x_1038);
return x_1040;
}
}
else
{
lean_object* x_1041; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1041 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1041;
}
}
case 6:
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; size_t x_1046; size_t x_1047; uint8_t x_1048; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1042 = lean_ctor_get(x_1, 0);
x_1043 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_1044 = lean_ctor_get(x_1043, 0);
lean_inc_ref(x_1044);
lean_dec_ref(x_1043);
lean_inc_ref(x_1042);
x_1045 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1044, x_122, x_1042);
lean_dec_ref(x_1044);
x_1046 = lean_ptr_addr(x_1042);
x_1047 = lean_ptr_addr(x_1045);
x_1048 = lean_usize_dec_eq(x_1046, x_1047);
if (x_1048 == 0)
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1049 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1049 = lean_box(0);
}
if (lean_is_scalar(x_1049)) {
 x_1050 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1050 = x_1049;
}
lean_ctor_set(x_1050, 0, x_1045);
x_1051 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1051, 0, x_1050);
return x_1051;
}
else
{
lean_object* x_1052; 
lean_dec_ref(x_1045);
x_1052 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1052, 0, x_1);
return x_1052;
}
}
default: 
{
lean_object* x_1053; lean_object* x_1054; 
x_1053 = lean_ctor_get(x_1, 0);
x_1054 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1054);
lean_inc_ref(x_1053);
x_655 = x_1053;
x_656 = x_1054;
x_657 = x_2;
x_658 = x_3;
x_659 = x_4;
x_660 = x_5;
x_661 = x_6;
x_662 = x_7;
x_663 = x_8;
goto block_702;
}
}
block_702:
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_664 = lean_ctor_get(x_655, 0);
x_665 = lean_ctor_get(x_655, 2);
x_666 = lean_ctor_get(x_655, 3);
x_667 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_664, x_658);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; uint8_t x_669; 
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
lean_dec_ref(x_667);
x_669 = lean_unbox(x_668);
if (x_669 == 0)
{
uint8_t x_670; 
x_670 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
if (x_670 == 0)
{
uint8_t x_671; 
x_671 = lean_unbox(x_668);
lean_dec(x_668);
x_89 = x_671;
x_90 = x_656;
x_91 = x_655;
x_92 = x_657;
x_93 = x_658;
x_94 = x_659;
x_95 = x_660;
x_96 = x_661;
x_97 = x_662;
x_98 = x_663;
x_99 = lean_box(0);
goto block_105;
}
else
{
uint8_t x_672; 
lean_inc_ref(x_666);
x_672 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_666, x_665);
if (x_672 == 0)
{
uint8_t x_673; 
x_673 = lean_unbox(x_668);
lean_dec(x_668);
x_89 = x_673;
x_90 = x_656;
x_91 = x_655;
x_92 = x_657;
x_93 = x_658;
x_94 = x_659;
x_95 = x_660;
x_96 = x_661;
x_97 = x_662;
x_98 = x_663;
x_99 = lean_box(0);
goto block_105;
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_674 = lean_st_ref_get(x_658);
x_675 = lean_ctor_get(x_674, 0);
lean_inc_ref(x_675);
lean_dec_ref(x_674);
x_676 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_655, x_675, x_660, x_661, x_662, x_663);
lean_dec_ref(x_675);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
lean_dec_ref(x_676);
lean_inc(x_663);
lean_inc_ref(x_662);
lean_inc(x_661);
lean_inc_ref(x_660);
x_678 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_677, x_660, x_661, x_662, x_663);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
lean_dec_ref(x_678);
x_680 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_658);
if (lean_obj_tag(x_680) == 0)
{
uint8_t x_681; 
lean_dec_ref(x_680);
x_681 = lean_unbox(x_668);
lean_dec(x_668);
x_89 = x_681;
x_90 = x_656;
x_91 = x_679;
x_92 = x_657;
x_93 = x_658;
x_94 = x_659;
x_95 = x_660;
x_96 = x_661;
x_97 = x_662;
x_98 = x_663;
x_99 = lean_box(0);
goto block_105;
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_679);
lean_dec(x_668);
lean_dec(x_663);
lean_dec_ref(x_662);
lean_dec(x_661);
lean_dec_ref(x_660);
lean_dec_ref(x_659);
lean_dec(x_658);
lean_dec_ref(x_657);
lean_dec_ref(x_656);
lean_dec_ref(x_1);
x_682 = lean_ctor_get(x_680, 0);
lean_inc(x_682);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 x_683 = x_680;
} else {
 lean_dec_ref(x_680);
 x_683 = lean_box(0);
}
if (lean_is_scalar(x_683)) {
 x_684 = lean_alloc_ctor(1, 1, 0);
} else {
 x_684 = x_683;
}
lean_ctor_set(x_684, 0, x_682);
return x_684;
}
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
lean_dec(x_668);
lean_dec(x_663);
lean_dec_ref(x_662);
lean_dec(x_661);
lean_dec_ref(x_660);
lean_dec_ref(x_659);
lean_dec(x_658);
lean_dec_ref(x_657);
lean_dec_ref(x_656);
lean_dec_ref(x_1);
x_685 = lean_ctor_get(x_678, 0);
lean_inc(x_685);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 x_686 = x_678;
} else {
 lean_dec_ref(x_678);
 x_686 = lean_box(0);
}
if (lean_is_scalar(x_686)) {
 x_687 = lean_alloc_ctor(1, 1, 0);
} else {
 x_687 = x_686;
}
lean_ctor_set(x_687, 0, x_685);
return x_687;
}
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_668);
lean_dec(x_663);
lean_dec_ref(x_662);
lean_dec(x_661);
lean_dec_ref(x_660);
lean_dec_ref(x_659);
lean_dec(x_658);
lean_dec_ref(x_657);
lean_dec_ref(x_656);
lean_dec_ref(x_1);
x_688 = lean_ctor_get(x_676, 0);
lean_inc(x_688);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 x_689 = x_676;
} else {
 lean_dec_ref(x_676);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(1, 1, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_688);
return x_690;
}
}
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_691 = lean_st_ref_get(x_658);
x_692 = lean_ctor_get(x_691, 0);
lean_inc_ref(x_692);
lean_dec_ref(x_691);
x_693 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_655, x_692, x_660, x_661, x_662, x_663);
lean_dec_ref(x_692);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; uint8_t x_695; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
lean_dec_ref(x_693);
x_695 = lean_unbox(x_668);
lean_dec(x_668);
x_57 = x_695;
x_58 = x_656;
x_59 = x_694;
x_60 = x_657;
x_61 = x_658;
x_62 = x_659;
x_63 = x_660;
x_64 = x_661;
x_65 = x_662;
x_66 = x_663;
x_67 = lean_box(0);
goto block_88;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_668);
lean_dec(x_663);
lean_dec_ref(x_662);
lean_dec(x_661);
lean_dec_ref(x_660);
lean_dec_ref(x_659);
lean_dec(x_658);
lean_dec_ref(x_657);
lean_dec_ref(x_656);
lean_dec_ref(x_1);
x_696 = lean_ctor_get(x_693, 0);
lean_inc(x_696);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 x_697 = x_693;
} else {
 lean_dec_ref(x_693);
 x_697 = lean_box(0);
}
if (lean_is_scalar(x_697)) {
 x_698 = lean_alloc_ctor(1, 1, 0);
} else {
 x_698 = x_697;
}
lean_ctor_set(x_698, 0, x_696);
return x_698;
}
}
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_dec(x_663);
lean_dec_ref(x_662);
lean_dec(x_661);
lean_dec_ref(x_660);
lean_dec_ref(x_659);
lean_dec(x_658);
lean_dec_ref(x_657);
lean_dec_ref(x_656);
lean_dec_ref(x_655);
lean_dec_ref(x_1);
x_699 = lean_ctor_get(x_667, 0);
lean_inc(x_699);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 x_700 = x_667;
} else {
 lean_dec_ref(x_667);
 x_700 = lean_box(0);
}
if (lean_is_scalar(x_700)) {
 x_701 = lean_alloc_ctor(1, 1, 0);
} else {
 x_701 = x_700;
}
lean_ctor_set(x_701, 0, x_699);
return x_701;
}
}
}
}
else
{
uint8_t x_1055; 
lean_free_object(x_7);
lean_dec_ref(x_121);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1055 = !lean_is_exclusive(x_138);
if (x_1055 == 0)
{
return x_138;
}
else
{
lean_object* x_1056; lean_object* x_1057; 
x_1056 = lean_ctor_get(x_138, 0);
lean_inc(x_1056);
lean_dec(x_138);
x_1057 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1057, 0, x_1056);
return x_1057;
}
}
}
else
{
lean_object* x_1058; 
lean_dec(x_7);
x_1058 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3);
if (lean_obj_tag(x_1058) == 0)
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
if (lean_is_exclusive(x_1058)) {
 lean_ctor_release(x_1058, 0);
 x_1059 = x_1058;
} else {
 lean_dec_ref(x_1058);
 x_1059 = lean_box(0);
}
x_1108 = lean_unsigned_to_nat(1u);
x_1109 = lean_nat_add(x_109, x_1108);
lean_dec(x_109);
x_1110 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_1110, 0, x_106);
lean_ctor_set(x_1110, 1, x_107);
lean_ctor_set(x_1110, 2, x_108);
lean_ctor_set(x_1110, 3, x_1109);
lean_ctor_set(x_1110, 4, x_110);
lean_ctor_set(x_1110, 5, x_111);
lean_ctor_set(x_1110, 6, x_112);
lean_ctor_set(x_1110, 7, x_113);
lean_ctor_set(x_1110, 8, x_114);
lean_ctor_set(x_1110, 9, x_115);
lean_ctor_set(x_1110, 10, x_116);
lean_ctor_set(x_1110, 11, x_117);
lean_ctor_set(x_1110, 12, x_119);
lean_ctor_set(x_1110, 13, x_121);
lean_ctor_set_uint8(x_1110, sizeof(void*)*14, x_118);
lean_ctor_set_uint8(x_1110, sizeof(void*)*14 + 1, x_120);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; uint8_t x_1122; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1250; 
lean_dec(x_1059);
x_1111 = lean_ctor_get(x_1, 0);
x_1112 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1111);
x_1250 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_122, x_1111, x_3, x_6);
if (lean_obj_tag(x_1250) == 0)
{
lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; uint8_t x_1285; 
x_1251 = lean_ctor_get(x_1250, 0);
lean_inc(x_1251);
lean_dec_ref(x_1250);
x_1285 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_1111, x_1251);
if (x_1285 == 0)
{
goto block_1284;
}
else
{
if (x_122 == 0)
{
x_1252 = x_2;
x_1253 = x_3;
x_1254 = x_4;
x_1255 = x_5;
x_1256 = x_6;
x_1257 = x_1110;
x_1258 = x_8;
x_1259 = lean_box(0);
goto block_1279;
}
else
{
goto block_1284;
}
}
block_1279:
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
x_1260 = lean_ctor_get(x_1251, 2);
x_1261 = lean_ctor_get(x_1251, 3);
lean_inc(x_1258);
lean_inc_ref(x_1257);
lean_inc(x_1256);
lean_inc_ref(x_1255);
lean_inc_ref(x_1254);
lean_inc(x_1261);
x_1262 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_1261, x_1252, x_1254, x_1255, x_1256, x_1257, x_1258);
if (lean_obj_tag(x_1262) == 0)
{
lean_object* x_1263; 
x_1263 = lean_ctor_get(x_1262, 0);
lean_inc(x_1263);
lean_dec_ref(x_1262);
if (lean_obj_tag(x_1263) == 0)
{
lean_inc(x_1261);
lean_inc_ref(x_1260);
x_1235 = x_1251;
x_1236 = x_1260;
x_1237 = x_1261;
x_1238 = x_1252;
x_1239 = x_1253;
x_1240 = x_1254;
x_1241 = x_1255;
x_1242 = x_1256;
x_1243 = x_1257;
x_1244 = x_1258;
x_1245 = lean_box(0);
goto block_1249;
}
else
{
lean_object* x_1264; lean_object* x_1265; 
x_1264 = lean_ctor_get(x_1263, 0);
lean_inc(x_1264);
lean_dec_ref(x_1263);
x_1265 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1253);
if (lean_obj_tag(x_1265) == 0)
{
lean_object* x_1266; 
lean_dec_ref(x_1265);
x_1266 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_1251, x_1264, x_1256);
if (lean_obj_tag(x_1266) == 0)
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1266, 0);
lean_inc(x_1267);
lean_dec_ref(x_1266);
x_1268 = lean_ctor_get(x_1267, 2);
lean_inc_ref(x_1268);
x_1269 = lean_ctor_get(x_1267, 3);
lean_inc(x_1269);
x_1235 = x_1267;
x_1236 = x_1268;
x_1237 = x_1269;
x_1238 = x_1252;
x_1239 = x_1253;
x_1240 = x_1254;
x_1241 = x_1255;
x_1242 = x_1256;
x_1243 = x_1257;
x_1244 = x_1258;
x_1245 = lean_box(0);
goto block_1249;
}
else
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
lean_dec(x_1258);
lean_dec_ref(x_1257);
lean_dec(x_1256);
lean_dec_ref(x_1255);
lean_dec_ref(x_1254);
lean_dec(x_1253);
lean_dec_ref(x_1252);
lean_dec_ref(x_1);
x_1270 = lean_ctor_get(x_1266, 0);
lean_inc(x_1270);
if (lean_is_exclusive(x_1266)) {
 lean_ctor_release(x_1266, 0);
 x_1271 = x_1266;
} else {
 lean_dec_ref(x_1266);
 x_1271 = lean_box(0);
}
if (lean_is_scalar(x_1271)) {
 x_1272 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1272 = x_1271;
}
lean_ctor_set(x_1272, 0, x_1270);
return x_1272;
}
}
else
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; 
lean_dec(x_1264);
lean_dec(x_1258);
lean_dec_ref(x_1257);
lean_dec(x_1256);
lean_dec_ref(x_1255);
lean_dec_ref(x_1254);
lean_dec(x_1253);
lean_dec_ref(x_1252);
lean_dec(x_1251);
lean_dec_ref(x_1);
x_1273 = lean_ctor_get(x_1265, 0);
lean_inc(x_1273);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 x_1274 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_1274 = lean_box(0);
}
if (lean_is_scalar(x_1274)) {
 x_1275 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1275 = x_1274;
}
lean_ctor_set(x_1275, 0, x_1273);
return x_1275;
}
}
}
else
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
lean_dec(x_1258);
lean_dec_ref(x_1257);
lean_dec(x_1256);
lean_dec_ref(x_1255);
lean_dec_ref(x_1254);
lean_dec(x_1253);
lean_dec_ref(x_1252);
lean_dec(x_1251);
lean_dec_ref(x_1);
x_1276 = lean_ctor_get(x_1262, 0);
lean_inc(x_1276);
if (lean_is_exclusive(x_1262)) {
 lean_ctor_release(x_1262, 0);
 x_1277 = x_1262;
} else {
 lean_dec_ref(x_1262);
 x_1277 = lean_box(0);
}
if (lean_is_scalar(x_1277)) {
 x_1278 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1278 = x_1277;
}
lean_ctor_set(x_1278, 0, x_1276);
return x_1278;
}
}
block_1284:
{
lean_object* x_1280; 
x_1280 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_1280) == 0)
{
lean_dec_ref(x_1280);
x_1252 = x_2;
x_1253 = x_3;
x_1254 = x_4;
x_1255 = x_5;
x_1256 = x_6;
x_1257 = x_1110;
x_1258 = x_8;
x_1259 = lean_box(0);
goto block_1279;
}
else
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
lean_dec(x_1251);
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1281 = lean_ctor_get(x_1280, 0);
lean_inc(x_1281);
if (lean_is_exclusive(x_1280)) {
 lean_ctor_release(x_1280, 0);
 x_1282 = x_1280;
} else {
 lean_dec_ref(x_1280);
 x_1282 = lean_box(0);
}
if (lean_is_scalar(x_1282)) {
 x_1283 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1283 = x_1282;
}
lean_ctor_set(x_1283, 0, x_1281);
return x_1283;
}
}
}
else
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1286 = lean_ctor_get(x_1250, 0);
lean_inc(x_1286);
if (lean_is_exclusive(x_1250)) {
 lean_ctor_release(x_1250, 0);
 x_1287 = x_1250;
} else {
 lean_dec_ref(x_1250);
 x_1287 = lean_box(0);
}
if (lean_is_scalar(x_1287)) {
 x_1288 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1288 = x_1287;
}
lean_ctor_set(x_1288, 0, x_1286);
return x_1288;
}
block_1234:
{
if (x_1122 == 0)
{
lean_object* x_1123; 
lean_inc(x_1113);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1117);
lean_inc_ref(x_1114);
x_1123 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_1114, x_1117, x_1115, x_1121, x_1113);
if (lean_obj_tag(x_1123) == 0)
{
lean_object* x_1124; 
x_1124 = lean_ctor_get(x_1123, 0);
lean_inc(x_1124);
lean_dec_ref(x_1123);
if (lean_obj_tag(x_1124) == 0)
{
lean_object* x_1125; 
lean_inc(x_1113);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1117);
lean_inc_ref(x_1114);
x_1125 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1114, x_1120, x_1119, x_1117, x_1115, x_1121, x_1113);
if (lean_obj_tag(x_1125) == 0)
{
lean_object* x_1126; 
x_1126 = lean_ctor_get(x_1125, 0);
lean_inc(x_1126);
lean_dec_ref(x_1125);
if (lean_obj_tag(x_1126) == 0)
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1127 = lean_ctor_get(x_1114, 0);
x_1128 = lean_ctor_get(x_1114, 3);
x_1129 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1128);
x_1130 = lean_ctor_get(x_1129, 0);
lean_inc(x_1130);
lean_dec_ref(x_1129);
if (lean_obj_tag(x_1130) == 0)
{
lean_object* x_1131; 
lean_inc(x_1113);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1117);
lean_inc_ref(x_1118);
lean_inc(x_1119);
lean_inc_ref(x_1120);
lean_inc_ref(x_1112);
lean_inc_ref(x_1114);
x_1131 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1114, x_1112, x_1120, x_1119, x_1118, x_1117, x_1115, x_1121, x_1113);
if (lean_obj_tag(x_1131) == 0)
{
lean_object* x_1132; 
x_1132 = lean_ctor_get(x_1131, 0);
lean_inc(x_1132);
lean_dec_ref(x_1131);
if (lean_obj_tag(x_1132) == 0)
{
lean_object* x_1133; 
lean_inc(x_1113);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1117);
lean_inc_ref(x_1118);
lean_inc(x_1119);
lean_inc_ref(x_1120);
lean_inc(x_1128);
x_1133 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_1128, x_1120, x_1119, x_1118, x_1117, x_1115, x_1121, x_1113);
if (lean_obj_tag(x_1133) == 0)
{
lean_object* x_1134; 
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
lean_dec_ref(x_1133);
if (lean_obj_tag(x_1134) == 0)
{
lean_object* x_1135; 
lean_inc(x_1113);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1117);
lean_inc_ref(x_1118);
lean_inc(x_1119);
lean_inc_ref(x_1120);
lean_inc_ref(x_1112);
x_1135 = l_Lean_Compiler_LCNF_Simp_simp(x_1112, x_1120, x_1119, x_1118, x_1117, x_1115, x_1121, x_1113);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; lean_object* x_1137; 
x_1136 = lean_ctor_get(x_1135, 0);
lean_inc(x_1136);
lean_dec_ref(x_1135);
x_1137 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_1127, x_1119);
if (lean_obj_tag(x_1137) == 0)
{
lean_object* x_1138; uint8_t x_1139; 
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
lean_dec_ref(x_1137);
x_1139 = lean_unbox(x_1138);
lean_dec(x_1138);
if (x_1139 == 0)
{
lean_object* x_1140; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1113);
lean_dec_ref(x_1);
x_1140 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1114, x_1119, x_1115);
lean_dec(x_1115);
lean_dec(x_1119);
lean_dec_ref(x_1114);
if (lean_obj_tag(x_1140) == 0)
{
lean_object* x_1141; lean_object* x_1142; 
if (lean_is_exclusive(x_1140)) {
 lean_ctor_release(x_1140, 0);
 x_1141 = x_1140;
} else {
 lean_dec_ref(x_1140);
 x_1141 = lean_box(0);
}
if (lean_is_scalar(x_1141)) {
 x_1142 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1142 = x_1141;
}
lean_ctor_set(x_1142, 0, x_1136);
return x_1142;
}
else
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
lean_dec(x_1136);
x_1143 = lean_ctor_get(x_1140, 0);
lean_inc(x_1143);
if (lean_is_exclusive(x_1140)) {
 lean_ctor_release(x_1140, 0);
 x_1144 = x_1140;
} else {
 lean_dec_ref(x_1140);
 x_1144 = lean_box(0);
}
if (lean_is_scalar(x_1144)) {
 x_1145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1145 = x_1144;
}
lean_ctor_set(x_1145, 0, x_1143);
return x_1145;
}
}
else
{
lean_object* x_1146; 
lean_inc_ref(x_1114);
x_1146 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_1114, x_1120, x_1119, x_1118, x_1117, x_1115, x_1121, x_1113);
lean_dec(x_1113);
lean_dec_ref(x_1121);
lean_dec(x_1115);
lean_dec_ref(x_1117);
lean_dec_ref(x_1118);
lean_dec(x_1119);
lean_dec_ref(x_1120);
if (lean_obj_tag(x_1146) == 0)
{
size_t x_1147; size_t x_1148; uint8_t x_1149; 
lean_dec_ref(x_1146);
x_1147 = lean_ptr_addr(x_1112);
x_1148 = lean_ptr_addr(x_1136);
x_1149 = lean_usize_dec_eq(x_1147, x_1148);
if (x_1149 == 0)
{
x_10 = x_1114;
x_11 = lean_box(0);
x_12 = x_1136;
x_13 = x_1149;
goto block_17;
}
else
{
size_t x_1150; size_t x_1151; uint8_t x_1152; 
x_1150 = lean_ptr_addr(x_1111);
x_1151 = lean_ptr_addr(x_1114);
x_1152 = lean_usize_dec_eq(x_1150, x_1151);
x_10 = x_1114;
x_11 = lean_box(0);
x_12 = x_1136;
x_13 = x_1152;
goto block_17;
}
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
lean_dec(x_1136);
lean_dec_ref(x_1114);
lean_dec_ref(x_1);
x_1153 = lean_ctor_get(x_1146, 0);
lean_inc(x_1153);
if (lean_is_exclusive(x_1146)) {
 lean_ctor_release(x_1146, 0);
 x_1154 = x_1146;
} else {
 lean_dec_ref(x_1146);
 x_1154 = lean_box(0);
}
if (lean_is_scalar(x_1154)) {
 x_1155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1155 = x_1154;
}
lean_ctor_set(x_1155, 0, x_1153);
return x_1155;
}
}
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
lean_dec(x_1136);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec_ref(x_1114);
lean_dec(x_1113);
lean_dec_ref(x_1);
x_1156 = lean_ctor_get(x_1137, 0);
lean_inc(x_1156);
if (lean_is_exclusive(x_1137)) {
 lean_ctor_release(x_1137, 0);
 x_1157 = x_1137;
} else {
 lean_dec_ref(x_1137);
 x_1157 = lean_box(0);
}
if (lean_is_scalar(x_1157)) {
 x_1158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1158 = x_1157;
}
lean_ctor_set(x_1158, 0, x_1156);
return x_1158;
}
}
else
{
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec_ref(x_1114);
lean_dec(x_1113);
lean_dec_ref(x_1);
return x_1135;
}
}
else
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
lean_inc_ref(x_1112);
lean_dec_ref(x_1);
x_1159 = lean_ctor_get(x_1134, 0);
lean_inc(x_1159);
lean_dec_ref(x_1134);
x_1160 = lean_ctor_get(x_1159, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1159, 1);
lean_inc(x_1161);
lean_dec(x_1159);
lean_inc(x_1127);
x_1162 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1127, x_1161, x_1119, x_1115, x_1121, x_1113);
if (lean_obj_tag(x_1162) == 0)
{
lean_object* x_1163; 
lean_dec_ref(x_1162);
x_1163 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1114, x_1119, x_1115);
lean_dec_ref(x_1114);
if (lean_obj_tag(x_1163) == 0)
{
lean_object* x_1164; 
lean_dec_ref(x_1163);
lean_inc(x_1113);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1117);
lean_inc_ref(x_1118);
lean_inc(x_1119);
lean_inc_ref(x_1120);
x_1164 = l_Lean_Compiler_LCNF_Simp_simp(x_1112, x_1120, x_1119, x_1118, x_1117, x_1115, x_1121, x_1113);
if (lean_obj_tag(x_1164) == 0)
{
lean_object* x_1165; lean_object* x_1166; 
x_1165 = lean_ctor_get(x_1164, 0);
lean_inc(x_1165);
lean_dec_ref(x_1164);
x_1166 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1160, x_1165, x_1120, x_1119, x_1118, x_1117, x_1115, x_1121, x_1113);
lean_dec(x_1113);
lean_dec_ref(x_1121);
lean_dec(x_1115);
lean_dec_ref(x_1117);
lean_dec_ref(x_1118);
lean_dec(x_1119);
lean_dec_ref(x_1120);
lean_dec(x_1160);
return x_1166;
}
else
{
lean_dec(x_1160);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec(x_1113);
return x_1164;
}
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; 
lean_dec(x_1160);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec(x_1113);
lean_dec_ref(x_1112);
x_1167 = lean_ctor_get(x_1163, 0);
lean_inc(x_1167);
if (lean_is_exclusive(x_1163)) {
 lean_ctor_release(x_1163, 0);
 x_1168 = x_1163;
} else {
 lean_dec_ref(x_1163);
 x_1168 = lean_box(0);
}
if (lean_is_scalar(x_1168)) {
 x_1169 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1169 = x_1168;
}
lean_ctor_set(x_1169, 0, x_1167);
return x_1169;
}
}
else
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
lean_dec(x_1160);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec_ref(x_1114);
lean_dec(x_1113);
lean_dec_ref(x_1112);
x_1170 = lean_ctor_get(x_1162, 0);
lean_inc(x_1170);
if (lean_is_exclusive(x_1162)) {
 lean_ctor_release(x_1162, 0);
 x_1171 = x_1162;
} else {
 lean_dec_ref(x_1162);
 x_1171 = lean_box(0);
}
if (lean_is_scalar(x_1171)) {
 x_1172 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1172 = x_1171;
}
lean_ctor_set(x_1172, 0, x_1170);
return x_1172;
}
}
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec_ref(x_1114);
lean_dec(x_1113);
lean_dec_ref(x_1);
x_1173 = lean_ctor_get(x_1133, 0);
lean_inc(x_1173);
if (lean_is_exclusive(x_1133)) {
 lean_ctor_release(x_1133, 0);
 x_1174 = x_1133;
} else {
 lean_dec_ref(x_1133);
 x_1174 = lean_box(0);
}
if (lean_is_scalar(x_1174)) {
 x_1175 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1175 = x_1174;
}
lean_ctor_set(x_1175, 0, x_1173);
return x_1175;
}
}
else
{
lean_object* x_1176; lean_object* x_1177; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1113);
lean_dec_ref(x_1);
x_1176 = lean_ctor_get(x_1132, 0);
lean_inc(x_1176);
lean_dec_ref(x_1132);
x_1177 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1114, x_1119, x_1115);
lean_dec(x_1115);
lean_dec(x_1119);
lean_dec_ref(x_1114);
if (lean_obj_tag(x_1177) == 0)
{
lean_object* x_1178; lean_object* x_1179; 
if (lean_is_exclusive(x_1177)) {
 lean_ctor_release(x_1177, 0);
 x_1178 = x_1177;
} else {
 lean_dec_ref(x_1177);
 x_1178 = lean_box(0);
}
if (lean_is_scalar(x_1178)) {
 x_1179 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1179 = x_1178;
}
lean_ctor_set(x_1179, 0, x_1176);
return x_1179;
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
lean_dec(x_1176);
x_1180 = lean_ctor_get(x_1177, 0);
lean_inc(x_1180);
if (lean_is_exclusive(x_1177)) {
 lean_ctor_release(x_1177, 0);
 x_1181 = x_1177;
} else {
 lean_dec_ref(x_1177);
 x_1181 = lean_box(0);
}
if (lean_is_scalar(x_1181)) {
 x_1182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1182 = x_1181;
}
lean_ctor_set(x_1182, 0, x_1180);
return x_1182;
}
}
}
else
{
lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec_ref(x_1114);
lean_dec(x_1113);
lean_dec_ref(x_1);
x_1183 = lean_ctor_get(x_1131, 0);
lean_inc(x_1183);
if (lean_is_exclusive(x_1131)) {
 lean_ctor_release(x_1131, 0);
 x_1184 = x_1131;
} else {
 lean_dec_ref(x_1131);
 x_1184 = lean_box(0);
}
if (lean_is_scalar(x_1184)) {
 x_1185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1185 = x_1184;
}
lean_ctor_set(x_1185, 0, x_1183);
return x_1185;
}
}
else
{
lean_object* x_1186; lean_object* x_1187; 
lean_inc_ref(x_1112);
lean_dec_ref(x_1);
x_1186 = lean_ctor_get(x_1130, 0);
lean_inc(x_1186);
lean_dec_ref(x_1130);
lean_inc(x_1127);
x_1187 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1127, x_1186, x_1119, x_1115, x_1121, x_1113);
if (lean_obj_tag(x_1187) == 0)
{
lean_object* x_1188; 
lean_dec_ref(x_1187);
x_1188 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1114, x_1119, x_1115);
lean_dec_ref(x_1114);
if (lean_obj_tag(x_1188) == 0)
{
lean_dec_ref(x_1188);
x_1 = x_1112;
x_2 = x_1120;
x_3 = x_1119;
x_4 = x_1118;
x_5 = x_1117;
x_6 = x_1115;
x_7 = x_1121;
x_8 = x_1113;
goto _start;
}
else
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec(x_1113);
lean_dec_ref(x_1112);
x_1190 = lean_ctor_get(x_1188, 0);
lean_inc(x_1190);
if (lean_is_exclusive(x_1188)) {
 lean_ctor_release(x_1188, 0);
 x_1191 = x_1188;
} else {
 lean_dec_ref(x_1188);
 x_1191 = lean_box(0);
}
if (lean_is_scalar(x_1191)) {
 x_1192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1192 = x_1191;
}
lean_ctor_set(x_1192, 0, x_1190);
return x_1192;
}
}
else
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec_ref(x_1114);
lean_dec(x_1113);
lean_dec_ref(x_1112);
x_1193 = lean_ctor_get(x_1187, 0);
lean_inc(x_1193);
if (lean_is_exclusive(x_1187)) {
 lean_ctor_release(x_1187, 0);
 x_1194 = x_1187;
} else {
 lean_dec_ref(x_1187);
 x_1194 = lean_box(0);
}
if (lean_is_scalar(x_1194)) {
 x_1195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1195 = x_1194;
}
lean_ctor_set(x_1195, 0, x_1193);
return x_1195;
}
}
}
else
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
lean_dec_ref(x_1114);
lean_inc_ref(x_1112);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1196 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1196 = lean_box(0);
}
x_1197 = lean_ctor_get(x_1126, 0);
lean_inc(x_1197);
lean_dec_ref(x_1126);
if (lean_is_scalar(x_1196)) {
 x_1198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1198 = x_1196;
 lean_ctor_set_tag(x_1198, 1);
}
lean_ctor_set(x_1198, 0, x_1197);
lean_ctor_set(x_1198, 1, x_1112);
x_1 = x_1198;
x_2 = x_1120;
x_3 = x_1119;
x_4 = x_1118;
x_5 = x_1117;
x_6 = x_1115;
x_7 = x_1121;
x_8 = x_1113;
goto _start;
}
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec_ref(x_1114);
lean_dec(x_1113);
lean_dec_ref(x_1);
x_1200 = lean_ctor_get(x_1125, 0);
lean_inc(x_1200);
if (lean_is_exclusive(x_1125)) {
 lean_ctor_release(x_1125, 0);
 x_1201 = x_1125;
} else {
 lean_dec_ref(x_1125);
 x_1201 = lean_box(0);
}
if (lean_is_scalar(x_1201)) {
 x_1202 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1202 = x_1201;
}
lean_ctor_set(x_1202, 0, x_1200);
return x_1202;
}
}
else
{
lean_object* x_1203; lean_object* x_1204; 
lean_dec_ref(x_1114);
lean_inc_ref(x_1112);
lean_dec_ref(x_1);
x_1203 = lean_ctor_get(x_1124, 0);
lean_inc(x_1203);
lean_dec_ref(x_1124);
x_1204 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1119);
if (lean_obj_tag(x_1204) == 0)
{
lean_object* x_1205; 
lean_dec_ref(x_1204);
lean_inc(x_1113);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1117);
lean_inc_ref(x_1118);
lean_inc(x_1119);
lean_inc_ref(x_1120);
x_1205 = l_Lean_Compiler_LCNF_Simp_simp(x_1112, x_1120, x_1119, x_1118, x_1117, x_1115, x_1121, x_1113);
if (lean_obj_tag(x_1205) == 0)
{
lean_object* x_1206; lean_object* x_1207; 
x_1206 = lean_ctor_get(x_1205, 0);
lean_inc(x_1206);
lean_dec_ref(x_1205);
x_1207 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1203, x_1206, x_1120, x_1119, x_1118, x_1117, x_1115, x_1121, x_1113);
lean_dec(x_1113);
lean_dec_ref(x_1121);
lean_dec(x_1115);
lean_dec_ref(x_1117);
lean_dec_ref(x_1118);
lean_dec(x_1119);
lean_dec_ref(x_1120);
lean_dec(x_1203);
return x_1207;
}
else
{
lean_dec(x_1203);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec(x_1113);
return x_1205;
}
}
else
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; 
lean_dec(x_1203);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec(x_1113);
lean_dec_ref(x_1112);
x_1208 = lean_ctor_get(x_1204, 0);
lean_inc(x_1208);
if (lean_is_exclusive(x_1204)) {
 lean_ctor_release(x_1204, 0);
 x_1209 = x_1204;
} else {
 lean_dec_ref(x_1204);
 x_1209 = lean_box(0);
}
if (lean_is_scalar(x_1209)) {
 x_1210 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1210 = x_1209;
}
lean_ctor_set(x_1210, 0, x_1208);
return x_1210;
}
}
}
else
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec_ref(x_1114);
lean_dec(x_1113);
lean_dec_ref(x_1);
x_1211 = lean_ctor_get(x_1123, 0);
lean_inc(x_1211);
if (lean_is_exclusive(x_1123)) {
 lean_ctor_release(x_1123, 0);
 x_1212 = x_1123;
} else {
 lean_dec_ref(x_1123);
 x_1212 = lean_box(0);
}
if (lean_is_scalar(x_1212)) {
 x_1213 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1213 = x_1212;
}
lean_ctor_set(x_1213, 0, x_1211);
return x_1213;
}
}
else
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; uint8_t x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; 
lean_inc_ref(x_1112);
lean_dec_ref(x_1);
x_1214 = lean_st_ref_take(x_1119);
x_1215 = lean_ctor_get(x_1114, 0);
x_1216 = lean_ctor_get(x_1214, 0);
lean_inc_ref(x_1216);
x_1217 = lean_ctor_get(x_1214, 1);
lean_inc_ref(x_1217);
x_1218 = lean_ctor_get(x_1214, 2);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1214, 3);
lean_inc_ref(x_1219);
x_1220 = lean_ctor_get_uint8(x_1214, sizeof(void*)*7);
x_1221 = lean_ctor_get(x_1214, 4);
lean_inc(x_1221);
x_1222 = lean_ctor_get(x_1214, 5);
lean_inc(x_1222);
x_1223 = lean_ctor_get(x_1214, 6);
lean_inc(x_1223);
if (lean_is_exclusive(x_1214)) {
 lean_ctor_release(x_1214, 0);
 lean_ctor_release(x_1214, 1);
 lean_ctor_release(x_1214, 2);
 lean_ctor_release(x_1214, 3);
 lean_ctor_release(x_1214, 4);
 lean_ctor_release(x_1214, 5);
 lean_ctor_release(x_1214, 6);
 x_1224 = x_1214;
} else {
 lean_dec_ref(x_1214);
 x_1224 = lean_box(0);
}
x_1225 = lean_box(0);
lean_inc(x_1215);
x_1226 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1216, x_1215, x_1225);
if (lean_is_scalar(x_1224)) {
 x_1227 = lean_alloc_ctor(0, 7, 1);
} else {
 x_1227 = x_1224;
}
lean_ctor_set(x_1227, 0, x_1226);
lean_ctor_set(x_1227, 1, x_1217);
lean_ctor_set(x_1227, 2, x_1218);
lean_ctor_set(x_1227, 3, x_1219);
lean_ctor_set(x_1227, 4, x_1221);
lean_ctor_set(x_1227, 5, x_1222);
lean_ctor_set(x_1227, 6, x_1223);
lean_ctor_set_uint8(x_1227, sizeof(void*)*7, x_1220);
x_1228 = lean_st_ref_set(x_1119, x_1227);
x_1229 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1114, x_1119, x_1115);
lean_dec_ref(x_1114);
if (lean_obj_tag(x_1229) == 0)
{
lean_dec_ref(x_1229);
x_1 = x_1112;
x_2 = x_1120;
x_3 = x_1119;
x_4 = x_1118;
x_5 = x_1117;
x_6 = x_1115;
x_7 = x_1121;
x_8 = x_1113;
goto _start;
}
else
{
lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec_ref(x_1117);
lean_dec(x_1115);
lean_dec(x_1113);
lean_dec_ref(x_1112);
x_1231 = lean_ctor_get(x_1229, 0);
lean_inc(x_1231);
if (lean_is_exclusive(x_1229)) {
 lean_ctor_release(x_1229, 0);
 x_1232 = x_1229;
} else {
 lean_dec_ref(x_1229);
 x_1232 = lean_box(0);
}
if (lean_is_scalar(x_1232)) {
 x_1233 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1233 = x_1232;
}
lean_ctor_set(x_1233, 0, x_1231);
return x_1233;
}
}
}
block_1249:
{
uint8_t x_1246; 
x_1246 = l_Lean_Expr_isErased(x_1236);
lean_dec_ref(x_1236);
if (x_1246 == 0)
{
lean_dec(x_1237);
x_1113 = x_1244;
x_1114 = x_1235;
x_1115 = x_1242;
x_1116 = lean_box(0);
x_1117 = x_1241;
x_1118 = x_1240;
x_1119 = x_1239;
x_1120 = x_1238;
x_1121 = x_1243;
x_1122 = x_122;
goto block_1234;
}
else
{
lean_object* x_1247; uint8_t x_1248; 
x_1247 = lean_box(1);
x_1248 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_1237, x_1247);
lean_dec(x_1237);
if (x_1248 == 0)
{
x_1113 = x_1244;
x_1114 = x_1235;
x_1115 = x_1242;
x_1116 = lean_box(0);
x_1117 = x_1241;
x_1118 = x_1240;
x_1119 = x_1239;
x_1120 = x_1238;
x_1121 = x_1243;
x_1122 = x_1246;
goto block_1234;
}
else
{
x_1113 = x_1244;
x_1114 = x_1235;
x_1115 = x_1242;
x_1116 = lean_box(0);
x_1117 = x_1241;
x_1118 = x_1240;
x_1119 = x_1239;
x_1120 = x_1238;
x_1121 = x_1243;
x_1122 = x_122;
goto block_1234;
}
}
}
}
case 3:
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; 
lean_dec(x_1059);
x_1289 = lean_ctor_get(x_1, 0);
x_1290 = lean_ctor_get(x_1, 1);
x_1291 = lean_st_ref_get(x_3);
x_1292 = lean_ctor_get(x_1291, 0);
lean_inc_ref(x_1292);
lean_dec_ref(x_1291);
lean_inc(x_1289);
x_1293 = l_Lean_Compiler_LCNF_normFVarImp(x_1292, x_1289, x_122);
lean_dec_ref(x_1292);
if (lean_obj_tag(x_1293) == 0)
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; uint8_t x_1299; lean_object* x_1305; lean_object* x_1311; 
x_1294 = lean_ctor_get(x_1293, 0);
lean_inc(x_1294);
lean_dec_ref(x_1293);
lean_inc_ref(x_1290);
x_1295 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_122, x_1290, x_3);
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
if (lean_is_exclusive(x_1295)) {
 lean_ctor_release(x_1295, 0);
 x_1297 = x_1295;
} else {
 lean_dec_ref(x_1295);
 x_1297 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_1110);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1296);
x_1311 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1294, x_1296, x_2, x_3, x_4, x_5, x_6, x_1110, x_8);
if (lean_obj_tag(x_1311) == 0)
{
lean_object* x_1312; 
x_1312 = lean_ctor_get(x_1311, 0);
lean_inc(x_1312);
lean_dec_ref(x_1311);
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1313; 
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_1294);
x_1313 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1294, x_3);
if (lean_obj_tag(x_1313) == 0)
{
lean_object* x_1314; lean_object* x_1315; uint8_t x_1316; 
lean_dec_ref(x_1313);
x_1314 = lean_unsigned_to_nat(0u);
x_1315 = lean_array_get_size(x_1296);
x_1316 = lean_nat_dec_lt(x_1314, x_1315);
if (x_1316 == 0)
{
lean_dec(x_1315);
lean_dec(x_3);
x_1305 = lean_box(0);
goto block_1310;
}
else
{
uint8_t x_1317; 
x_1317 = lean_nat_dec_le(x_1315, x_1315);
if (x_1317 == 0)
{
lean_dec(x_1315);
lean_dec(x_3);
x_1305 = lean_box(0);
goto block_1310;
}
else
{
lean_object* x_1318; size_t x_1319; size_t x_1320; lean_object* x_1321; 
x_1318 = lean_box(0);
x_1319 = 0;
x_1320 = lean_usize_of_nat(x_1315);
lean_dec(x_1315);
x_1321 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1296, x_1319, x_1320, x_1318, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1321) == 0)
{
lean_dec_ref(x_1321);
x_1305 = lean_box(0);
goto block_1310;
}
else
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; 
lean_dec(x_1297);
lean_dec(x_1296);
lean_dec(x_1294);
lean_dec_ref(x_1);
x_1322 = lean_ctor_get(x_1321, 0);
lean_inc(x_1322);
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 x_1323 = x_1321;
} else {
 lean_dec_ref(x_1321);
 x_1323 = lean_box(0);
}
if (lean_is_scalar(x_1323)) {
 x_1324 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1324 = x_1323;
}
lean_ctor_set(x_1324, 0, x_1322);
return x_1324;
}
}
}
}
else
{
lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; 
lean_dec(x_1297);
lean_dec(x_1296);
lean_dec(x_1294);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1325 = lean_ctor_get(x_1313, 0);
lean_inc(x_1325);
if (lean_is_exclusive(x_1313)) {
 lean_ctor_release(x_1313, 0);
 x_1326 = x_1313;
} else {
 lean_dec_ref(x_1313);
 x_1326 = lean_box(0);
}
if (lean_is_scalar(x_1326)) {
 x_1327 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1327 = x_1326;
}
lean_ctor_set(x_1327, 0, x_1325);
return x_1327;
}
}
else
{
lean_object* x_1328; 
lean_dec(x_1297);
lean_dec(x_1296);
lean_dec(x_1294);
lean_dec_ref(x_1);
x_1328 = lean_ctor_get(x_1312, 0);
lean_inc(x_1328);
lean_dec_ref(x_1312);
x_1 = x_1328;
x_7 = x_1110;
goto _start;
}
}
else
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; 
lean_dec(x_1297);
lean_dec(x_1296);
lean_dec(x_1294);
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1330 = lean_ctor_get(x_1311, 0);
lean_inc(x_1330);
if (lean_is_exclusive(x_1311)) {
 lean_ctor_release(x_1311, 0);
 x_1331 = x_1311;
} else {
 lean_dec_ref(x_1311);
 x_1331 = lean_box(0);
}
if (lean_is_scalar(x_1331)) {
 x_1332 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1332 = x_1331;
}
lean_ctor_set(x_1332, 0, x_1330);
return x_1332;
}
block_1304:
{
if (x_1299 == 0)
{
lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1300 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1300 = lean_box(0);
}
if (lean_is_scalar(x_1300)) {
 x_1301 = lean_alloc_ctor(3, 2, 0);
} else {
 x_1301 = x_1300;
}
lean_ctor_set(x_1301, 0, x_1294);
lean_ctor_set(x_1301, 1, x_1296);
if (lean_is_scalar(x_1297)) {
 x_1302 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1302 = x_1297;
}
lean_ctor_set(x_1302, 0, x_1301);
return x_1302;
}
else
{
lean_object* x_1303; 
lean_dec(x_1296);
lean_dec(x_1294);
if (lean_is_scalar(x_1297)) {
 x_1303 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1303 = x_1297;
}
lean_ctor_set(x_1303, 0, x_1);
return x_1303;
}
}
block_1310:
{
uint8_t x_1306; 
x_1306 = l_Lean_instBEqFVarId_beq(x_1289, x_1294);
if (x_1306 == 0)
{
x_1298 = lean_box(0);
x_1299 = x_1306;
goto block_1304;
}
else
{
size_t x_1307; size_t x_1308; uint8_t x_1309; 
x_1307 = lean_ptr_addr(x_1290);
x_1308 = lean_ptr_addr(x_1296);
x_1309 = lean_usize_dec_eq(x_1307, x_1308);
x_1298 = lean_box(0);
x_1299 = x_1309;
goto block_1304;
}
}
}
else
{
lean_object* x_1333; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1333 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1110, x_8);
lean_dec(x_8);
lean_dec_ref(x_1110);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1333;
}
}
case 4:
{
lean_object* x_1334; lean_object* x_1335; 
lean_dec(x_1059);
x_1334 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1334);
lean_inc(x_8);
lean_inc_ref(x_1110);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1334);
x_1335 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1334, x_2, x_3, x_4, x_5, x_6, x_1110, x_8);
if (lean_obj_tag(x_1335) == 0)
{
lean_object* x_1336; lean_object* x_1337; 
x_1336 = lean_ctor_get(x_1335, 0);
lean_inc(x_1336);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 x_1337 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1337 = lean_box(0);
}
if (lean_obj_tag(x_1336) == 0)
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; 
x_1338 = lean_st_ref_get(x_3);
x_1339 = lean_ctor_get(x_1334, 0);
lean_inc(x_1339);
x_1340 = lean_ctor_get(x_1334, 1);
lean_inc_ref(x_1340);
x_1341 = lean_ctor_get(x_1334, 2);
lean_inc(x_1341);
x_1342 = lean_ctor_get(x_1334, 3);
lean_inc_ref(x_1342);
if (lean_is_exclusive(x_1334)) {
 lean_ctor_release(x_1334, 0);
 lean_ctor_release(x_1334, 1);
 lean_ctor_release(x_1334, 2);
 lean_ctor_release(x_1334, 3);
 x_1343 = x_1334;
} else {
 lean_dec_ref(x_1334);
 x_1343 = lean_box(0);
}
x_1344 = lean_ctor_get(x_1338, 0);
lean_inc_ref(x_1344);
lean_dec_ref(x_1338);
lean_inc(x_1341);
x_1345 = l_Lean_Compiler_LCNF_normFVarImp(x_1344, x_1341, x_122);
lean_dec_ref(x_1344);
if (lean_obj_tag(x_1345) == 0)
{
lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1346 = lean_ctor_get(x_1345, 0);
lean_inc(x_1346);
if (lean_is_exclusive(x_1345)) {
 lean_ctor_release(x_1345, 0);
 x_1347 = x_1345;
} else {
 lean_dec_ref(x_1345);
 x_1347 = lean_box(0);
}
x_1348 = lean_st_ref_get(x_3);
x_1349 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_1110);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1342);
lean_inc(x_1346);
x_1350 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_1346, x_122, x_1349, x_1342, x_2, x_3, x_4, x_5, x_6, x_1110, x_8);
if (lean_obj_tag(x_1350) == 0)
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; 
x_1351 = lean_ctor_get(x_1350, 0);
lean_inc(x_1351);
if (lean_is_exclusive(x_1350)) {
 lean_ctor_release(x_1350, 0);
 x_1352 = x_1350;
} else {
 lean_dec_ref(x_1350);
 x_1352 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_1353 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1351, x_2, x_3, x_4, x_5, x_6, x_1110, x_8);
if (lean_obj_tag(x_1353) == 0)
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1363; uint8_t x_1364; lean_object* x_1368; lean_object* x_1369; lean_object* x_1381; uint8_t x_1382; 
x_1354 = lean_ctor_get(x_1353, 0);
lean_inc(x_1354);
if (lean_is_exclusive(x_1353)) {
 lean_ctor_release(x_1353, 0);
 x_1355 = x_1353;
} else {
 lean_dec_ref(x_1353);
 x_1355 = lean_box(0);
}
x_1356 = lean_ctor_get(x_1348, 0);
lean_inc_ref(x_1356);
lean_dec_ref(x_1348);
lean_inc_ref(x_1340);
x_1357 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1356, x_122, x_1340);
lean_dec_ref(x_1356);
x_1381 = lean_array_get_size(x_1354);
x_1382 = lean_nat_dec_eq(x_1381, x_1108);
lean_dec(x_1381);
if (x_1382 == 0)
{
lean_dec(x_1337);
lean_dec(x_6);
x_1368 = x_3;
x_1369 = lean_box(0);
goto block_1380;
}
else
{
lean_object* x_1383; 
x_1383 = lean_array_fget_borrowed(x_1354, x_1349);
if (lean_obj_tag(x_1383) == 0)
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1394; lean_object* x_1395; uint8_t x_1406; lean_object* x_1407; uint8_t x_1409; 
lean_dec(x_1337);
x_1384 = lean_ctor_get(x_1383, 1);
x_1385 = lean_ctor_get(x_1383, 2);
x_1394 = lean_array_get_size(x_1384);
x_1409 = lean_nat_dec_lt(x_1349, x_1394);
if (x_1409 == 0)
{
x_1406 = x_122;
x_1407 = lean_box(0);
goto block_1408;
}
else
{
if (x_1409 == 0)
{
x_1406 = x_122;
x_1407 = lean_box(0);
goto block_1408;
}
else
{
size_t x_1410; size_t x_1411; lean_object* x_1412; 
x_1410 = 0;
x_1411 = lean_usize_of_nat(x_1394);
x_1412 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1384, x_1410, x_1411, x_3);
if (lean_obj_tag(x_1412) == 0)
{
lean_object* x_1413; uint8_t x_1414; 
x_1413 = lean_ctor_get(x_1412, 0);
lean_inc(x_1413);
lean_dec_ref(x_1412);
x_1414 = lean_unbox(x_1413);
lean_dec(x_1413);
x_1406 = x_1414;
x_1407 = lean_box(0);
goto block_1408;
}
else
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; 
lean_dec(x_1394);
lean_dec_ref(x_1357);
lean_dec(x_1355);
lean_dec(x_1354);
lean_dec(x_1352);
lean_dec(x_1347);
lean_dec(x_1346);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec_ref(x_1340);
lean_dec(x_1339);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1415 = lean_ctor_get(x_1412, 0);
lean_inc(x_1415);
if (lean_is_exclusive(x_1412)) {
 lean_ctor_release(x_1412, 0);
 x_1416 = x_1412;
} else {
 lean_dec_ref(x_1412);
 x_1416 = lean_box(0);
}
if (lean_is_scalar(x_1416)) {
 x_1417 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1417 = x_1416;
}
lean_ctor_set(x_1417, 0, x_1415);
return x_1417;
}
}
}
block_1393:
{
lean_object* x_1387; 
x_1387 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1387) == 0)
{
lean_object* x_1388; lean_object* x_1389; 
if (lean_is_exclusive(x_1387)) {
 lean_ctor_release(x_1387, 0);
 x_1388 = x_1387;
} else {
 lean_dec_ref(x_1387);
 x_1388 = lean_box(0);
}
if (lean_is_scalar(x_1388)) {
 x_1389 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1389 = x_1388;
}
lean_ctor_set(x_1389, 0, x_1385);
return x_1389;
}
else
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
lean_dec_ref(x_1385);
x_1390 = lean_ctor_get(x_1387, 0);
lean_inc(x_1390);
if (lean_is_exclusive(x_1387)) {
 lean_ctor_release(x_1387, 0);
 x_1391 = x_1387;
} else {
 lean_dec_ref(x_1387);
 x_1391 = lean_box(0);
}
if (lean_is_scalar(x_1391)) {
 x_1392 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1392 = x_1391;
}
lean_ctor_set(x_1392, 0, x_1390);
return x_1392;
}
}
block_1405:
{
uint8_t x_1396; 
x_1396 = lean_nat_dec_lt(x_1349, x_1394);
if (x_1396 == 0)
{
lean_dec(x_1394);
lean_dec_ref(x_1384);
lean_dec(x_6);
x_1386 = lean_box(0);
goto block_1393;
}
else
{
uint8_t x_1397; 
x_1397 = lean_nat_dec_le(x_1394, x_1394);
if (x_1397 == 0)
{
lean_dec(x_1394);
lean_dec_ref(x_1384);
lean_dec(x_6);
x_1386 = lean_box(0);
goto block_1393;
}
else
{
lean_object* x_1398; size_t x_1399; size_t x_1400; lean_object* x_1401; 
x_1398 = lean_box(0);
x_1399 = 0;
x_1400 = lean_usize_of_nat(x_1394);
lean_dec(x_1394);
x_1401 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1384, x_1399, x_1400, x_1398, x_6);
lean_dec(x_6);
lean_dec_ref(x_1384);
if (lean_obj_tag(x_1401) == 0)
{
lean_dec_ref(x_1401);
x_1386 = lean_box(0);
goto block_1393;
}
else
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; 
lean_dec_ref(x_1385);
lean_dec(x_3);
x_1402 = lean_ctor_get(x_1401, 0);
lean_inc(x_1402);
if (lean_is_exclusive(x_1401)) {
 lean_ctor_release(x_1401, 0);
 x_1403 = x_1401;
} else {
 lean_dec_ref(x_1401);
 x_1403 = lean_box(0);
}
if (lean_is_scalar(x_1403)) {
 x_1404 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1404 = x_1403;
}
lean_ctor_set(x_1404, 0, x_1402);
return x_1404;
}
}
}
}
block_1408:
{
if (x_1406 == 0)
{
lean_inc_ref(x_1385);
lean_inc_ref(x_1384);
lean_dec_ref(x_1357);
lean_dec(x_1355);
lean_dec(x_1354);
lean_dec(x_1352);
lean_dec(x_1347);
lean_dec(x_1346);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec_ref(x_1340);
lean_dec(x_1339);
lean_dec_ref(x_1);
x_1395 = lean_box(0);
goto block_1405;
}
else
{
if (x_122 == 0)
{
lean_dec(x_1394);
lean_dec(x_6);
x_1368 = x_3;
x_1369 = lean_box(0);
goto block_1380;
}
else
{
lean_inc_ref(x_1385);
lean_inc_ref(x_1384);
lean_dec_ref(x_1357);
lean_dec(x_1355);
lean_dec(x_1354);
lean_dec(x_1352);
lean_dec(x_1347);
lean_dec(x_1346);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec_ref(x_1340);
lean_dec(x_1339);
lean_dec_ref(x_1);
x_1395 = lean_box(0);
goto block_1405;
}
}
}
}
else
{
lean_object* x_1418; lean_object* x_1419; 
lean_inc_ref(x_1383);
lean_dec_ref(x_1357);
lean_dec(x_1355);
lean_dec(x_1354);
lean_dec(x_1352);
lean_dec(x_1347);
lean_dec(x_1346);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec_ref(x_1340);
lean_dec(x_1339);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1418 = lean_ctor_get(x_1383, 0);
lean_inc_ref(x_1418);
lean_dec_ref(x_1383);
if (lean_is_scalar(x_1337)) {
 x_1419 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1419 = x_1337;
}
lean_ctor_set(x_1419, 0, x_1418);
return x_1419;
}
}
block_1362:
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
if (lean_is_scalar(x_1343)) {
 x_1359 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1359 = x_1343;
}
lean_ctor_set(x_1359, 0, x_1339);
lean_ctor_set(x_1359, 1, x_1357);
lean_ctor_set(x_1359, 2, x_1346);
lean_ctor_set(x_1359, 3, x_1354);
if (lean_is_scalar(x_1347)) {
 x_1360 = lean_alloc_ctor(4, 1, 0);
} else {
 x_1360 = x_1347;
 lean_ctor_set_tag(x_1360, 4);
}
lean_ctor_set(x_1360, 0, x_1359);
if (lean_is_scalar(x_1355)) {
 x_1361 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1361 = x_1355;
}
lean_ctor_set(x_1361, 0, x_1360);
return x_1361;
}
block_1367:
{
if (x_1364 == 0)
{
lean_dec(x_1352);
lean_dec(x_1341);
lean_dec_ref(x_1);
x_1358 = lean_box(0);
goto block_1362;
}
else
{
uint8_t x_1365; 
x_1365 = l_Lean_instBEqFVarId_beq(x_1341, x_1346);
lean_dec(x_1341);
if (x_1365 == 0)
{
lean_dec(x_1352);
lean_dec_ref(x_1);
x_1358 = lean_box(0);
goto block_1362;
}
else
{
lean_object* x_1366; 
lean_dec_ref(x_1357);
lean_dec(x_1355);
lean_dec(x_1354);
lean_dec(x_1347);
lean_dec(x_1346);
lean_dec(x_1343);
lean_dec(x_1339);
if (lean_is_scalar(x_1352)) {
 x_1366 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1366 = x_1352;
}
lean_ctor_set(x_1366, 0, x_1);
return x_1366;
}
}
}
block_1380:
{
lean_object* x_1370; 
lean_inc(x_1346);
x_1370 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1346, x_1368);
lean_dec(x_1368);
if (lean_obj_tag(x_1370) == 0)
{
size_t x_1371; size_t x_1372; uint8_t x_1373; 
lean_dec_ref(x_1370);
x_1371 = lean_ptr_addr(x_1342);
lean_dec_ref(x_1342);
x_1372 = lean_ptr_addr(x_1354);
x_1373 = lean_usize_dec_eq(x_1371, x_1372);
if (x_1373 == 0)
{
lean_dec_ref(x_1340);
x_1363 = lean_box(0);
x_1364 = x_1373;
goto block_1367;
}
else
{
size_t x_1374; size_t x_1375; uint8_t x_1376; 
x_1374 = lean_ptr_addr(x_1340);
lean_dec_ref(x_1340);
x_1375 = lean_ptr_addr(x_1357);
x_1376 = lean_usize_dec_eq(x_1374, x_1375);
x_1363 = lean_box(0);
x_1364 = x_1376;
goto block_1367;
}
}
else
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
lean_dec_ref(x_1357);
lean_dec(x_1355);
lean_dec(x_1354);
lean_dec(x_1352);
lean_dec(x_1347);
lean_dec(x_1346);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec_ref(x_1340);
lean_dec(x_1339);
lean_dec_ref(x_1);
x_1377 = lean_ctor_get(x_1370, 0);
lean_inc(x_1377);
if (lean_is_exclusive(x_1370)) {
 lean_ctor_release(x_1370, 0);
 x_1378 = x_1370;
} else {
 lean_dec_ref(x_1370);
 x_1378 = lean_box(0);
}
if (lean_is_scalar(x_1378)) {
 x_1379 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1379 = x_1378;
}
lean_ctor_set(x_1379, 0, x_1377);
return x_1379;
}
}
}
else
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; 
lean_dec(x_1352);
lean_dec_ref(x_1348);
lean_dec(x_1347);
lean_dec(x_1346);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec_ref(x_1340);
lean_dec(x_1339);
lean_dec(x_1337);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1420 = lean_ctor_get(x_1353, 0);
lean_inc(x_1420);
if (lean_is_exclusive(x_1353)) {
 lean_ctor_release(x_1353, 0);
 x_1421 = x_1353;
} else {
 lean_dec_ref(x_1353);
 x_1421 = lean_box(0);
}
if (lean_is_scalar(x_1421)) {
 x_1422 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1422 = x_1421;
}
lean_ctor_set(x_1422, 0, x_1420);
return x_1422;
}
}
else
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; 
lean_dec_ref(x_1348);
lean_dec(x_1347);
lean_dec(x_1346);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec_ref(x_1340);
lean_dec(x_1339);
lean_dec(x_1337);
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1423 = lean_ctor_get(x_1350, 0);
lean_inc(x_1423);
if (lean_is_exclusive(x_1350)) {
 lean_ctor_release(x_1350, 0);
 x_1424 = x_1350;
} else {
 lean_dec_ref(x_1350);
 x_1424 = lean_box(0);
}
if (lean_is_scalar(x_1424)) {
 x_1425 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1425 = x_1424;
}
lean_ctor_set(x_1425, 0, x_1423);
return x_1425;
}
}
else
{
lean_object* x_1426; 
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec_ref(x_1340);
lean_dec(x_1339);
lean_dec(x_1337);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1426 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1110, x_8);
lean_dec(x_8);
lean_dec_ref(x_1110);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1426;
}
}
else
{
lean_object* x_1427; lean_object* x_1428; 
lean_dec_ref(x_1334);
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1427 = lean_ctor_get(x_1336, 0);
lean_inc(x_1427);
lean_dec_ref(x_1336);
if (lean_is_scalar(x_1337)) {
 x_1428 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1428 = x_1337;
}
lean_ctor_set(x_1428, 0, x_1427);
return x_1428;
}
}
else
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; 
lean_dec_ref(x_1334);
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1429 = lean_ctor_get(x_1335, 0);
lean_inc(x_1429);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 x_1430 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1430 = lean_box(0);
}
if (lean_is_scalar(x_1430)) {
 x_1431 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1431 = x_1430;
}
lean_ctor_set(x_1431, 0, x_1429);
return x_1431;
}
}
case 5:
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
lean_dec(x_1059);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1432 = lean_ctor_get(x_1, 0);
x_1433 = lean_st_ref_get(x_3);
x_1434 = lean_ctor_get(x_1433, 0);
lean_inc_ref(x_1434);
lean_dec_ref(x_1433);
lean_inc(x_1432);
x_1435 = l_Lean_Compiler_LCNF_normFVarImp(x_1434, x_1432, x_122);
lean_dec_ref(x_1434);
if (lean_obj_tag(x_1435) == 0)
{
lean_object* x_1436; lean_object* x_1437; 
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1436 = lean_ctor_get(x_1435, 0);
lean_inc(x_1436);
lean_dec_ref(x_1435);
lean_inc(x_1436);
x_1437 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1436, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1437) == 0)
{
lean_object* x_1438; uint8_t x_1439; 
if (lean_is_exclusive(x_1437)) {
 lean_ctor_release(x_1437, 0);
 x_1438 = x_1437;
} else {
 lean_dec_ref(x_1437);
 x_1438 = lean_box(0);
}
x_1439 = l_Lean_instBEqFVarId_beq(x_1432, x_1436);
if (x_1439 == 0)
{
lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1440 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1440 = lean_box(0);
}
if (lean_is_scalar(x_1440)) {
 x_1441 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1441 = x_1440;
}
lean_ctor_set(x_1441, 0, x_1436);
if (lean_is_scalar(x_1438)) {
 x_1442 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1442 = x_1438;
}
lean_ctor_set(x_1442, 0, x_1441);
return x_1442;
}
else
{
lean_object* x_1443; 
lean_dec(x_1436);
if (lean_is_scalar(x_1438)) {
 x_1443 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1443 = x_1438;
}
lean_ctor_set(x_1443, 0, x_1);
return x_1443;
}
}
else
{
lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; 
lean_dec(x_1436);
lean_dec_ref(x_1);
x_1444 = lean_ctor_get(x_1437, 0);
lean_inc(x_1444);
if (lean_is_exclusive(x_1437)) {
 lean_ctor_release(x_1437, 0);
 x_1445 = x_1437;
} else {
 lean_dec_ref(x_1437);
 x_1445 = lean_box(0);
}
if (lean_is_scalar(x_1445)) {
 x_1446 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1446 = x_1445;
}
lean_ctor_set(x_1446, 0, x_1444);
return x_1446;
}
}
else
{
lean_object* x_1447; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1447 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1110, x_8);
lean_dec(x_8);
lean_dec_ref(x_1110);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1447;
}
}
case 6:
{
lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; size_t x_1452; size_t x_1453; uint8_t x_1454; 
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1448 = lean_ctor_get(x_1, 0);
x_1449 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_1450 = lean_ctor_get(x_1449, 0);
lean_inc_ref(x_1450);
lean_dec_ref(x_1449);
lean_inc_ref(x_1448);
x_1451 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1450, x_122, x_1448);
lean_dec_ref(x_1450);
x_1452 = lean_ptr_addr(x_1448);
x_1453 = lean_ptr_addr(x_1451);
x_1454 = lean_usize_dec_eq(x_1452, x_1453);
if (x_1454 == 0)
{
lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1455 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1455 = lean_box(0);
}
if (lean_is_scalar(x_1455)) {
 x_1456 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1456 = x_1455;
}
lean_ctor_set(x_1456, 0, x_1451);
if (lean_is_scalar(x_1059)) {
 x_1457 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1457 = x_1059;
}
lean_ctor_set(x_1457, 0, x_1456);
return x_1457;
}
else
{
lean_object* x_1458; 
lean_dec_ref(x_1451);
if (lean_is_scalar(x_1059)) {
 x_1458 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1458 = x_1059;
}
lean_ctor_set(x_1458, 0, x_1);
return x_1458;
}
}
default: 
{
lean_object* x_1459; lean_object* x_1460; 
lean_dec(x_1059);
x_1459 = lean_ctor_get(x_1, 0);
x_1460 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1460);
lean_inc_ref(x_1459);
x_1060 = x_1459;
x_1061 = x_1460;
x_1062 = x_2;
x_1063 = x_3;
x_1064 = x_4;
x_1065 = x_5;
x_1066 = x_6;
x_1067 = x_1110;
x_1068 = x_8;
goto block_1107;
}
}
block_1107:
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
x_1069 = lean_ctor_get(x_1060, 0);
x_1070 = lean_ctor_get(x_1060, 2);
x_1071 = lean_ctor_get(x_1060, 3);
x_1072 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_1069, x_1063);
if (lean_obj_tag(x_1072) == 0)
{
lean_object* x_1073; uint8_t x_1074; 
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
lean_dec_ref(x_1072);
x_1074 = lean_unbox(x_1073);
if (x_1074 == 0)
{
uint8_t x_1075; 
x_1075 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
if (x_1075 == 0)
{
uint8_t x_1076; 
x_1076 = lean_unbox(x_1073);
lean_dec(x_1073);
x_89 = x_1076;
x_90 = x_1061;
x_91 = x_1060;
x_92 = x_1062;
x_93 = x_1063;
x_94 = x_1064;
x_95 = x_1065;
x_96 = x_1066;
x_97 = x_1067;
x_98 = x_1068;
x_99 = lean_box(0);
goto block_105;
}
else
{
uint8_t x_1077; 
lean_inc_ref(x_1071);
x_1077 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_1071, x_1070);
if (x_1077 == 0)
{
uint8_t x_1078; 
x_1078 = lean_unbox(x_1073);
lean_dec(x_1073);
x_89 = x_1078;
x_90 = x_1061;
x_91 = x_1060;
x_92 = x_1062;
x_93 = x_1063;
x_94 = x_1064;
x_95 = x_1065;
x_96 = x_1066;
x_97 = x_1067;
x_98 = x_1068;
x_99 = lean_box(0);
goto block_105;
}
else
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1079 = lean_st_ref_get(x_1063);
x_1080 = lean_ctor_get(x_1079, 0);
lean_inc_ref(x_1080);
lean_dec_ref(x_1079);
x_1081 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_1060, x_1080, x_1065, x_1066, x_1067, x_1068);
lean_dec_ref(x_1080);
if (lean_obj_tag(x_1081) == 0)
{
lean_object* x_1082; lean_object* x_1083; 
x_1082 = lean_ctor_get(x_1081, 0);
lean_inc(x_1082);
lean_dec_ref(x_1081);
lean_inc(x_1068);
lean_inc_ref(x_1067);
lean_inc(x_1066);
lean_inc_ref(x_1065);
x_1083 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_1082, x_1065, x_1066, x_1067, x_1068);
if (lean_obj_tag(x_1083) == 0)
{
lean_object* x_1084; lean_object* x_1085; 
x_1084 = lean_ctor_get(x_1083, 0);
lean_inc(x_1084);
lean_dec_ref(x_1083);
x_1085 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1063);
if (lean_obj_tag(x_1085) == 0)
{
uint8_t x_1086; 
lean_dec_ref(x_1085);
x_1086 = lean_unbox(x_1073);
lean_dec(x_1073);
x_89 = x_1086;
x_90 = x_1061;
x_91 = x_1084;
x_92 = x_1062;
x_93 = x_1063;
x_94 = x_1064;
x_95 = x_1065;
x_96 = x_1066;
x_97 = x_1067;
x_98 = x_1068;
x_99 = lean_box(0);
goto block_105;
}
else
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
lean_dec(x_1084);
lean_dec(x_1073);
lean_dec(x_1068);
lean_dec_ref(x_1067);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec_ref(x_1064);
lean_dec(x_1063);
lean_dec_ref(x_1062);
lean_dec_ref(x_1061);
lean_dec_ref(x_1);
x_1087 = lean_ctor_get(x_1085, 0);
lean_inc(x_1087);
if (lean_is_exclusive(x_1085)) {
 lean_ctor_release(x_1085, 0);
 x_1088 = x_1085;
} else {
 lean_dec_ref(x_1085);
 x_1088 = lean_box(0);
}
if (lean_is_scalar(x_1088)) {
 x_1089 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1089 = x_1088;
}
lean_ctor_set(x_1089, 0, x_1087);
return x_1089;
}
}
else
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
lean_dec(x_1073);
lean_dec(x_1068);
lean_dec_ref(x_1067);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec_ref(x_1064);
lean_dec(x_1063);
lean_dec_ref(x_1062);
lean_dec_ref(x_1061);
lean_dec_ref(x_1);
x_1090 = lean_ctor_get(x_1083, 0);
lean_inc(x_1090);
if (lean_is_exclusive(x_1083)) {
 lean_ctor_release(x_1083, 0);
 x_1091 = x_1083;
} else {
 lean_dec_ref(x_1083);
 x_1091 = lean_box(0);
}
if (lean_is_scalar(x_1091)) {
 x_1092 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1092 = x_1091;
}
lean_ctor_set(x_1092, 0, x_1090);
return x_1092;
}
}
else
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
lean_dec(x_1073);
lean_dec(x_1068);
lean_dec_ref(x_1067);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec_ref(x_1064);
lean_dec(x_1063);
lean_dec_ref(x_1062);
lean_dec_ref(x_1061);
lean_dec_ref(x_1);
x_1093 = lean_ctor_get(x_1081, 0);
lean_inc(x_1093);
if (lean_is_exclusive(x_1081)) {
 lean_ctor_release(x_1081, 0);
 x_1094 = x_1081;
} else {
 lean_dec_ref(x_1081);
 x_1094 = lean_box(0);
}
if (lean_is_scalar(x_1094)) {
 x_1095 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1095 = x_1094;
}
lean_ctor_set(x_1095, 0, x_1093);
return x_1095;
}
}
}
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1096 = lean_st_ref_get(x_1063);
x_1097 = lean_ctor_get(x_1096, 0);
lean_inc_ref(x_1097);
lean_dec_ref(x_1096);
x_1098 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_1060, x_1097, x_1065, x_1066, x_1067, x_1068);
lean_dec_ref(x_1097);
if (lean_obj_tag(x_1098) == 0)
{
lean_object* x_1099; uint8_t x_1100; 
x_1099 = lean_ctor_get(x_1098, 0);
lean_inc(x_1099);
lean_dec_ref(x_1098);
x_1100 = lean_unbox(x_1073);
lean_dec(x_1073);
x_57 = x_1100;
x_58 = x_1061;
x_59 = x_1099;
x_60 = x_1062;
x_61 = x_1063;
x_62 = x_1064;
x_63 = x_1065;
x_64 = x_1066;
x_65 = x_1067;
x_66 = x_1068;
x_67 = lean_box(0);
goto block_88;
}
else
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
lean_dec(x_1073);
lean_dec(x_1068);
lean_dec_ref(x_1067);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec_ref(x_1064);
lean_dec(x_1063);
lean_dec_ref(x_1062);
lean_dec_ref(x_1061);
lean_dec_ref(x_1);
x_1101 = lean_ctor_get(x_1098, 0);
lean_inc(x_1101);
if (lean_is_exclusive(x_1098)) {
 lean_ctor_release(x_1098, 0);
 x_1102 = x_1098;
} else {
 lean_dec_ref(x_1098);
 x_1102 = lean_box(0);
}
if (lean_is_scalar(x_1102)) {
 x_1103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1103 = x_1102;
}
lean_ctor_set(x_1103, 0, x_1101);
return x_1103;
}
}
}
else
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
lean_dec(x_1068);
lean_dec_ref(x_1067);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec_ref(x_1064);
lean_dec(x_1063);
lean_dec_ref(x_1062);
lean_dec_ref(x_1061);
lean_dec_ref(x_1060);
lean_dec_ref(x_1);
x_1104 = lean_ctor_get(x_1072, 0);
lean_inc(x_1104);
if (lean_is_exclusive(x_1072)) {
 lean_ctor_release(x_1072, 0);
 x_1105 = x_1072;
} else {
 lean_dec_ref(x_1072);
 x_1105 = lean_box(0);
}
if (lean_is_scalar(x_1105)) {
 x_1106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1106 = x_1105;
}
lean_ctor_set(x_1106, 0, x_1104);
return x_1106;
}
}
}
else
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
lean_dec_ref(x_121);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1461 = lean_ctor_get(x_1058, 0);
lean_inc(x_1461);
if (lean_is_exclusive(x_1058)) {
 lean_ctor_release(x_1058, 0);
 x_1462 = x_1058;
} else {
 lean_dec_ref(x_1058);
 x_1462 = lean_box(0);
}
if (lean_is_scalar(x_1462)) {
 x_1463 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1463 = x_1462;
}
lean_ctor_set(x_1463, 0, x_1461);
return x_1463;
}
}
}
else
{
lean_object* x_1464; 
lean_dec_ref(x_1);
x_1464 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1464;
}
block_17:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_12);
lean_dec_ref(x_10);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
}
block_25:
{
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_1);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_19);
lean_dec_ref(x_18);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
}
block_33:
{
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_1);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_1);
return x_32;
}
}
block_56:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ptr_addr(x_38);
x_40 = lean_ptr_addr(x_35);
x_41 = lean_usize_dec_eq(x_39, x_40);
if (x_41 == 0)
{
x_18 = x_34;
x_19 = x_35;
x_20 = lean_box(0);
x_21 = x_41;
goto block_25;
}
else
{
size_t x_42; size_t x_43; uint8_t x_44; 
x_42 = lean_ptr_addr(x_37);
x_43 = lean_ptr_addr(x_34);
x_44 = lean_usize_dec_eq(x_42, x_43);
x_18 = x_34;
x_19 = x_35;
x_20 = lean_box(0);
x_21 = x_44;
goto block_25;
}
}
case 2:
{
lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
x_47 = lean_ptr_addr(x_46);
x_48 = lean_ptr_addr(x_35);
x_49 = lean_usize_dec_eq(x_47, x_48);
if (x_49 == 0)
{
x_26 = x_34;
x_27 = x_35;
x_28 = lean_box(0);
x_29 = x_49;
goto block_33;
}
else
{
size_t x_50; size_t x_51; uint8_t x_52; 
x_50 = lean_ptr_addr(x_45);
x_51 = lean_ptr_addr(x_34);
x_52 = lean_usize_dec_eq(x_50, x_51);
x_26 = x_34;
x_27 = x_35;
x_28 = lean_box(0);
x_29 = x_52;
goto block_33;
}
}
default: 
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_1);
x_53 = l_Lean_Compiler_LCNF_Simp_simp___closed__3;
x_54 = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0(x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
block_88:
{
lean_object* x_68; 
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc_ref(x_62);
lean_inc(x_61);
lean_inc_ref(x_60);
x_68 = l_Lean_Compiler_LCNF_Simp_simp(x_58, x_60, x_61, x_62, x_63, x_64, x_65, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = lean_ctor_get(x_59, 0);
x_71 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_70, x_61);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_1);
x_74 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(x_59, x_61, x_64);
lean_dec(x_64);
lean_dec(x_61);
lean_dec_ref(x_59);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_69);
return x_74;
}
else
{
lean_object* x_77; 
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_69);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_69);
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
return x_74;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec(x_74);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
if (x_57 == 0)
{
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
x_34 = x_59;
x_35 = x_69;
x_36 = lean_box(0);
goto block_56;
}
else
{
lean_object* x_81; 
lean_inc_ref(x_59);
x_81 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_59, x_60, x_61, x_62, x_63, x_64, x_65, x_66);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_34 = x_59;
x_35 = x_69;
x_36 = lean_box(0);
goto block_56;
}
else
{
uint8_t x_82; 
lean_dec(x_69);
lean_dec_ref(x_59);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_69);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_1);
x_85 = !lean_is_exclusive(x_71);
if (x_85 == 0)
{
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_71, 0);
lean_inc(x_86);
lean_dec(x_71);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_1);
return x_68;
}
}
block_105:
{
lean_object* x_100; 
lean_inc(x_98);
lean_inc_ref(x_97);
lean_inc(x_96);
lean_inc_ref(x_95);
lean_inc_ref(x_94);
lean_inc(x_93);
lean_inc_ref(x_92);
x_100 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_91, x_92, x_93, x_94, x_95, x_96, x_97, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_57 = x_89;
x_58 = x_90;
x_59 = x_101;
x_60 = x_92;
x_61 = x_93;
x_62 = x_94;
x_63 = x_95;
x_64 = x_96;
x_65 = x_97;
x_66 = x_98;
x_67 = lean_box(0);
goto block_88;
}
else
{
uint8_t x_102; 
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_90);
lean_dec_ref(x_1);
x_102 = !lean_is_exclusive(x_100);
if (x_102 == 0)
{
return x_100;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
uint8_t x_14; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_4, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = lean_st_ref_take(x_5);
x_19 = lean_array_uget(x_1, x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_23);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_22, x_20, x_23);
lean_ctor_set(x_18, 0, x_24);
x_25 = lean_st_ref_set(x_5, x_18);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_10, x_26);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_27);
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_3 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
x_33 = lean_ctor_get(x_18, 2);
x_34 = lean_ctor_get(x_18, 3);
x_35 = lean_ctor_get_uint8(x_18, sizeof(void*)*7);
x_36 = lean_ctor_get(x_18, 4);
x_37 = lean_ctor_get(x_18, 5);
x_38 = lean_ctor_get(x_18, 6);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_39 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_39);
x_40 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_31, x_20, x_39);
x_41 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_33);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_36);
lean_ctor_set(x_41, 5, x_37);
lean_ctor_set(x_41, 6, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*7, x_35);
x_42 = lean_st_ref_set(x_5, x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_10, x_43);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_44);
x_45 = 1;
x_46 = lean_usize_add(x_3, x_45);
x_3 = x_46;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; 
lean_dec(x_4);
x_48 = lean_st_ref_take(x_5);
x_49 = lean_array_uget(x_1, x_3);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_48, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_54);
x_55 = lean_ctor_get_uint8(x_48, sizeof(void*)*7);
x_56 = lean_ctor_get(x_48, 4);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_48, 6);
lean_inc(x_58);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 lean_ctor_release(x_48, 5);
 lean_ctor_release(x_48, 6);
 x_59 = x_48;
} else {
 lean_dec_ref(x_48);
 x_59 = lean_box(0);
}
x_60 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_60);
x_61 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_51, x_50, x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 7, 1);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_52);
lean_ctor_set(x_62, 2, x_53);
lean_ctor_set(x_62, 3, x_54);
lean_ctor_set(x_62, 4, x_56);
lean_ctor_set(x_62, 5, x_57);
lean_ctor_set(x_62, 6, x_58);
lean_ctor_set_uint8(x_62, sizeof(void*)*7, x_55);
x_63 = lean_st_ref_set(x_5, x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_10, x_64);
lean_dec(x_10);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_9);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_11);
x_67 = 1;
x_68 = lean_usize_add(x_3, x_67);
x_3 = x_68;
x_4 = x_66;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_13;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedParam_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_st_ref_get(x_3);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_10);
x_13 = 0;
lean_inc(x_11);
x_14 = l_Lean_Compiler_LCNF_normFVarImp(x_12, x_11, x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_16, x_4, x_6, x_8);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_free_object(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_free_object(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_21);
x_24 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_ctor_set_tag(x_14, 4);
lean_ctor_set(x_14, 0, x_27);
x_28 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_14, x_6);
lean_dec_ref(x_14);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec_ref(x_28);
x_29 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_dec_ref(x_29);
if (lean_obj_tag(x_26) == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_free_object(x_24);
x_30 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_26, 2);
lean_inc_ref(x_31);
lean_dec_ref(x_26);
x_32 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_21);
x_55 = lean_ctor_get(x_32, 3);
lean_inc(x_55);
lean_dec_ref(x_32);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_array_get_size(x_33);
x_58 = lean_nat_dec_le(x_55, x_56);
if (x_58 == 0)
{
x_34 = x_55;
x_35 = x_57;
goto block_54;
}
else
{
lean_dec(x_55);
x_34 = x_56;
x_35 = x_57;
goto block_54;
}
block_54:
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Array_toSubarray___redArg(x_33, x_34, x_35);
x_37 = lean_array_size(x_30);
x_38 = 0;
x_39 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_30, x_37, x_38, x_36, x_3);
lean_dec_ref(x_39);
lean_inc(x_6);
x_40 = l_Lean_Compiler_LCNF_Simp_simp(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_30, x_6);
lean_dec(x_6);
lean_dec_ref(x_30);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
if (lean_is_scalar(x_22)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_22;
}
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
if (lean_is_scalar(x_22)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_22;
}
lean_ctor_set(x_46, 0, x_41);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_41);
lean_dec(x_22);
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec_ref(x_30);
lean_dec(x_22);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_40, 0);
lean_inc(x_52);
lean_dec(x_40);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_26, 2);
lean_inc_ref(x_60);
lean_dec_ref(x_26);
x_61 = !lean_is_exclusive(x_21);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_21, 0);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_nat_dec_eq(x_62, x_63);
if (x_64 == 1)
{
lean_object* x_65; 
lean_free_object(x_21);
lean_dec(x_62);
lean_dec_ref(x_59);
lean_free_object(x_24);
x_65 = l_Lean_Compiler_LCNF_Simp_simp(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
if (lean_is_scalar(x_22)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_22;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_65, 0, x_68);
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
lean_dec(x_65);
if (lean_is_scalar(x_22)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_22;
}
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_22);
x_72 = !lean_is_exclusive(x_65);
if (x_72 == 0)
{
return x_65;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
lean_dec(x_65);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_62, x_75);
lean_dec(x_62);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_76);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_21);
x_78 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_79 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_77, x_78, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_82 = lean_array_get_borrowed(x_81, x_59, x_63);
x_83 = lean_ctor_get(x_82, 0);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_inc(x_83);
x_85 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_83, x_84, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
lean_dec_ref(x_85);
lean_inc(x_6);
x_86 = l_Lean_Compiler_LCNF_Simp_simp(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_59, x_6);
lean_dec(x_6);
lean_dec_ref(x_59);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
lean_dec(x_90);
lean_ctor_set(x_24, 1, x_87);
lean_ctor_set(x_24, 0, x_80);
if (lean_is_scalar(x_22)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_22;
}
lean_ctor_set(x_91, 0, x_24);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_88);
lean_ctor_set(x_24, 1, x_87);
lean_ctor_set(x_24, 0, x_80);
if (lean_is_scalar(x_22)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_22;
}
lean_ctor_set(x_92, 0, x_24);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_87);
lean_dec(x_80);
lean_free_object(x_24);
lean_dec(x_22);
x_94 = !lean_is_exclusive(x_88);
if (x_94 == 0)
{
return x_88;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_88, 0);
lean_inc(x_95);
lean_dec(x_88);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_80);
lean_dec_ref(x_59);
lean_free_object(x_24);
lean_dec(x_22);
lean_dec(x_6);
x_97 = !lean_is_exclusive(x_86);
if (x_97 == 0)
{
return x_86;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_86, 0);
lean_inc(x_98);
lean_dec(x_86);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_80);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_free_object(x_24);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_100 = !lean_is_exclusive(x_85);
if (x_100 == 0)
{
return x_85;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_85, 0);
lean_inc(x_101);
lean_dec(x_85);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_free_object(x_24);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_103 = !lean_is_exclusive(x_79);
if (x_103 == 0)
{
return x_79;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
lean_dec(x_79);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_21, 0);
lean_inc(x_106);
lean_dec(x_21);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_eq(x_106, x_107);
if (x_108 == 1)
{
lean_object* x_109; 
lean_dec(x_106);
lean_dec_ref(x_59);
lean_free_object(x_24);
x_109 = l_Lean_Compiler_LCNF_Simp_simp(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_22;
}
lean_ctor_set(x_112, 0, x_110);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 1, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_22);
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_115 = x_109;
} else {
 lean_dec_ref(x_109);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_sub(x_106, x_117);
lean_dec(x_106);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_122 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_120, x_121, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_125 = lean_array_get_borrowed(x_124, x_59, x_107);
x_126 = lean_ctor_get(x_125, 0);
x_127 = lean_ctor_get(x_123, 0);
lean_inc(x_127);
lean_inc(x_126);
x_128 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_126, x_127, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
lean_dec_ref(x_128);
lean_inc(x_6);
x_129 = l_Lean_Compiler_LCNF_Simp_simp(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_59, x_6);
lean_dec(x_6);
lean_dec_ref(x_59);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_132 = x_131;
} else {
 lean_dec_ref(x_131);
 x_132 = lean_box(0);
}
lean_ctor_set(x_24, 1, x_130);
lean_ctor_set(x_24, 0, x_123);
if (lean_is_scalar(x_22)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_22;
}
lean_ctor_set(x_133, 0, x_24);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 1, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_130);
lean_dec(x_123);
lean_free_object(x_24);
lean_dec(x_22);
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_136 = x_131;
} else {
 lean_dec_ref(x_131);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_123);
lean_dec_ref(x_59);
lean_free_object(x_24);
lean_dec(x_22);
lean_dec(x_6);
x_138 = lean_ctor_get(x_129, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_139 = x_129;
} else {
 lean_dec_ref(x_129);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_123);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_free_object(x_24);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_141 = lean_ctor_get(x_128, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_142 = x_128;
} else {
 lean_dec_ref(x_128);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 1, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_141);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_free_object(x_24);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_144 = lean_ctor_get(x_122, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_145 = x_122;
} else {
 lean_dec_ref(x_122);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_144);
return x_146;
}
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_free_object(x_24);
lean_dec(x_21);
x_147 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_147);
lean_dec_ref(x_26);
x_148 = l_Lean_Compiler_LCNF_Simp_simp(x_147, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 0);
if (lean_is_scalar(x_22)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_22;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_148, 0, x_151);
return x_148;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_148, 0);
lean_inc(x_152);
lean_dec(x_148);
if (lean_is_scalar(x_22)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_22;
}
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
else
{
uint8_t x_155; 
lean_dec(x_22);
x_155 = !lean_is_exclusive(x_148);
if (x_155 == 0)
{
return x_148;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_148, 0);
lean_inc(x_156);
lean_dec(x_148);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
}
}
else
{
uint8_t x_158; 
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_158 = !lean_is_exclusive(x_29);
if (x_158 == 0)
{
return x_29;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_29, 0);
lean_inc(x_159);
lean_dec(x_29);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_161 = !lean_is_exclusive(x_28);
if (x_161 == 0)
{
return x_28;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_28, 0);
lean_inc(x_162);
lean_dec(x_28);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_24, 0);
x_165 = lean_ctor_get(x_24, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_24);
lean_ctor_set_tag(x_14, 4);
lean_ctor_set(x_14, 0, x_165);
x_166 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_14, x_6);
lean_dec_ref(x_14);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
lean_dec_ref(x_166);
x_167 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_167) == 0)
{
lean_dec_ref(x_167);
if (lean_obj_tag(x_164) == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_168 = lean_ctor_get(x_164, 1);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_164, 2);
lean_inc_ref(x_169);
lean_dec_ref(x_164);
x_170 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_171);
lean_dec_ref(x_21);
x_191 = lean_ctor_get(x_170, 3);
lean_inc(x_191);
lean_dec_ref(x_170);
x_192 = lean_unsigned_to_nat(0u);
x_193 = lean_array_get_size(x_171);
x_194 = lean_nat_dec_le(x_191, x_192);
if (x_194 == 0)
{
x_172 = x_191;
x_173 = x_193;
goto block_190;
}
else
{
lean_dec(x_191);
x_172 = x_192;
x_173 = x_193;
goto block_190;
}
block_190:
{
lean_object* x_174; size_t x_175; size_t x_176; lean_object* x_177; lean_object* x_178; 
x_174 = l_Array_toSubarray___redArg(x_171, x_172, x_173);
x_175 = lean_array_size(x_168);
x_176 = 0;
x_177 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_168, x_175, x_176, x_174, x_3);
lean_dec_ref(x_177);
lean_inc(x_6);
x_178 = l_Lean_Compiler_LCNF_Simp_simp(x_169, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec_ref(x_178);
x_180 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_168, x_6);
lean_dec(x_6);
lean_dec_ref(x_168);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_181 = x_180;
} else {
 lean_dec_ref(x_180);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_22;
}
lean_ctor_set(x_182, 0, x_179);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 1, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_179);
lean_dec(x_22);
x_184 = lean_ctor_get(x_180, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_185 = x_180;
} else {
 lean_dec_ref(x_180);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec_ref(x_168);
lean_dec(x_22);
lean_dec(x_6);
x_187 = lean_ctor_get(x_178, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_188 = x_178;
} else {
 lean_dec_ref(x_178);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_195 = lean_ctor_get(x_164, 1);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_164, 2);
lean_inc_ref(x_196);
lean_dec_ref(x_164);
x_197 = lean_ctor_get(x_21, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_198 = x_21;
} else {
 lean_dec_ref(x_21);
 x_198 = lean_box(0);
}
x_199 = lean_unsigned_to_nat(0u);
x_200 = lean_nat_dec_eq(x_197, x_199);
if (x_200 == 1)
{
lean_object* x_201; 
lean_dec(x_198);
lean_dec(x_197);
lean_dec_ref(x_195);
x_201 = l_Lean_Compiler_LCNF_Simp_simp(x_196, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_22;
}
lean_ctor_set(x_204, 0, x_202);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 1, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_22);
x_206 = lean_ctor_get(x_201, 0);
lean_inc(x_206);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_207 = x_201;
} else {
 lean_dec_ref(x_201);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 1, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_sub(x_197, x_209);
lean_dec(x_197);
if (lean_is_scalar(x_198)) {
 x_211 = lean_alloc_ctor(0, 1, 0);
} else {
 x_211 = x_198;
 lean_ctor_set_tag(x_211, 0);
}
lean_ctor_set(x_211, 0, x_210);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_213 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_214 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_212, x_213, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
lean_dec_ref(x_214);
x_216 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_217 = lean_array_get_borrowed(x_216, x_195, x_199);
x_218 = lean_ctor_get(x_217, 0);
x_219 = lean_ctor_get(x_215, 0);
lean_inc(x_219);
lean_inc(x_218);
x_220 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_218, x_219, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
lean_dec_ref(x_220);
lean_inc(x_6);
x_221 = l_Lean_Compiler_LCNF_Simp_simp(x_196, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
x_223 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_195, x_6);
lean_dec(x_6);
lean_dec_ref(x_195);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_224 = x_223;
} else {
 lean_dec_ref(x_223);
 x_224 = lean_box(0);
}
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_215);
lean_ctor_set(x_225, 1, x_222);
if (lean_is_scalar(x_22)) {
 x_226 = lean_alloc_ctor(1, 1, 0);
} else {
 x_226 = x_22;
}
lean_ctor_set(x_226, 0, x_225);
if (lean_is_scalar(x_224)) {
 x_227 = lean_alloc_ctor(0, 1, 0);
} else {
 x_227 = x_224;
}
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_222);
lean_dec(x_215);
lean_dec(x_22);
x_228 = lean_ctor_get(x_223, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_229 = x_223;
} else {
 lean_dec_ref(x_223);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_215);
lean_dec_ref(x_195);
lean_dec(x_22);
lean_dec(x_6);
x_231 = lean_ctor_get(x_221, 0);
lean_inc(x_231);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_232 = x_221;
} else {
 lean_dec_ref(x_221);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 1, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_215);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_234 = lean_ctor_get(x_220, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_235 = x_220;
} else {
 lean_dec_ref(x_220);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 1, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_234);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_237 = lean_ctor_get(x_214, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_238 = x_214;
} else {
 lean_dec_ref(x_214);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 1, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_237);
return x_239;
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_21);
x_240 = lean_ctor_get(x_164, 0);
lean_inc_ref(x_240);
lean_dec_ref(x_164);
x_241 = l_Lean_Compiler_LCNF_Simp_simp(x_240, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 x_243 = x_241;
} else {
 lean_dec_ref(x_241);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_244 = x_22;
}
lean_ctor_set(x_244, 0, x_242);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 1, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_22);
x_246 = lean_ctor_get(x_241, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 x_247 = x_241;
} else {
 lean_dec_ref(x_241);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 1, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_246);
return x_248;
}
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_164);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_249 = lean_ctor_get(x_167, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_250 = x_167;
} else {
 lean_dec_ref(x_167);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_249);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_164);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_252 = lean_ctor_get(x_166, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_253 = x_166;
} else {
 lean_dec_ref(x_166);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_252);
return x_254;
}
}
}
}
else
{
lean_object* x_255; 
x_255 = lean_ctor_get(x_17, 0);
lean_inc(x_255);
lean_dec(x_17);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; 
lean_free_object(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_256 = lean_box(0);
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_258 = lean_ctor_get(x_255, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_259 = x_255;
} else {
 lean_dec_ref(x_255);
 x_259 = lean_box(0);
}
x_260 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_258);
x_261 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_260);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_264 = x_261;
} else {
 lean_dec_ref(x_261);
 x_264 = lean_box(0);
}
lean_ctor_set_tag(x_14, 4);
lean_ctor_set(x_14, 0, x_263);
x_265 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_14, x_6);
lean_dec_ref(x_14);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; 
lean_dec_ref(x_265);
x_266 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_266) == 0)
{
lean_dec_ref(x_266);
if (lean_obj_tag(x_262) == 0)
{
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
lean_dec(x_264);
x_267 = lean_ctor_get(x_262, 1);
lean_inc_ref(x_267);
x_268 = lean_ctor_get(x_262, 2);
lean_inc_ref(x_268);
lean_dec_ref(x_262);
x_269 = lean_ctor_get(x_258, 0);
lean_inc_ref(x_269);
x_270 = lean_ctor_get(x_258, 1);
lean_inc_ref(x_270);
lean_dec_ref(x_258);
x_290 = lean_ctor_get(x_269, 3);
lean_inc(x_290);
lean_dec_ref(x_269);
x_291 = lean_unsigned_to_nat(0u);
x_292 = lean_array_get_size(x_270);
x_293 = lean_nat_dec_le(x_290, x_291);
if (x_293 == 0)
{
x_271 = x_290;
x_272 = x_292;
goto block_289;
}
else
{
lean_dec(x_290);
x_271 = x_291;
x_272 = x_292;
goto block_289;
}
block_289:
{
lean_object* x_273; size_t x_274; size_t x_275; lean_object* x_276; lean_object* x_277; 
x_273 = l_Array_toSubarray___redArg(x_270, x_271, x_272);
x_274 = lean_array_size(x_267);
x_275 = 0;
x_276 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_267, x_274, x_275, x_273, x_3);
lean_dec_ref(x_276);
lean_inc(x_6);
x_277 = l_Lean_Compiler_LCNF_Simp_simp(x_268, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
lean_dec_ref(x_277);
x_279 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_267, x_6);
lean_dec(x_6);
lean_dec_ref(x_267);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 x_280 = x_279;
} else {
 lean_dec_ref(x_279);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_259;
}
lean_ctor_set(x_281, 0, x_278);
if (lean_is_scalar(x_280)) {
 x_282 = lean_alloc_ctor(0, 1, 0);
} else {
 x_282 = x_280;
}
lean_ctor_set(x_282, 0, x_281);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_278);
lean_dec(x_259);
x_283 = lean_ctor_get(x_279, 0);
lean_inc(x_283);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 x_284 = x_279;
} else {
 lean_dec_ref(x_279);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 1, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_283);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec_ref(x_267);
lean_dec(x_259);
lean_dec(x_6);
x_286 = lean_ctor_get(x_277, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 x_287 = x_277;
} else {
 lean_dec_ref(x_277);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 1, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_286);
return x_288;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_294 = lean_ctor_get(x_262, 1);
lean_inc_ref(x_294);
x_295 = lean_ctor_get(x_262, 2);
lean_inc_ref(x_295);
lean_dec_ref(x_262);
x_296 = lean_ctor_get(x_258, 0);
lean_inc(x_296);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_297 = x_258;
} else {
 lean_dec_ref(x_258);
 x_297 = lean_box(0);
}
x_298 = lean_unsigned_to_nat(0u);
x_299 = lean_nat_dec_eq(x_296, x_298);
if (x_299 == 1)
{
lean_object* x_300; 
lean_dec(x_297);
lean_dec(x_296);
lean_dec_ref(x_294);
lean_dec(x_264);
x_300 = l_Lean_Compiler_LCNF_Simp_simp(x_295, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 x_302 = x_300;
} else {
 lean_dec_ref(x_300);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_303 = lean_alloc_ctor(1, 1, 0);
} else {
 x_303 = x_259;
}
lean_ctor_set(x_303, 0, x_301);
if (lean_is_scalar(x_302)) {
 x_304 = lean_alloc_ctor(0, 1, 0);
} else {
 x_304 = x_302;
}
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_259);
x_305 = lean_ctor_get(x_300, 0);
lean_inc(x_305);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 x_306 = x_300;
} else {
 lean_dec_ref(x_300);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 1, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_305);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_308 = lean_unsigned_to_nat(1u);
x_309 = lean_nat_sub(x_296, x_308);
lean_dec(x_296);
if (lean_is_scalar(x_297)) {
 x_310 = lean_alloc_ctor(0, 1, 0);
} else {
 x_310 = x_297;
 lean_ctor_set_tag(x_310, 0);
}
lean_ctor_set(x_310, 0, x_309);
x_311 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_311, 0, x_310);
x_312 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_313 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_311, x_312, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
lean_dec_ref(x_313);
x_315 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_316 = lean_array_get_borrowed(x_315, x_294, x_298);
x_317 = lean_ctor_get(x_316, 0);
x_318 = lean_ctor_get(x_314, 0);
lean_inc(x_318);
lean_inc(x_317);
x_319 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_317, x_318, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; 
lean_dec_ref(x_319);
lean_inc(x_6);
x_320 = l_Lean_Compiler_LCNF_Simp_simp(x_295, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
lean_dec_ref(x_320);
x_322 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_294, x_6);
lean_dec(x_6);
lean_dec_ref(x_294);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 x_323 = x_322;
} else {
 lean_dec_ref(x_322);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_264;
}
lean_ctor_set(x_324, 0, x_314);
lean_ctor_set(x_324, 1, x_321);
if (lean_is_scalar(x_259)) {
 x_325 = lean_alloc_ctor(1, 1, 0);
} else {
 x_325 = x_259;
}
lean_ctor_set(x_325, 0, x_324);
if (lean_is_scalar(x_323)) {
 x_326 = lean_alloc_ctor(0, 1, 0);
} else {
 x_326 = x_323;
}
lean_ctor_set(x_326, 0, x_325);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_321);
lean_dec(x_314);
lean_dec(x_264);
lean_dec(x_259);
x_327 = lean_ctor_get(x_322, 0);
lean_inc(x_327);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 x_328 = x_322;
} else {
 lean_dec_ref(x_322);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 1, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_327);
return x_329;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_314);
lean_dec_ref(x_294);
lean_dec(x_264);
lean_dec(x_259);
lean_dec(x_6);
x_330 = lean_ctor_get(x_320, 0);
lean_inc(x_330);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_331 = x_320;
} else {
 lean_dec_ref(x_320);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 1, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_330);
return x_332;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_314);
lean_dec_ref(x_295);
lean_dec_ref(x_294);
lean_dec(x_264);
lean_dec(x_259);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_333 = lean_ctor_get(x_319, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 x_334 = x_319;
} else {
 lean_dec_ref(x_319);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 1, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_333);
return x_335;
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec_ref(x_295);
lean_dec_ref(x_294);
lean_dec(x_264);
lean_dec(x_259);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_336 = lean_ctor_get(x_313, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 x_337 = x_313;
} else {
 lean_dec_ref(x_313);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 1, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_336);
return x_338;
}
}
}
}
else
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_264);
lean_dec(x_258);
x_339 = lean_ctor_get(x_262, 0);
lean_inc_ref(x_339);
lean_dec_ref(x_262);
x_340 = l_Lean_Compiler_LCNF_Simp_simp(x_339, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 x_342 = x_340;
} else {
 lean_dec_ref(x_340);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_343 = lean_alloc_ctor(1, 1, 0);
} else {
 x_343 = x_259;
}
lean_ctor_set(x_343, 0, x_341);
if (lean_is_scalar(x_342)) {
 x_344 = lean_alloc_ctor(0, 1, 0);
} else {
 x_344 = x_342;
}
lean_ctor_set(x_344, 0, x_343);
return x_344;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_259);
x_345 = lean_ctor_get(x_340, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 x_346 = x_340;
} else {
 lean_dec_ref(x_340);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 1, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_345);
return x_347;
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_264);
lean_dec(x_262);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_348 = lean_ctor_get(x_266, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 x_349 = x_266;
} else {
 lean_dec_ref(x_266);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_264);
lean_dec(x_262);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_351 = lean_ctor_get(x_265, 0);
lean_inc(x_351);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_352 = x_265;
} else {
 lean_dec_ref(x_265);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 1, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_351);
return x_353;
}
}
}
}
else
{
uint8_t x_354; 
lean_free_object(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_354 = !lean_is_exclusive(x_17);
if (x_354 == 0)
{
return x_17;
}
else
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_17, 0);
lean_inc(x_355);
lean_dec(x_17);
x_356 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_356, 0, x_355);
return x_356;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_14, 0);
lean_inc(x_357);
lean_dec(x_14);
x_358 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_357, x_4, x_6, x_8);
lean_dec(x_357);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_360 = x_358;
} else {
 lean_dec_ref(x_358);
 x_360 = lean_box(0);
}
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_361 = lean_box(0);
if (lean_is_scalar(x_360)) {
 x_362 = lean_alloc_ctor(0, 1, 0);
} else {
 x_362 = x_360;
}
lean_ctor_set(x_362, 0, x_361);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_360);
x_363 = lean_ctor_get(x_359, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 x_364 = x_359;
} else {
 lean_dec_ref(x_359);
 x_364 = lean_box(0);
}
x_365 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_363);
x_366 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_365);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_369 = x_366;
} else {
 lean_dec_ref(x_366);
 x_369 = lean_box(0);
}
x_370 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_370, 0, x_368);
x_371 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_370, x_6);
lean_dec_ref(x_370);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; 
lean_dec_ref(x_371);
x_372 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_372) == 0)
{
lean_dec_ref(x_372);
if (lean_obj_tag(x_367) == 0)
{
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
lean_dec(x_369);
x_373 = lean_ctor_get(x_367, 1);
lean_inc_ref(x_373);
x_374 = lean_ctor_get(x_367, 2);
lean_inc_ref(x_374);
lean_dec_ref(x_367);
x_375 = lean_ctor_get(x_363, 0);
lean_inc_ref(x_375);
x_376 = lean_ctor_get(x_363, 1);
lean_inc_ref(x_376);
lean_dec_ref(x_363);
x_396 = lean_ctor_get(x_375, 3);
lean_inc(x_396);
lean_dec_ref(x_375);
x_397 = lean_unsigned_to_nat(0u);
x_398 = lean_array_get_size(x_376);
x_399 = lean_nat_dec_le(x_396, x_397);
if (x_399 == 0)
{
x_377 = x_396;
x_378 = x_398;
goto block_395;
}
else
{
lean_dec(x_396);
x_377 = x_397;
x_378 = x_398;
goto block_395;
}
block_395:
{
lean_object* x_379; size_t x_380; size_t x_381; lean_object* x_382; lean_object* x_383; 
x_379 = l_Array_toSubarray___redArg(x_376, x_377, x_378);
x_380 = lean_array_size(x_373);
x_381 = 0;
x_382 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_373, x_380, x_381, x_379, x_3);
lean_dec_ref(x_382);
lean_inc(x_6);
x_383 = l_Lean_Compiler_LCNF_Simp_simp(x_374, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
lean_dec_ref(x_383);
x_385 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_373, x_6);
lean_dec(x_6);
lean_dec_ref(x_373);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 x_386 = x_385;
} else {
 lean_dec_ref(x_385);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_387 = lean_alloc_ctor(1, 1, 0);
} else {
 x_387 = x_364;
}
lean_ctor_set(x_387, 0, x_384);
if (lean_is_scalar(x_386)) {
 x_388 = lean_alloc_ctor(0, 1, 0);
} else {
 x_388 = x_386;
}
lean_ctor_set(x_388, 0, x_387);
return x_388;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_384);
lean_dec(x_364);
x_389 = lean_ctor_get(x_385, 0);
lean_inc(x_389);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 x_390 = x_385;
} else {
 lean_dec_ref(x_385);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 1, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_389);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec_ref(x_373);
lean_dec(x_364);
lean_dec(x_6);
x_392 = lean_ctor_get(x_383, 0);
lean_inc(x_392);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 x_393 = x_383;
} else {
 lean_dec_ref(x_383);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 1, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_392);
return x_394;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_400 = lean_ctor_get(x_367, 1);
lean_inc_ref(x_400);
x_401 = lean_ctor_get(x_367, 2);
lean_inc_ref(x_401);
lean_dec_ref(x_367);
x_402 = lean_ctor_get(x_363, 0);
lean_inc(x_402);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_403 = x_363;
} else {
 lean_dec_ref(x_363);
 x_403 = lean_box(0);
}
x_404 = lean_unsigned_to_nat(0u);
x_405 = lean_nat_dec_eq(x_402, x_404);
if (x_405 == 1)
{
lean_object* x_406; 
lean_dec(x_403);
lean_dec(x_402);
lean_dec_ref(x_400);
lean_dec(x_369);
x_406 = l_Lean_Compiler_LCNF_Simp_simp(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_408 = x_406;
} else {
 lean_dec_ref(x_406);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_409 = lean_alloc_ctor(1, 1, 0);
} else {
 x_409 = x_364;
}
lean_ctor_set(x_409, 0, x_407);
if (lean_is_scalar(x_408)) {
 x_410 = lean_alloc_ctor(0, 1, 0);
} else {
 x_410 = x_408;
}
lean_ctor_set(x_410, 0, x_409);
return x_410;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_364);
x_411 = lean_ctor_get(x_406, 0);
lean_inc(x_411);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_412 = x_406;
} else {
 lean_dec_ref(x_406);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 1, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_411);
return x_413;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_414 = lean_unsigned_to_nat(1u);
x_415 = lean_nat_sub(x_402, x_414);
lean_dec(x_402);
if (lean_is_scalar(x_403)) {
 x_416 = lean_alloc_ctor(0, 1, 0);
} else {
 x_416 = x_403;
 lean_ctor_set_tag(x_416, 0);
}
lean_ctor_set(x_416, 0, x_415);
x_417 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_417, 0, x_416);
x_418 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_419 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_417, x_418, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
lean_dec_ref(x_419);
x_421 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_422 = lean_array_get_borrowed(x_421, x_400, x_404);
x_423 = lean_ctor_get(x_422, 0);
x_424 = lean_ctor_get(x_420, 0);
lean_inc(x_424);
lean_inc(x_423);
x_425 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_423, x_424, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; 
lean_dec_ref(x_425);
lean_inc(x_6);
x_426 = l_Lean_Compiler_LCNF_Simp_simp(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
lean_dec_ref(x_426);
x_428 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_400, x_6);
lean_dec(x_6);
lean_dec_ref(x_400);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 x_429 = x_428;
} else {
 lean_dec_ref(x_428);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_430 = x_369;
}
lean_ctor_set(x_430, 0, x_420);
lean_ctor_set(x_430, 1, x_427);
if (lean_is_scalar(x_364)) {
 x_431 = lean_alloc_ctor(1, 1, 0);
} else {
 x_431 = x_364;
}
lean_ctor_set(x_431, 0, x_430);
if (lean_is_scalar(x_429)) {
 x_432 = lean_alloc_ctor(0, 1, 0);
} else {
 x_432 = x_429;
}
lean_ctor_set(x_432, 0, x_431);
return x_432;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_427);
lean_dec(x_420);
lean_dec(x_369);
lean_dec(x_364);
x_433 = lean_ctor_get(x_428, 0);
lean_inc(x_433);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 x_434 = x_428;
} else {
 lean_dec_ref(x_428);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 1, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_433);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_420);
lean_dec_ref(x_400);
lean_dec(x_369);
lean_dec(x_364);
lean_dec(x_6);
x_436 = lean_ctor_get(x_426, 0);
lean_inc(x_436);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_437 = x_426;
} else {
 lean_dec_ref(x_426);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 1, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_436);
return x_438;
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_420);
lean_dec_ref(x_401);
lean_dec_ref(x_400);
lean_dec(x_369);
lean_dec(x_364);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_439 = lean_ctor_get(x_425, 0);
lean_inc(x_439);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 x_440 = x_425;
} else {
 lean_dec_ref(x_425);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 1, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec_ref(x_401);
lean_dec_ref(x_400);
lean_dec(x_369);
lean_dec(x_364);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_442 = lean_ctor_get(x_419, 0);
lean_inc(x_442);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 x_443 = x_419;
} else {
 lean_dec_ref(x_419);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(1, 1, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_442);
return x_444;
}
}
}
}
else
{
lean_object* x_445; lean_object* x_446; 
lean_dec(x_369);
lean_dec(x_363);
x_445 = lean_ctor_get(x_367, 0);
lean_inc_ref(x_445);
lean_dec_ref(x_367);
x_446 = l_Lean_Compiler_LCNF_Simp_simp(x_445, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 x_448 = x_446;
} else {
 lean_dec_ref(x_446);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_449 = lean_alloc_ctor(1, 1, 0);
} else {
 x_449 = x_364;
}
lean_ctor_set(x_449, 0, x_447);
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(0, 1, 0);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_449);
return x_450;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_364);
x_451 = lean_ctor_get(x_446, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 x_452 = x_446;
} else {
 lean_dec_ref(x_446);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 1, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_451);
return x_453;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_454 = lean_ctor_get(x_372, 0);
lean_inc(x_454);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_455 = x_372;
} else {
 lean_dec_ref(x_372);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(1, 1, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_454);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_457 = lean_ctor_get(x_371, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 x_458 = x_371;
} else {
 lean_dec_ref(x_371);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 1, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_457);
return x_459;
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_460 = lean_ctor_get(x_358, 0);
lean_inc(x_460);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_461 = x_358;
} else {
 lean_dec_ref(x_358);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 1, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_460);
return x_462;
}
}
}
else
{
lean_object* x_463; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_463 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_463) == 0)
{
uint8_t x_464; 
x_464 = !lean_is_exclusive(x_463);
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; 
x_465 = lean_ctor_get(x_463, 0);
x_466 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_463, 0, x_466);
return x_463;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_463, 0);
lean_inc(x_467);
lean_dec(x_463);
x_468 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_468, 0, x_467);
x_469 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_469, 0, x_468);
return x_469;
}
}
else
{
uint8_t x_470; 
x_470 = !lean_is_exclusive(x_463);
if (x_470 == 0)
{
return x_463;
}
else
{
lean_object* x_471; lean_object* x_472; 
x_471 = lean_ctor_get(x_463, 0);
lean_inc(x_471);
lean_dec(x_463);
x_472 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_472, 0, x_471);
return x_472;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget_borrowed(x_3, x_2);
x_11 = lean_ctor_get(x_10, 2);
x_12 = lean_st_ref_get(x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
lean_inc_ref(x_11);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_13, x_1, x_11);
lean_dec_ref(x_13);
lean_inc_ref(x_10);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(x_10, x_14, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ptr_addr(x_10);
x_18 = lean_ptr_addr(x_16);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_array_fset(x_3, x_2, x_16);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_1, x_2, x_3, x_5, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_1, x_11, x_2, x_4, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_st_ref_get(x_3);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
x_14 = 0;
lean_inc_ref(x_11);
x_15 = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_14, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_6);
lean_inc_ref(x_13);
x_17 = l_Lean_Compiler_LCNF_Simp_simp(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_10);
lean_inc_ref(x_12);
x_20 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_19, x_14, x_12);
lean_dec_ref(x_19);
x_21 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_20, x_16, x_18, x_6);
lean_dec(x_6);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_6, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_5, x_2, x_3);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_6, x_7, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_6, x_7, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_7, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_ConstantFold(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_ConstantFold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7);
l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0);
l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3);
l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0 = _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0);
l_Lean_Compiler_LCNF_Simp_simp___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__0);
l_Lean_Compiler_LCNF_Simp_simp___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__1);
l_Lean_Compiler_LCNF_Simp_simp___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__2);
l_Lean_Compiler_LCNF_Simp_simp___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__3);
l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
