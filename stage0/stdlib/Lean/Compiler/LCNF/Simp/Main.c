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
if (lean_obj_tag(x_13) == 1)
{
uint8_t x_14; 
lean_free_object(x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_15, x_4, x_6);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; 
lean_free_object(x_16);
x_21 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec_ref(x_21);
x_22 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_15, 4);
lean_inc_ref(x_23);
lean_dec(x_15);
x_24 = 0;
x_25 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_22, x_23, x_2, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_13, 0, x_27);
lean_ctor_set(x_25, 0, x_13);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_13, 0, x_28);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_13);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_free_object(x_13);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
lean_dec(x_16);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
lean_dec_ref(x_40);
x_41 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_15, 4);
lean_inc_ref(x_42);
lean_dec(x_15);
x_43 = 0;
x_44 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_41, x_42, x_2, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
lean_ctor_set(x_13, 0, x_45);
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_13);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_13);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_49 = x_44;
} else {
 lean_dec_ref(x_44);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_51 = lean_ctor_get(x_40, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_52 = x_40;
} else {
 lean_dec_ref(x_40);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_54 = !lean_is_exclusive(x_16);
if (x_54 == 0)
{
return x_16;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_16, 0);
lean_inc(x_55);
lean_dec(x_16);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_13, 0);
lean_inc(x_57);
lean_dec(x_13);
x_58 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_57, x_4, x_6);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_unbox(x_59);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_57);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_62 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
lean_object* x_64; 
lean_dec(x_60);
x_64 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
lean_dec_ref(x_64);
x_65 = lean_ctor_get(x_57, 2);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_57, 4);
lean_inc_ref(x_66);
lean_dec(x_57);
x_67 = 0;
x_68 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_65, x_66, x_2, x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_65);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_69);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_74 = x_68;
} else {
 lean_dec_ref(x_68);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_57);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_76 = lean_ctor_get(x_64, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_77 = x_64;
} else {
 lean_dec_ref(x_64);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_57);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_79 = lean_ctor_get(x_58, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_80 = x_58;
} else {
 lean_dec_ref(x_58);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_82 = lean_box(0);
lean_ctor_set(x_11, 0, x_82);
return x_11;
}
}
else
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_11, 0);
lean_inc(x_83);
lean_dec(x_11);
if (lean_obj_tag(x_83) == 1)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_84, x_4, x_6);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_unbox(x_87);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_90 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
else
{
lean_object* x_92; 
lean_dec(x_88);
x_92 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
lean_dec_ref(x_92);
x_93 = lean_ctor_get(x_84, 2);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_84, 4);
lean_inc_ref(x_94);
lean_dec(x_84);
x_95 = 0;
x_96 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_93, x_94, x_2, x_95, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_93);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_85;
}
lean_ctor_set(x_99, 0, x_97);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 1, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_85);
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_102 = x_96;
} else {
 lean_dec_ref(x_96);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_104 = lean_ctor_get(x_92, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_105 = x_92;
} else {
 lean_dec_ref(x_92);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_107 = lean_ctor_get(x_86, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_108 = x_86;
} else {
 lean_dec_ref(x_86);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_83);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
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
if (lean_obj_tag(x_23) == 1)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_ConstantInfo_type(x_25);
lean_dec(x_25);
x_27 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_26, x_7);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
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
x_31 = lean_box(0);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; 
lean_free_object(x_27);
x_32 = l_Lean_Meta_isInstance___redArg(x_17, x_7);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_free_object(x_32);
lean_inc(x_17);
x_36 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
if (lean_obj_tag(x_38) == 1)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_array_get_size(x_19);
x_42 = l_Lean_Compiler_LCNF_Decl_getArity(x_40);
lean_dec(x_40);
x_43 = lean_nat_dec_lt(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_free_object(x_38);
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
x_44 = lean_box(0);
lean_ctor_set(x_36, 0, x_44);
return x_36;
}
else
{
lean_object* x_45; 
lean_free_object(x_36);
lean_inc_ref(x_16);
x_45 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_array_size(x_46);
x_48 = 0;
lean_inc(x_46);
x_49 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_47, x_48, x_46);
x_50 = l_Array_append___redArg(x_19, x_49);
lean_dec_ref(x_49);
lean_ctor_set(x_13, 2, x_50);
x_51 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_52 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_51, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_ctor_set_tag(x_23, 5);
lean_ctor_set(x_23, 0, x_54);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_23);
x_56 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_57 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_46, x_55, x_56, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_inc(x_15);
x_60 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_59, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_dec_ref(x_60);
x_61 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_38, 0, x_58);
lean_ctor_set(x_61, 0, x_38);
return x_61;
}
else
{
lean_object* x_64; 
lean_dec(x_61);
lean_ctor_set(x_38, 0, x_58);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_38);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_58);
lean_free_object(x_38);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_58);
lean_free_object(x_38);
lean_dec(x_5);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_60, 0);
lean_inc(x_69);
lean_dec(x_60);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_free_object(x_38);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_57);
if (x_71 == 0)
{
return x_57;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_57, 0);
lean_inc(x_72);
lean_dec(x_57);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_46);
lean_free_object(x_38);
lean_free_object(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_52);
if (x_74 == 0)
{
return x_52;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_52, 0);
lean_inc(x_75);
lean_dec(x_52);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_free_object(x_38);
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
x_77 = !lean_is_exclusive(x_45);
if (x_77 == 0)
{
return x_45;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_45, 0);
lean_inc(x_78);
lean_dec(x_45);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_38, 0);
lean_inc(x_80);
lean_dec(x_38);
x_81 = lean_array_get_size(x_19);
x_82 = l_Lean_Compiler_LCNF_Decl_getArity(x_80);
lean_dec(x_80);
x_83 = lean_nat_dec_lt(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; 
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
x_84 = lean_box(0);
lean_ctor_set(x_36, 0, x_84);
return x_36;
}
else
{
lean_object* x_85; 
lean_free_object(x_36);
lean_inc_ref(x_16);
x_85 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_array_size(x_86);
x_88 = 0;
lean_inc(x_86);
x_89 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_87, x_88, x_86);
x_90 = l_Array_append___redArg(x_19, x_89);
lean_dec_ref(x_89);
lean_ctor_set(x_13, 2, x_90);
x_91 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_92 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_91, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_ctor_set_tag(x_23, 5);
lean_ctor_set(x_23, 0, x_94);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_23);
x_96 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_97 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_86, x_95, x_96, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_inc(x_15);
x_100 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_99, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
lean_dec_ref(x_100);
x_101 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_102 = x_101;
} else {
 lean_dec_ref(x_101);
 x_102 = lean_box(0);
}
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 1, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_98);
x_105 = lean_ctor_get(x_101, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_106 = x_101;
} else {
 lean_dec_ref(x_101);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 1, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_98);
lean_dec(x_5);
lean_dec_ref(x_1);
x_108 = lean_ctor_get(x_100, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_109 = x_100;
} else {
 lean_dec_ref(x_100);
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
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_97, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_112 = x_97;
} else {
 lean_dec_ref(x_97);
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
lean_dec(x_86);
lean_free_object(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_114 = lean_ctor_get(x_92, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_115 = x_92;
} else {
 lean_dec_ref(x_92);
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
x_117 = lean_ctor_get(x_85, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_118 = x_85;
} else {
 lean_dec_ref(x_85);
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
}
}
else
{
lean_object* x_120; 
lean_dec(x_38);
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
x_120 = lean_box(0);
lean_ctor_set(x_36, 0, x_120);
return x_36;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_36, 0);
lean_inc(x_121);
lean_dec(x_36);
if (lean_obj_tag(x_121) == 1)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
x_124 = lean_array_get_size(x_19);
x_125 = l_Lean_Compiler_LCNF_Decl_getArity(x_122);
lean_dec(x_122);
x_126 = lean_nat_dec_lt(x_124, x_125);
lean_dec(x_125);
lean_dec(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_123);
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
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
else
{
lean_object* x_129; 
lean_inc_ref(x_16);
x_129 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; size_t x_131; size_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = lean_array_size(x_130);
x_132 = 0;
lean_inc(x_130);
x_133 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_131, x_132, x_130);
x_134 = l_Array_append___redArg(x_19, x_133);
lean_dec_ref(x_133);
lean_ctor_set(x_13, 2, x_134);
x_135 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_136 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_135, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_ctor_set_tag(x_23, 5);
lean_ctor_set(x_23, 0, x_138);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_23);
x_140 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_141 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_130, x_139, x_140, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_inc(x_15);
x_144 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_143, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
lean_dec_ref(x_144);
x_145 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_146 = x_145;
} else {
 lean_dec_ref(x_145);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_147 = x_123;
}
lean_ctor_set(x_147, 0, x_142);
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 1, 0);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_142);
lean_dec(x_123);
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_150 = x_145;
} else {
 lean_dec_ref(x_145);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_149);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_142);
lean_dec(x_123);
lean_dec(x_5);
lean_dec_ref(x_1);
x_152 = lean_ctor_get(x_144, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_153 = x_144;
} else {
 lean_dec_ref(x_144);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 1, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_123);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_141, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_156 = x_141;
} else {
 lean_dec_ref(x_141);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 1, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_130);
lean_dec(x_123);
lean_free_object(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_158 = lean_ctor_get(x_136, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_159 = x_136;
} else {
 lean_dec_ref(x_136);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_123);
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
x_161 = lean_ctor_get(x_129, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_162 = x_129;
} else {
 lean_dec_ref(x_129);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_161);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_121);
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
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
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
x_166 = !lean_is_exclusive(x_36);
if (x_166 == 0)
{
return x_36;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_36, 0);
lean_inc(x_167);
lean_dec(x_36);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; 
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
x_169 = lean_box(0);
lean_ctor_set(x_32, 0, x_169);
return x_32;
}
}
else
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_32, 0);
lean_inc(x_170);
lean_dec(x_32);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; 
lean_inc(x_17);
x_172 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
if (lean_obj_tag(x_173) == 1)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
x_177 = lean_array_get_size(x_19);
x_178 = l_Lean_Compiler_LCNF_Decl_getArity(x_175);
lean_dec(x_175);
x_179 = lean_nat_dec_lt(x_177, x_178);
lean_dec(x_178);
lean_dec(x_177);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_176);
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
x_180 = lean_box(0);
if (lean_is_scalar(x_174)) {
 x_181 = lean_alloc_ctor(0, 1, 0);
} else {
 x_181 = x_174;
}
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
else
{
lean_object* x_182; 
lean_dec(x_174);
lean_inc_ref(x_16);
x_182 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; size_t x_184; size_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = lean_array_size(x_183);
x_185 = 0;
lean_inc(x_183);
x_186 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_184, x_185, x_183);
x_187 = l_Array_append___redArg(x_19, x_186);
lean_dec_ref(x_186);
lean_ctor_set(x_13, 2, x_187);
x_188 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_189 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_188, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec_ref(x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_ctor_set_tag(x_23, 5);
lean_ctor_set(x_23, 0, x_191);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_23);
x_193 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_194 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_183, x_192, x_193, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec_ref(x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
lean_inc(x_15);
x_197 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_196, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; 
lean_dec_ref(x_197);
x_198 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_199 = x_198;
} else {
 lean_dec_ref(x_198);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_176;
}
lean_ctor_set(x_200, 0, x_195);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 1, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_195);
lean_dec(x_176);
x_202 = lean_ctor_get(x_198, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_203 = x_198;
} else {
 lean_dec_ref(x_198);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_195);
lean_dec(x_176);
lean_dec(x_5);
lean_dec_ref(x_1);
x_205 = lean_ctor_get(x_197, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 x_206 = x_197;
} else {
 lean_dec_ref(x_197);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_176);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_208 = lean_ctor_get(x_194, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_209 = x_194;
} else {
 lean_dec_ref(x_194);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 1, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_183);
lean_dec(x_176);
lean_free_object(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_211 = lean_ctor_get(x_189, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_212 = x_189;
} else {
 lean_dec_ref(x_189);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 1, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_176);
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
x_214 = lean_ctor_get(x_182, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_215 = x_182;
} else {
 lean_dec_ref(x_182);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_214);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_173);
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
x_217 = lean_box(0);
if (lean_is_scalar(x_174)) {
 x_218 = lean_alloc_ctor(0, 1, 0);
} else {
 x_218 = x_174;
}
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
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
x_219 = lean_ctor_get(x_172, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_220 = x_172;
} else {
 lean_dec_ref(x_172);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 1, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_219);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; 
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
x_222 = lean_box(0);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_222);
return x_223;
}
}
}
else
{
uint8_t x_224; 
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
x_224 = !lean_is_exclusive(x_32);
if (x_224 == 0)
{
return x_32;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_32, 0);
lean_inc(x_225);
lean_dec(x_32);
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_225);
return x_226;
}
}
}
}
else
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_ctor_get(x_27, 0);
lean_inc(x_227);
lean_dec(x_27);
x_228 = lean_unbox(x_227);
lean_dec(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
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
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_229);
return x_230;
}
else
{
lean_object* x_231; 
x_231 = l_Lean_Meta_isInstance___redArg(x_17, x_7);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
x_234 = lean_unbox(x_232);
lean_dec(x_232);
if (x_234 == 0)
{
lean_object* x_235; 
lean_dec(x_233);
lean_inc(x_17);
x_235 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
if (lean_obj_tag(x_236) == 1)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_238 = lean_ctor_get(x_236, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
x_240 = lean_array_get_size(x_19);
x_241 = l_Lean_Compiler_LCNF_Decl_getArity(x_238);
lean_dec(x_238);
x_242 = lean_nat_dec_lt(x_240, x_241);
lean_dec(x_241);
lean_dec(x_240);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_239);
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
x_243 = lean_box(0);
if (lean_is_scalar(x_237)) {
 x_244 = lean_alloc_ctor(0, 1, 0);
} else {
 x_244 = x_237;
}
lean_ctor_set(x_244, 0, x_243);
return x_244;
}
else
{
lean_object* x_245; 
lean_dec(x_237);
lean_inc_ref(x_16);
x_245 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; size_t x_247; size_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_247 = lean_array_size(x_246);
x_248 = 0;
lean_inc(x_246);
x_249 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_247, x_248, x_246);
x_250 = l_Array_append___redArg(x_19, x_249);
lean_dec_ref(x_249);
lean_ctor_set(x_13, 2, x_250);
x_251 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_252 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_251, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_ctor_set_tag(x_23, 5);
lean_ctor_set(x_23, 0, x_254);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_23);
x_256 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_257 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_246, x_255, x_256, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec_ref(x_257);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_inc(x_15);
x_260 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_259, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; 
lean_dec_ref(x_260);
x_261 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_262 = x_261;
} else {
 lean_dec_ref(x_261);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_263 = lean_alloc_ctor(1, 1, 0);
} else {
 x_263 = x_239;
}
lean_ctor_set(x_263, 0, x_258);
if (lean_is_scalar(x_262)) {
 x_264 = lean_alloc_ctor(0, 1, 0);
} else {
 x_264 = x_262;
}
lean_ctor_set(x_264, 0, x_263);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_258);
lean_dec(x_239);
x_265 = lean_ctor_get(x_261, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_266 = x_261;
} else {
 lean_dec_ref(x_261);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 1, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_265);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_258);
lean_dec(x_239);
lean_dec(x_5);
lean_dec_ref(x_1);
x_268 = lean_ctor_get(x_260, 0);
lean_inc(x_268);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 x_269 = x_260;
} else {
 lean_dec_ref(x_260);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 1, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_268);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_239);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_271 = lean_ctor_get(x_257, 0);
lean_inc(x_271);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_272 = x_257;
} else {
 lean_dec_ref(x_257);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 1, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_271);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_246);
lean_dec(x_239);
lean_free_object(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_274 = lean_ctor_get(x_252, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 x_275 = x_252;
} else {
 lean_dec_ref(x_252);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 1, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_274);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_239);
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
x_277 = lean_ctor_get(x_245, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 x_278 = x_245;
} else {
 lean_dec_ref(x_245);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 1, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_277);
return x_279;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_236);
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
x_280 = lean_box(0);
if (lean_is_scalar(x_237)) {
 x_281 = lean_alloc_ctor(0, 1, 0);
} else {
 x_281 = x_237;
}
lean_ctor_set(x_281, 0, x_280);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
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
x_282 = lean_ctor_get(x_235, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_283 = x_235;
} else {
 lean_dec_ref(x_235);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 1, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; 
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
x_285 = lean_box(0);
if (lean_is_scalar(x_233)) {
 x_286 = lean_alloc_ctor(0, 1, 0);
} else {
 x_286 = x_233;
}
lean_ctor_set(x_286, 0, x_285);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
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
x_287 = lean_ctor_get(x_231, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_288 = x_231;
} else {
 lean_dec_ref(x_231);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 1, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_287);
return x_289;
}
}
}
}
else
{
uint8_t x_290; 
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
x_290 = !lean_is_exclusive(x_27);
if (x_290 == 0)
{
return x_27;
}
else
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_27, 0);
lean_inc(x_291);
lean_dec(x_27);
x_292 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_292, 0, x_291);
return x_292;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_23, 0);
lean_inc(x_293);
lean_dec(x_23);
x_294 = l_Lean_ConstantInfo_type(x_293);
lean_dec(x_293);
x_295 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_294, x_7);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_297 = x_295;
} else {
 lean_dec_ref(x_295);
 x_297 = lean_box(0);
}
x_298 = lean_unbox(x_296);
lean_dec(x_296);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_299 = lean_box(0);
if (lean_is_scalar(x_297)) {
 x_300 = lean_alloc_ctor(0, 1, 0);
} else {
 x_300 = x_297;
}
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
else
{
lean_object* x_301; 
lean_dec(x_297);
x_301 = l_Lean_Meta_isInstance___redArg(x_17, x_7);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 x_303 = x_301;
} else {
 lean_dec_ref(x_301);
 x_303 = lean_box(0);
}
x_304 = lean_unbox(x_302);
lean_dec(x_302);
if (x_304 == 0)
{
lean_object* x_305; 
lean_dec(x_303);
lean_inc(x_17);
x_305 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_307 = x_305;
} else {
 lean_dec_ref(x_305);
 x_307 = lean_box(0);
}
if (lean_obj_tag(x_306) == 1)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_308 = lean_ctor_get(x_306, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_309 = x_306;
} else {
 lean_dec_ref(x_306);
 x_309 = lean_box(0);
}
x_310 = lean_array_get_size(x_19);
x_311 = l_Lean_Compiler_LCNF_Decl_getArity(x_308);
lean_dec(x_308);
x_312 = lean_nat_dec_lt(x_310, x_311);
lean_dec(x_311);
lean_dec(x_310);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_309);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_313 = lean_box(0);
if (lean_is_scalar(x_307)) {
 x_314 = lean_alloc_ctor(0, 1, 0);
} else {
 x_314 = x_307;
}
lean_ctor_set(x_314, 0, x_313);
return x_314;
}
else
{
lean_object* x_315; 
lean_dec(x_307);
lean_inc_ref(x_16);
x_315 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; size_t x_317; size_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
x_317 = lean_array_size(x_316);
x_318 = 0;
lean_inc(x_316);
x_319 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_317, x_318, x_316);
x_320 = l_Array_append___redArg(x_19, x_319);
lean_dec_ref(x_319);
lean_ctor_set(x_13, 2, x_320);
x_321 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_322 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_321, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
lean_dec_ref(x_322);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_325, 0, x_324);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_325);
x_327 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_328 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_316, x_326, x_327, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
lean_dec_ref(x_328);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
lean_inc(x_15);
x_331 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_330, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; 
lean_dec_ref(x_331);
x_332 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 x_333 = x_332;
} else {
 lean_dec_ref(x_332);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_334 = lean_alloc_ctor(1, 1, 0);
} else {
 x_334 = x_309;
}
lean_ctor_set(x_334, 0, x_329);
if (lean_is_scalar(x_333)) {
 x_335 = lean_alloc_ctor(0, 1, 0);
} else {
 x_335 = x_333;
}
lean_ctor_set(x_335, 0, x_334);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_329);
lean_dec(x_309);
x_336 = lean_ctor_get(x_332, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 x_337 = x_332;
} else {
 lean_dec_ref(x_332);
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
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_329);
lean_dec(x_309);
lean_dec(x_5);
lean_dec_ref(x_1);
x_339 = lean_ctor_get(x_331, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 x_340 = x_331;
} else {
 lean_dec_ref(x_331);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 1, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_339);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_309);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_342 = lean_ctor_get(x_328, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_343 = x_328;
} else {
 lean_dec_ref(x_328);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 1, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_342);
return x_344;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_316);
lean_dec(x_309);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_345 = lean_ctor_get(x_322, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 x_346 = x_322;
} else {
 lean_dec_ref(x_322);
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
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_309);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_348 = lean_ctor_get(x_315, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 x_349 = x_315;
} else {
 lean_dec_ref(x_315);
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
}
else
{
lean_object* x_351; lean_object* x_352; 
lean_dec(x_306);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_351 = lean_box(0);
if (lean_is_scalar(x_307)) {
 x_352 = lean_alloc_ctor(0, 1, 0);
} else {
 x_352 = x_307;
}
lean_ctor_set(x_352, 0, x_351);
return x_352;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_353 = lean_ctor_get(x_305, 0);
lean_inc(x_353);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_354 = x_305;
} else {
 lean_dec_ref(x_305);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 1, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_353);
return x_355;
}
}
else
{
lean_object* x_356; lean_object* x_357; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_356 = lean_box(0);
if (lean_is_scalar(x_303)) {
 x_357 = lean_alloc_ctor(0, 1, 0);
} else {
 x_357 = x_303;
}
lean_ctor_set(x_357, 0, x_356);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_358 = lean_ctor_get(x_301, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 x_359 = x_301;
} else {
 lean_dec_ref(x_301);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 1, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_358);
return x_360;
}
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_361 = lean_ctor_get(x_295, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_362 = x_295;
} else {
 lean_dec_ref(x_295);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 1, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_361);
return x_363;
}
}
}
else
{
lean_object* x_364; lean_object* x_365; 
lean_dec(x_23);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_364 = lean_box(0);
x_365 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_365, 0, x_364);
return x_365;
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
if (lean_obj_tag(x_374) == 1)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_376 = x_374;
} else {
 lean_dec_ref(x_374);
 x_376 = lean_box(0);
}
x_377 = l_Lean_ConstantInfo_type(x_375);
lean_dec(x_375);
x_378 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_377, x_7);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 x_380 = x_378;
} else {
 lean_dec_ref(x_378);
 x_380 = lean_box(0);
}
x_381 = lean_unbox(x_379);
lean_dec(x_379);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_376);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_382 = lean_box(0);
if (lean_is_scalar(x_380)) {
 x_383 = lean_alloc_ctor(0, 1, 0);
} else {
 x_383 = x_380;
}
lean_ctor_set(x_383, 0, x_382);
return x_383;
}
else
{
lean_object* x_384; 
lean_dec(x_380);
x_384 = l_Lean_Meta_isInstance___redArg(x_368, x_7);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 x_386 = x_384;
} else {
 lean_dec_ref(x_384);
 x_386 = lean_box(0);
}
x_387 = lean_unbox(x_385);
lean_dec(x_385);
if (x_387 == 0)
{
lean_object* x_388; 
lean_dec(x_386);
lean_inc(x_368);
x_388 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_368, x_4, x_7);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 x_390 = x_388;
} else {
 lean_dec_ref(x_388);
 x_390 = lean_box(0);
}
if (lean_obj_tag(x_389) == 1)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_391 = lean_ctor_get(x_389, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 x_392 = x_389;
} else {
 lean_dec_ref(x_389);
 x_392 = lean_box(0);
}
x_393 = lean_array_get_size(x_370);
x_394 = l_Lean_Compiler_LCNF_Decl_getArity(x_391);
lean_dec(x_391);
x_395 = lean_nat_dec_lt(x_393, x_394);
lean_dec(x_394);
lean_dec(x_393);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_392);
lean_dec(x_376);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_396 = lean_box(0);
if (lean_is_scalar(x_390)) {
 x_397 = lean_alloc_ctor(0, 1, 0);
} else {
 x_397 = x_390;
}
lean_ctor_set(x_397, 0, x_396);
return x_397;
}
else
{
lean_object* x_398; 
lean_dec(x_390);
lean_inc_ref(x_367);
x_398 = l_Lean_Compiler_LCNF_mkNewParams(x_367, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; size_t x_400; size_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
x_400 = lean_array_size(x_399);
x_401 = 0;
lean_inc(x_399);
x_402 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_400, x_401, x_399);
x_403 = l_Array_append___redArg(x_370, x_402);
lean_dec_ref(x_402);
x_404 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_404, 0, x_368);
lean_ctor_set(x_404, 1, x_369);
lean_ctor_set(x_404, 2, x_403);
x_405 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_406 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_404, x_405, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
lean_dec_ref(x_406);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
if (lean_is_scalar(x_376)) {
 x_409 = lean_alloc_ctor(5, 1, 0);
} else {
 x_409 = x_376;
 lean_ctor_set_tag(x_409, 5);
}
lean_ctor_set(x_409, 0, x_408);
x_410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_409);
x_411 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_412 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_399, x_410, x_411, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
lean_dec_ref(x_412);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
lean_inc(x_366);
x_415 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_366, x_414, x_3, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; 
lean_dec_ref(x_415);
x_416 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_417 = x_416;
} else {
 lean_dec_ref(x_416);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_418 = lean_alloc_ctor(1, 1, 0);
} else {
 x_418 = x_392;
}
lean_ctor_set(x_418, 0, x_413);
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(0, 1, 0);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_418);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_413);
lean_dec(x_392);
x_420 = lean_ctor_get(x_416, 0);
lean_inc(x_420);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_421 = x_416;
} else {
 lean_dec_ref(x_416);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 1, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_420);
return x_422;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_413);
lean_dec(x_392);
lean_dec(x_5);
lean_dec_ref(x_1);
x_423 = lean_ctor_get(x_415, 0);
lean_inc(x_423);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 x_424 = x_415;
} else {
 lean_dec_ref(x_415);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 1, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_392);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_426 = lean_ctor_get(x_412, 0);
lean_inc(x_426);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 x_427 = x_412;
} else {
 lean_dec_ref(x_412);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 1, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_426);
return x_428;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_399);
lean_dec(x_392);
lean_dec(x_376);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_429 = lean_ctor_get(x_406, 0);
lean_inc(x_429);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_430 = x_406;
} else {
 lean_dec_ref(x_406);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 1, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_429);
return x_431;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_392);
lean_dec(x_376);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_432 = lean_ctor_get(x_398, 0);
lean_inc(x_432);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 x_433 = x_398;
} else {
 lean_dec_ref(x_398);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 1, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_432);
return x_434;
}
}
}
else
{
lean_object* x_435; lean_object* x_436; 
lean_dec(x_389);
lean_dec(x_376);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_435 = lean_box(0);
if (lean_is_scalar(x_390)) {
 x_436 = lean_alloc_ctor(0, 1, 0);
} else {
 x_436 = x_390;
}
lean_ctor_set(x_436, 0, x_435);
return x_436;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_376);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_437 = lean_ctor_get(x_388, 0);
lean_inc(x_437);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 x_438 = x_388;
} else {
 lean_dec_ref(x_388);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 1, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_437);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_376);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_440 = lean_box(0);
if (lean_is_scalar(x_386)) {
 x_441 = lean_alloc_ctor(0, 1, 0);
} else {
 x_441 = x_386;
}
lean_ctor_set(x_441, 0, x_440);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_376);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_442 = lean_ctor_get(x_384, 0);
lean_inc(x_442);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 x_443 = x_384;
} else {
 lean_dec_ref(x_384);
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
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_376);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_445 = lean_ctor_get(x_378, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 x_446 = x_378;
} else {
 lean_dec_ref(x_378);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 1, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; 
lean_dec(x_374);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_448 = lean_box(0);
x_449 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_449, 0, x_448);
return x_449;
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
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_free_object(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_16, 2);
x_21 = lean_ctor_get(x_16, 3);
x_22 = lean_ctor_get_uint8(x_16, sizeof(void*)*4 + 2);
x_23 = lean_array_get_size(x_21);
x_24 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_16);
lean_inc_ref(x_21);
lean_inc_ref(x_2);
lean_inc(x_11);
lean_inc(x_23);
lean_inc(x_24);
x_25 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 14, 5);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_23);
lean_closure_set(x_25, 2, x_11);
lean_closure_set(x_25, 3, x_2);
lean_closure_set(x_25, 4, x_21);
x_26 = lean_nat_dec_lt(x_23, x_24);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_12, 0);
lean_inc(x_202);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_202);
x_203 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(x_22, x_202, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
x_205 = !lean_is_exclusive(x_3);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_3, 2);
x_207 = lean_ctor_get(x_3, 3);
lean_inc(x_202);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_202);
lean_ctor_set(x_208, 1, x_206);
x_209 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_207, x_202, x_204);
lean_ctor_set(x_3, 3, x_209);
lean_ctor_set(x_3, 2, x_208);
x_165 = x_3;
x_166 = x_4;
x_167 = x_5;
x_168 = x_6;
x_169 = x_7;
x_170 = x_8;
x_171 = x_9;
x_172 = lean_box(0);
goto block_201;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_210 = lean_ctor_get(x_3, 0);
x_211 = lean_ctor_get(x_3, 1);
x_212 = lean_ctor_get(x_3, 2);
x_213 = lean_ctor_get(x_3, 3);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_3);
lean_inc(x_202);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_202);
lean_ctor_set(x_214, 1, x_212);
x_215 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_213, x_202, x_204);
x_216 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_216, 0, x_210);
lean_ctor_set(x_216, 1, x_211);
lean_ctor_set(x_216, 2, x_214);
lean_ctor_set(x_216, 3, x_215);
x_165 = x_216;
x_166 = x_4;
x_167 = x_5;
x_168 = x_6;
x_169 = x_7;
x_170 = x_8;
x_171 = x_9;
x_172 = lean_box(0);
goto block_201;
}
}
else
{
uint8_t x_217; 
lean_dec(x_202);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_217 = !lean_is_exclusive(x_203);
if (x_217 == 0)
{
return x_203;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_203, 0);
lean_inc(x_218);
lean_dec(x_203);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
return x_219;
}
}
}
else
{
lean_dec(x_12);
x_165 = x_3;
x_166 = x_4;
x_167 = x_5;
x_168 = x_6;
x_169 = x_7;
x_170 = x_8;
x_171 = x_9;
x_172 = lean_box(0);
goto block_201;
}
block_129:
{
lean_object* x_38; 
lean_inc(x_29);
lean_inc_ref(x_30);
lean_inc(x_37);
lean_inc_ref(x_35);
lean_inc_ref(x_27);
lean_inc(x_28);
lean_inc_ref(x_31);
x_38 = l_Lean_Compiler_LCNF_Simp_simp(x_36, x_31, x_28, x_27, x_35, x_37, x_30, x_29);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_28);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
lean_dec_ref(x_40);
lean_inc(x_39);
x_41 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec_ref(x_34);
x_42 = l_Lean_Compiler_LCNF_inferAppType(x_20, x_33, x_35, x_37, x_30, x_29);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc(x_43);
x_44 = l_Lean_Expr_headBeta(x_43);
x_45 = l_Lean_Expr_isForall(x_44);
lean_dec_ref(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Lean_Compiler_LCNF_mkAuxParam(x_43, x_26, x_35, x_37, x_30, x_29);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_29);
lean_inc_ref(x_30);
lean_inc(x_37);
lean_inc_ref(x_35);
lean_inc(x_48);
x_49 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_24, x_23, x_11, x_2, x_21, x_48, x_31, x_28, x_27, x_35, x_37, x_30, x_29);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_53 = lean_array_push(x_52, x_47);
x_54 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_55 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_53, x_50, x_54, x_35, x_37, x_30, x_29);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_56);
x_57 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_57, 0, x_56);
lean_closure_set(x_57, 1, x_51);
x_58 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_39, x_57, x_35, x_37, x_30, x_29);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
if (lean_is_scalar(x_17)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_17;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_58, 0, x_62);
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
lean_dec(x_58);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_63);
if (lean_is_scalar(x_17)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_17;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_56);
lean_dec(x_17);
x_67 = !lean_is_exclusive(x_58);
if (x_67 == 0)
{
return x_58;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_58, 0);
lean_inc(x_68);
lean_dec(x_58);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_17);
x_70 = !lean_is_exclusive(x_55);
if (x_70 == 0)
{
return x_55;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_55, 0);
lean_inc(x_71);
lean_dec(x_55);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_47);
lean_dec(x_39);
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_17);
x_73 = !lean_is_exclusive(x_49);
if (x_73 == 0)
{
return x_49;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_49, 0);
lean_inc(x_74);
lean_dec(x_49);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_2);
x_76 = !lean_is_exclusive(x_46);
if (x_76 == 0)
{
return x_46;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_46, 0);
lean_inc(x_77);
lean_dec(x_46);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_43);
x_79 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
x_80 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_81 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_79, x_39, x_80, x_35, x_37, x_30, x_29);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
lean_inc(x_29);
lean_inc_ref(x_30);
lean_inc(x_37);
lean_inc_ref(x_35);
x_83 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_82, x_35, x_37, x_30, x_29);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_29);
lean_inc_ref(x_30);
lean_inc(x_37);
lean_inc_ref(x_35);
lean_inc_ref(x_27);
lean_inc(x_28);
lean_inc_ref(x_31);
lean_inc(x_85);
x_86 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_24, x_23, x_11, x_2, x_21, x_85, x_31, x_28, x_27, x_35, x_37, x_30, x_29);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_84);
x_89 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_90 = lean_array_push(x_89, x_88);
x_91 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_90, x_87, x_31, x_28, x_27, x_35, x_37, x_30, x_29);
lean_dec(x_29);
lean_dec_ref(x_30);
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec_ref(x_27);
lean_dec(x_28);
lean_dec_ref(x_31);
lean_dec_ref(x_90);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
if (lean_is_scalar(x_17)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_17;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 0);
lean_inc(x_95);
lean_dec(x_91);
if (lean_is_scalar(x_17)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_17;
}
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_dec(x_17);
x_98 = !lean_is_exclusive(x_91);
if (x_98 == 0)
{
return x_91;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_91, 0);
lean_inc(x_99);
lean_dec(x_91);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_84);
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_17);
x_101 = !lean_is_exclusive(x_86);
if (x_101 == 0)
{
return x_86;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_86, 0);
lean_inc(x_102);
lean_dec(x_86);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_2);
x_104 = !lean_is_exclusive(x_83);
if (x_104 == 0)
{
return x_83;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_83, 0);
lean_inc(x_105);
lean_dec(x_83);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_2);
x_107 = !lean_is_exclusive(x_81);
if (x_107 == 0)
{
return x_81;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_81, 0);
lean_inc(x_108);
lean_dec(x_81);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_2);
x_110 = !lean_is_exclusive(x_42);
if (x_110 == 0)
{
return x_42;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_42, 0);
lean_inc(x_111);
lean_dec(x_42);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; 
lean_dec_ref(x_33);
lean_dec_ref(x_31);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_11);
lean_dec_ref(x_2);
x_113 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_39, x_34, x_35, x_37, x_30, x_29);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_113, 0);
if (lean_is_scalar(x_17)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_17;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_113, 0, x_116);
return x_113;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
lean_dec(x_113);
if (lean_is_scalar(x_17)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_17;
}
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
else
{
uint8_t x_120; 
lean_dec(x_17);
x_120 = !lean_is_exclusive(x_113);
if (x_120 == 0)
{
return x_113;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_113, 0);
lean_inc(x_121);
lean_dec(x_113);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_2);
x_123 = !lean_is_exclusive(x_40);
if (x_123 == 0)
{
return x_40;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_40, 0);
lean_inc(x_124);
lean_dec(x_40);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_2);
x_126 = !lean_is_exclusive(x_38);
if (x_126 == 0)
{
return x_38;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_38, 0);
lean_inc(x_127);
lean_dec(x_38);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
block_164:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_inc_ref(x_21);
x_141 = l_Array_toSubarray___redArg(x_21, x_139, x_140);
x_142 = l_Array_ofSubarray___redArg(x_141);
lean_dec_ref(x_141);
lean_inc(x_132);
lean_inc_ref(x_133);
lean_inc(x_138);
lean_inc_ref(x_137);
lean_inc_ref(x_142);
x_143 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_18, x_19, x_142, x_26, x_134, x_131, x_130, x_137, x_138, x_133, x_132);
lean_dec_ref(x_18);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_145 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_11);
if (x_145 == 0)
{
x_27 = x_130;
x_28 = x_131;
x_29 = x_132;
x_30 = x_133;
x_31 = x_134;
x_32 = lean_box(0);
x_33 = x_142;
x_34 = x_135;
x_35 = x_137;
x_36 = x_144;
x_37 = x_138;
goto block_129;
}
else
{
uint8_t x_146; 
x_146 = lean_nat_dec_eq(x_23, x_24);
if (x_146 == 0)
{
x_27 = x_130;
x_28 = x_131;
x_29 = x_132;
x_30 = x_133;
x_31 = x_134;
x_32 = lean_box(0);
x_33 = x_142;
x_34 = x_135;
x_35 = x_137;
x_36 = x_144;
x_37 = x_138;
goto block_129;
}
else
{
lean_object* x_147; 
lean_dec_ref(x_142);
lean_dec_ref(x_135);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_2);
x_147 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_131);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
lean_dec_ref(x_147);
x_148 = l_Lean_Compiler_LCNF_Simp_simp(x_144, x_134, x_131, x_130, x_137, x_138, x_133, x_132);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_alloc_ctor(1, 1, 0);
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
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
else
{
uint8_t x_155; 
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
else
{
uint8_t x_158; 
lean_dec(x_144);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_130);
x_158 = !lean_is_exclusive(x_147);
if (x_158 == 0)
{
return x_147;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_147, 0);
lean_inc(x_159);
lean_dec(x_147);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
}
}
else
{
uint8_t x_161; 
lean_dec_ref(x_142);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec_ref(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_2);
x_161 = !lean_is_exclusive(x_143);
if (x_161 == 0)
{
return x_143;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_143, 0);
lean_inc(x_162);
lean_dec(x_143);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
block_201:
{
if (x_26 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_inc_ref(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_19);
lean_inc_ref(x_18);
lean_dec(x_16);
lean_inc_ref(x_167);
lean_inc_ref(x_165);
lean_inc(x_166);
x_173 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(x_173, 0, x_166);
lean_closure_set(x_173, 1, x_25);
lean_closure_set(x_173, 2, x_165);
lean_closure_set(x_173, 3, x_167);
x_174 = lean_unsigned_to_nat(0u);
x_175 = lean_nat_dec_le(x_24, x_23);
if (x_175 == 0)
{
lean_inc(x_23);
x_130 = x_167;
x_131 = x_166;
x_132 = x_171;
x_133 = x_170;
x_134 = x_165;
x_135 = x_173;
x_136 = lean_box(0);
x_137 = x_168;
x_138 = x_169;
x_139 = x_174;
x_140 = x_23;
goto block_164;
}
else
{
lean_inc(x_24);
x_130 = x_167;
x_131 = x_166;
x_132 = x_171;
x_133 = x_170;
x_134 = x_165;
x_135 = x_173;
x_136 = lean_box(0);
x_137 = x_168;
x_138 = x_169;
x_139 = x_174;
x_140 = x_24;
goto block_164;
}
}
else
{
lean_object* x_176; 
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_17);
lean_inc(x_171);
lean_inc_ref(x_170);
lean_inc(x_169);
lean_inc_ref(x_168);
x_176 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_16, x_165, x_166, x_167, x_168, x_169, x_170, x_171);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec_ref(x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_178, x_166, x_169, x_170, x_171);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
lean_dec_ref(x_179);
x_180 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_166);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
lean_dec_ref(x_180);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_177);
lean_ctor_set(x_181, 1, x_2);
x_182 = l_Lean_Compiler_LCNF_Simp_simp(x_181, x_165, x_166, x_167, x_168, x_169, x_170, x_171);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_182, 0, x_185);
return x_182;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_182, 0);
lean_inc(x_186);
lean_dec(x_182);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
x_188 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
}
else
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_182);
if (x_189 == 0)
{
return x_182;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_182, 0);
lean_inc(x_190);
lean_dec(x_182);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_177);
lean_dec(x_171);
lean_dec_ref(x_170);
lean_dec(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec(x_166);
lean_dec_ref(x_165);
lean_dec_ref(x_2);
x_192 = !lean_is_exclusive(x_180);
if (x_192 == 0)
{
return x_180;
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_180, 0);
lean_inc(x_193);
lean_dec(x_180);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_177);
lean_dec(x_171);
lean_dec_ref(x_170);
lean_dec(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec(x_166);
lean_dec_ref(x_165);
lean_dec_ref(x_2);
x_195 = !lean_is_exclusive(x_179);
if (x_195 == 0)
{
return x_179;
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_179, 0);
lean_inc(x_196);
lean_dec(x_179);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_171);
lean_dec_ref(x_170);
lean_dec(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec(x_166);
lean_dec_ref(x_165);
lean_dec(x_11);
lean_dec_ref(x_2);
x_198 = !lean_is_exclusive(x_176);
if (x_198 == 0)
{
return x_176;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_176, 0);
lean_inc(x_199);
lean_dec(x_176);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
return x_200;
}
}
}
}
}
else
{
lean_object* x_220; 
lean_dec(x_15);
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
x_220 = lean_box(0);
lean_ctor_set(x_13, 0, x_220);
return x_13;
}
}
else
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_13, 0);
lean_inc(x_221);
lean_dec(x_13);
if (lean_obj_tag(x_221) == 1)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_223 = x_221;
} else {
 lean_dec_ref(x_221);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_222, 0);
x_225 = lean_ctor_get(x_222, 1);
x_226 = lean_ctor_get(x_222, 2);
x_227 = lean_ctor_get(x_222, 3);
x_228 = lean_ctor_get_uint8(x_222, sizeof(void*)*4 + 2);
x_229 = lean_array_get_size(x_227);
x_230 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_222);
lean_inc_ref(x_227);
lean_inc_ref(x_2);
lean_inc(x_11);
lean_inc(x_229);
lean_inc(x_230);
x_231 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 14, 5);
lean_closure_set(x_231, 0, x_230);
lean_closure_set(x_231, 1, x_229);
lean_closure_set(x_231, 2, x_11);
lean_closure_set(x_231, 3, x_2);
lean_closure_set(x_231, 4, x_227);
x_232 = lean_nat_dec_lt(x_229, x_230);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_397; lean_object* x_398; 
x_397 = lean_ctor_get(x_12, 0);
lean_inc(x_397);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_397);
x_398 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(x_228, x_397, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
x_400 = lean_ctor_get(x_3, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_401);
x_402 = lean_ctor_get(x_3, 2);
lean_inc(x_402);
x_403 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_403);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_404 = x_3;
} else {
 lean_dec_ref(x_3);
 x_404 = lean_box(0);
}
lean_inc(x_397);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_397);
lean_ctor_set(x_405, 1, x_402);
x_406 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_403, x_397, x_399);
if (lean_is_scalar(x_404)) {
 x_407 = lean_alloc_ctor(0, 4, 0);
} else {
 x_407 = x_404;
}
lean_ctor_set(x_407, 0, x_400);
lean_ctor_set(x_407, 1, x_401);
lean_ctor_set(x_407, 2, x_405);
lean_ctor_set(x_407, 3, x_406);
x_362 = x_407;
x_363 = x_4;
x_364 = x_5;
x_365 = x_6;
x_366 = x_7;
x_367 = x_8;
x_368 = x_9;
x_369 = lean_box(0);
goto block_396;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_397);
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_408 = lean_ctor_get(x_398, 0);
lean_inc(x_408);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 x_409 = x_398;
} else {
 lean_dec_ref(x_398);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 1, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_408);
return x_410;
}
}
else
{
lean_dec(x_12);
x_362 = x_3;
x_363 = x_4;
x_364 = x_5;
x_365 = x_6;
x_366 = x_7;
x_367 = x_8;
x_368 = x_9;
x_369 = lean_box(0);
goto block_396;
}
block_328:
{
lean_object* x_244; 
lean_inc(x_235);
lean_inc_ref(x_236);
lean_inc(x_243);
lean_inc_ref(x_241);
lean_inc_ref(x_233);
lean_inc(x_234);
lean_inc_ref(x_237);
x_244 = l_Lean_Compiler_LCNF_Simp_simp(x_242, x_237, x_234, x_233, x_241, x_243, x_236, x_235);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec_ref(x_244);
x_246 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_234);
if (lean_obj_tag(x_246) == 0)
{
uint8_t x_247; 
lean_dec_ref(x_246);
lean_inc(x_245);
x_247 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_245);
if (x_247 == 0)
{
lean_object* x_248; 
lean_dec_ref(x_240);
x_248 = l_Lean_Compiler_LCNF_inferAppType(x_226, x_239, x_241, x_243, x_236, x_235);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec_ref(x_248);
lean_inc(x_249);
x_250 = l_Lean_Expr_headBeta(x_249);
x_251 = l_Lean_Expr_isForall(x_250);
lean_dec_ref(x_250);
if (x_251 == 0)
{
lean_object* x_252; 
x_252 = l_Lean_Compiler_LCNF_mkAuxParam(x_249, x_232, x_241, x_243, x_236, x_235);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_235);
lean_inc_ref(x_236);
lean_inc(x_243);
lean_inc_ref(x_241);
lean_inc(x_254);
x_255 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_230, x_229, x_11, x_2, x_227, x_254, x_237, x_234, x_233, x_241, x_243, x_236, x_235);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
x_257 = lean_unsigned_to_nat(1u);
x_258 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_259 = lean_array_push(x_258, x_253);
x_260 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_261 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_259, x_256, x_260, x_241, x_243, x_236, x_235);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
lean_inc(x_262);
x_263 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_263, 0, x_262);
lean_closure_set(x_263, 1, x_257);
x_264 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_245, x_263, x_241, x_243, x_236, x_235);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 x_266 = x_264;
} else {
 lean_dec_ref(x_264);
 x_266 = lean_box(0);
}
x_267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_267, 0, x_262);
lean_ctor_set(x_267, 1, x_265);
if (lean_is_scalar(x_223)) {
 x_268 = lean_alloc_ctor(1, 1, 0);
} else {
 x_268 = x_223;
}
lean_ctor_set(x_268, 0, x_267);
if (lean_is_scalar(x_266)) {
 x_269 = lean_alloc_ctor(0, 1, 0);
} else {
 x_269 = x_266;
}
lean_ctor_set(x_269, 0, x_268);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_262);
lean_dec(x_223);
x_270 = lean_ctor_get(x_264, 0);
lean_inc(x_270);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 x_271 = x_264;
} else {
 lean_dec_ref(x_264);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 1, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_270);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_245);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_223);
x_273 = lean_ctor_get(x_261, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_274 = x_261;
} else {
 lean_dec_ref(x_261);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 1, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_273);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_253);
lean_dec(x_245);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_223);
x_276 = lean_ctor_get(x_255, 0);
lean_inc(x_276);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_277 = x_255;
} else {
 lean_dec_ref(x_255);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 1, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_245);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec(x_230);
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec(x_223);
lean_dec(x_11);
lean_dec_ref(x_2);
x_279 = lean_ctor_get(x_252, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 x_280 = x_252;
} else {
 lean_dec_ref(x_252);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_279);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_249);
x_282 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
x_283 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_284 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_282, x_245, x_283, x_241, x_243, x_236, x_235);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
lean_dec_ref(x_284);
lean_inc(x_235);
lean_inc_ref(x_236);
lean_inc(x_243);
lean_inc_ref(x_241);
x_286 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_285, x_241, x_243, x_236, x_235);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec_ref(x_286);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_235);
lean_inc_ref(x_236);
lean_inc(x_243);
lean_inc_ref(x_241);
lean_inc_ref(x_233);
lean_inc(x_234);
lean_inc_ref(x_237);
lean_inc(x_288);
x_289 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_230, x_229, x_11, x_2, x_227, x_288, x_237, x_234, x_233, x_241, x_243, x_236, x_235);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_287);
x_292 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_293 = lean_array_push(x_292, x_291);
x_294 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_293, x_290, x_237, x_234, x_233, x_241, x_243, x_236, x_235);
lean_dec(x_235);
lean_dec_ref(x_236);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_233);
lean_dec(x_234);
lean_dec_ref(x_237);
lean_dec_ref(x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_296 = x_294;
} else {
 lean_dec_ref(x_294);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_297 = x_223;
}
lean_ctor_set(x_297, 0, x_295);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(0, 1, 0);
} else {
 x_298 = x_296;
}
lean_ctor_set(x_298, 0, x_297);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_223);
x_299 = lean_ctor_get(x_294, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_300 = x_294;
} else {
 lean_dec_ref(x_294);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_287);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec(x_223);
x_302 = lean_ctor_get(x_289, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 x_303 = x_289;
} else {
 lean_dec_ref(x_289);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 1, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_302);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec(x_230);
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec(x_223);
lean_dec(x_11);
lean_dec_ref(x_2);
x_305 = lean_ctor_get(x_286, 0);
lean_inc(x_305);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 x_306 = x_286;
} else {
 lean_dec_ref(x_286);
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
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec(x_230);
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec(x_223);
lean_dec(x_11);
lean_dec_ref(x_2);
x_308 = lean_ctor_get(x_284, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 x_309 = x_284;
} else {
 lean_dec_ref(x_284);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 1, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_308);
return x_310;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_245);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec(x_230);
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec(x_223);
lean_dec(x_11);
lean_dec_ref(x_2);
x_311 = lean_ctor_get(x_248, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_312 = x_248;
} else {
 lean_dec_ref(x_248);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 1, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_311);
return x_313;
}
}
else
{
lean_object* x_314; 
lean_dec_ref(x_239);
lean_dec_ref(x_237);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec(x_230);
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec(x_11);
lean_dec_ref(x_2);
x_314 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_245, x_240, x_241, x_243, x_236, x_235);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 x_316 = x_314;
} else {
 lean_dec_ref(x_314);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_317 = lean_alloc_ctor(1, 1, 0);
} else {
 x_317 = x_223;
}
lean_ctor_set(x_317, 0, x_315);
if (lean_is_scalar(x_316)) {
 x_318 = lean_alloc_ctor(0, 1, 0);
} else {
 x_318 = x_316;
}
lean_ctor_set(x_318, 0, x_317);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_223);
x_319 = lean_ctor_get(x_314, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 x_320 = x_314;
} else {
 lean_dec_ref(x_314);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 1, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_319);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_245);
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_239);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec(x_230);
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec(x_223);
lean_dec(x_11);
lean_dec_ref(x_2);
x_322 = lean_ctor_get(x_246, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_323 = x_246;
} else {
 lean_dec_ref(x_246);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 1, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_322);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_243);
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_239);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec(x_230);
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec(x_223);
lean_dec(x_11);
lean_dec_ref(x_2);
x_325 = lean_ctor_get(x_244, 0);
lean_inc(x_325);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_326 = x_244;
} else {
 lean_dec_ref(x_244);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 1, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_325);
return x_327;
}
}
block_361:
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_inc_ref(x_227);
x_340 = l_Array_toSubarray___redArg(x_227, x_338, x_339);
x_341 = l_Array_ofSubarray___redArg(x_340);
lean_dec_ref(x_340);
lean_inc(x_331);
lean_inc_ref(x_332);
lean_inc(x_337);
lean_inc_ref(x_336);
lean_inc_ref(x_341);
x_342 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_224, x_225, x_341, x_232, x_333, x_330, x_329, x_336, x_337, x_332, x_331);
lean_dec_ref(x_224);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; uint8_t x_344; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec_ref(x_342);
x_344 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_11);
if (x_344 == 0)
{
x_233 = x_329;
x_234 = x_330;
x_235 = x_331;
x_236 = x_332;
x_237 = x_333;
x_238 = lean_box(0);
x_239 = x_341;
x_240 = x_334;
x_241 = x_336;
x_242 = x_343;
x_243 = x_337;
goto block_328;
}
else
{
uint8_t x_345; 
x_345 = lean_nat_dec_eq(x_229, x_230);
if (x_345 == 0)
{
x_233 = x_329;
x_234 = x_330;
x_235 = x_331;
x_236 = x_332;
x_237 = x_333;
x_238 = lean_box(0);
x_239 = x_341;
x_240 = x_334;
x_241 = x_336;
x_242 = x_343;
x_243 = x_337;
goto block_328;
}
else
{
lean_object* x_346; 
lean_dec_ref(x_341);
lean_dec_ref(x_334);
lean_dec(x_230);
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec(x_223);
lean_dec(x_11);
lean_dec_ref(x_2);
x_346 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_330);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; 
lean_dec_ref(x_346);
x_347 = l_Lean_Compiler_LCNF_Simp_simp(x_343, x_333, x_330, x_329, x_336, x_337, x_332, x_331);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 x_349 = x_347;
} else {
 lean_dec_ref(x_347);
 x_349 = lean_box(0);
}
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_348);
if (lean_is_scalar(x_349)) {
 x_351 = lean_alloc_ctor(0, 1, 0);
} else {
 x_351 = x_349;
}
lean_ctor_set(x_351, 0, x_350);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_347, 0);
lean_inc(x_352);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 x_353 = x_347;
} else {
 lean_dec_ref(x_347);
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
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_343);
lean_dec(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_333);
lean_dec_ref(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec_ref(x_329);
x_355 = lean_ctor_get(x_346, 0);
lean_inc(x_355);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_356 = x_346;
} else {
 lean_dec_ref(x_346);
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
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec_ref(x_341);
lean_dec(x_337);
lean_dec_ref(x_336);
lean_dec_ref(x_334);
lean_dec_ref(x_333);
lean_dec_ref(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec_ref(x_329);
lean_dec(x_230);
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec(x_223);
lean_dec(x_11);
lean_dec_ref(x_2);
x_358 = lean_ctor_get(x_342, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 x_359 = x_342;
} else {
 lean_dec_ref(x_342);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 1, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_358);
return x_360;
}
}
block_396:
{
if (x_232 == 0)
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; 
lean_inc_ref(x_227);
lean_inc_ref(x_226);
lean_inc_ref(x_225);
lean_inc_ref(x_224);
lean_dec(x_222);
lean_inc_ref(x_364);
lean_inc_ref(x_362);
lean_inc(x_363);
x_370 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(x_370, 0, x_363);
lean_closure_set(x_370, 1, x_231);
lean_closure_set(x_370, 2, x_362);
lean_closure_set(x_370, 3, x_364);
x_371 = lean_unsigned_to_nat(0u);
x_372 = lean_nat_dec_le(x_230, x_229);
if (x_372 == 0)
{
lean_inc(x_229);
x_329 = x_364;
x_330 = x_363;
x_331 = x_368;
x_332 = x_367;
x_333 = x_362;
x_334 = x_370;
x_335 = lean_box(0);
x_336 = x_365;
x_337 = x_366;
x_338 = x_371;
x_339 = x_229;
goto block_361;
}
else
{
lean_inc(x_230);
x_329 = x_364;
x_330 = x_363;
x_331 = x_368;
x_332 = x_367;
x_333 = x_362;
x_334 = x_370;
x_335 = lean_box(0);
x_336 = x_365;
x_337 = x_366;
x_338 = x_371;
x_339 = x_230;
goto block_361;
}
}
else
{
lean_object* x_373; 
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_223);
lean_inc(x_368);
lean_inc_ref(x_367);
lean_inc(x_366);
lean_inc_ref(x_365);
x_373 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_222, x_362, x_363, x_364, x_365, x_366, x_367, x_368);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
lean_dec_ref(x_373);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_375, x_363, x_366, x_367, x_368);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; 
lean_dec_ref(x_376);
x_377 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_363);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; 
lean_dec_ref(x_377);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_374);
lean_ctor_set(x_378, 1, x_2);
x_379 = l_Lean_Compiler_LCNF_Simp_simp(x_378, x_362, x_363, x_364, x_365, x_366, x_367, x_368);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_381 = x_379;
} else {
 lean_dec_ref(x_379);
 x_381 = lean_box(0);
}
x_382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_382, 0, x_380);
if (lean_is_scalar(x_381)) {
 x_383 = lean_alloc_ctor(0, 1, 0);
} else {
 x_383 = x_381;
}
lean_ctor_set(x_383, 0, x_382);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_ctor_get(x_379, 0);
lean_inc(x_384);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_385 = x_379;
} else {
 lean_dec_ref(x_379);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 1, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_384);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_374);
lean_dec(x_368);
lean_dec_ref(x_367);
lean_dec(x_366);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_2);
x_387 = lean_ctor_get(x_377, 0);
lean_inc(x_387);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_388 = x_377;
} else {
 lean_dec_ref(x_377);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 1, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_387);
return x_389;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_374);
lean_dec(x_368);
lean_dec_ref(x_367);
lean_dec(x_366);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_2);
x_390 = lean_ctor_get(x_376, 0);
lean_inc(x_390);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 x_391 = x_376;
} else {
 lean_dec_ref(x_376);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 1, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_390);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_368);
lean_dec_ref(x_367);
lean_dec(x_366);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec(x_11);
lean_dec_ref(x_2);
x_393 = lean_ctor_get(x_373, 0);
lean_inc(x_393);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 x_394 = x_373;
} else {
 lean_dec_ref(x_373);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 1, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_393);
return x_395;
}
}
}
}
else
{
lean_object* x_411; lean_object* x_412; 
lean_dec(x_221);
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
x_411 = lean_box(0);
x_412 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_412, 0, x_411);
return x_412;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; uint8_t x_122; 
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
if (lean_obj_tag(x_359) == 1)
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
else
{
lean_dec(x_359);
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
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc(x_198);
lean_inc_ref(x_197);
lean_inc_ref(x_200);
x_203 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_200, x_197, x_198, x_196, x_199);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
if (lean_obj_tag(x_204) == 1)
{
lean_object* x_205; lean_object* x_206; 
lean_dec_ref(x_200);
lean_inc_ref(x_192);
lean_dec_ref(x_1);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_195);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
lean_dec_ref(x_206);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc(x_198);
lean_inc_ref(x_197);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_193);
x_207 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_193, x_195, x_201, x_197, x_198, x_196, x_199);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_205, x_208, x_193, x_195, x_201, x_197, x_198, x_196, x_199);
lean_dec(x_199);
lean_dec_ref(x_196);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_201);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec(x_205);
return x_209;
}
else
{
lean_dec(x_205);
lean_dec_ref(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
return x_207;
}
}
else
{
uint8_t x_210; 
lean_dec(x_205);
lean_dec_ref(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
x_210 = !lean_is_exclusive(x_206);
if (x_210 == 0)
{
return x_206;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_206, 0);
lean_inc(x_211);
lean_dec(x_206);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
else
{
lean_object* x_213; 
lean_dec(x_204);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc(x_198);
lean_inc_ref(x_197);
lean_inc_ref(x_200);
x_213 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_200, x_193, x_195, x_197, x_198, x_196, x_199);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
if (lean_obj_tag(x_214) == 1)
{
uint8_t x_215; 
lean_dec_ref(x_200);
lean_inc_ref(x_192);
x_215 = !lean_is_exclusive(x_1);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_1, 1);
lean_dec(x_216);
x_217 = lean_ctor_get(x_1, 0);
lean_dec(x_217);
x_218 = lean_ctor_get(x_214, 0);
lean_inc(x_218);
lean_dec_ref(x_214);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_218);
x_2 = x_193;
x_3 = x_195;
x_4 = x_201;
x_5 = x_197;
x_6 = x_198;
x_7 = x_196;
x_8 = x_199;
goto _start;
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_1);
x_220 = lean_ctor_get(x_214, 0);
lean_inc(x_220);
lean_dec_ref(x_214);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_192);
x_1 = x_221;
x_2 = x_193;
x_3 = x_195;
x_4 = x_201;
x_5 = x_197;
x_6 = x_198;
x_7 = x_196;
x_8 = x_199;
goto _start;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_214);
x_223 = lean_ctor_get(x_200, 0);
x_224 = lean_ctor_get(x_200, 3);
x_225 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_224);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
if (lean_obj_tag(x_226) == 1)
{
lean_object* x_227; lean_object* x_228; 
lean_inc_ref(x_192);
lean_dec_ref(x_1);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
lean_inc(x_223);
x_228 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_223, x_227, x_195, x_198, x_196, x_199);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
lean_dec_ref(x_228);
x_229 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_198);
lean_dec_ref(x_200);
if (lean_obj_tag(x_229) == 0)
{
lean_dec_ref(x_229);
x_1 = x_192;
x_2 = x_193;
x_3 = x_195;
x_4 = x_201;
x_5 = x_197;
x_6 = x_198;
x_7 = x_196;
x_8 = x_199;
goto _start;
}
else
{
uint8_t x_231; 
lean_dec_ref(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
x_231 = !lean_is_exclusive(x_229);
if (x_231 == 0)
{
return x_229;
}
else
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_229, 0);
lean_inc(x_232);
lean_dec(x_229);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
}
}
else
{
uint8_t x_234; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
x_234 = !lean_is_exclusive(x_228);
if (x_234 == 0)
{
return x_228;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_228, 0);
lean_inc(x_235);
lean_dec(x_228);
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_235);
return x_236;
}
}
}
else
{
lean_object* x_237; 
lean_dec(x_226);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc(x_198);
lean_inc_ref(x_197);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_193);
lean_inc_ref(x_192);
lean_inc_ref(x_200);
x_237 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_200, x_192, x_193, x_195, x_201, x_197, x_198, x_196, x_199);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
if (lean_obj_tag(x_238) == 1)
{
lean_object* x_239; lean_object* x_240; 
lean_dec_ref(x_201);
lean_dec(x_199);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_198);
lean_dec(x_198);
lean_dec(x_195);
lean_dec_ref(x_200);
if (lean_obj_tag(x_240) == 0)
{
uint8_t x_241; 
x_241 = !lean_is_exclusive(x_240);
if (x_241 == 0)
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_240, 0);
lean_dec(x_242);
lean_ctor_set(x_240, 0, x_239);
return x_240;
}
else
{
lean_object* x_243; 
lean_dec(x_240);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_239);
return x_243;
}
}
else
{
uint8_t x_244; 
lean_dec(x_239);
x_244 = !lean_is_exclusive(x_240);
if (x_244 == 0)
{
return x_240;
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_240, 0);
lean_inc(x_245);
lean_dec(x_240);
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_245);
return x_246;
}
}
}
else
{
lean_object* x_247; 
lean_dec(x_238);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc(x_198);
lean_inc_ref(x_197);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_193);
lean_inc(x_224);
x_247 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_224, x_193, x_195, x_201, x_197, x_198, x_196, x_199);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_dec_ref(x_247);
if (lean_obj_tag(x_248) == 1)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_inc_ref(x_192);
lean_dec_ref(x_1);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec_ref(x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
lean_inc(x_223);
x_252 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_223, x_251, x_195, x_198, x_196, x_199);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; 
lean_dec_ref(x_252);
x_253 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_198);
lean_dec_ref(x_200);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; 
lean_dec_ref(x_253);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc(x_198);
lean_inc_ref(x_197);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_193);
x_254 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_193, x_195, x_201, x_197, x_198, x_196, x_199);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_250, x_255, x_193, x_195, x_201, x_197, x_198, x_196, x_199);
lean_dec(x_199);
lean_dec_ref(x_196);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_201);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec(x_250);
return x_256;
}
else
{
lean_dec(x_250);
lean_dec_ref(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
return x_254;
}
}
else
{
uint8_t x_257; 
lean_dec(x_250);
lean_dec_ref(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
x_257 = !lean_is_exclusive(x_253);
if (x_257 == 0)
{
return x_253;
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_253, 0);
lean_inc(x_258);
lean_dec(x_253);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_258);
return x_259;
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_250);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
x_260 = !lean_is_exclusive(x_252);
if (x_260 == 0)
{
return x_252;
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_252, 0);
lean_inc(x_261);
lean_dec(x_252);
x_262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_262, 0, x_261);
return x_262;
}
}
}
else
{
lean_object* x_263; 
lean_dec(x_248);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc(x_198);
lean_inc_ref(x_197);
lean_inc_ref(x_201);
lean_inc(x_195);
lean_inc_ref(x_193);
lean_inc_ref(x_192);
x_263 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_193, x_195, x_201, x_197, x_198, x_196, x_199);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
x_265 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_223, x_195);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
x_267 = lean_unbox(x_266);
lean_dec(x_266);
if (x_267 == 0)
{
lean_object* x_268; 
lean_dec_ref(x_201);
lean_dec(x_199);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_268 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_198);
lean_dec(x_198);
lean_dec(x_195);
lean_dec_ref(x_200);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_268, 0);
lean_dec(x_270);
lean_ctor_set(x_268, 0, x_264);
return x_268;
}
else
{
lean_object* x_271; 
lean_dec(x_268);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_264);
return x_271;
}
}
else
{
uint8_t x_272; 
lean_dec(x_264);
x_272 = !lean_is_exclusive(x_268);
if (x_272 == 0)
{
return x_268;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_268, 0);
lean_inc(x_273);
lean_dec(x_268);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
}
}
else
{
lean_object* x_275; 
lean_inc_ref(x_200);
x_275 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_200, x_193, x_195, x_201, x_197, x_198, x_196, x_199);
lean_dec(x_199);
lean_dec_ref(x_196);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_201);
lean_dec(x_195);
lean_dec_ref(x_193);
if (lean_obj_tag(x_275) == 0)
{
size_t x_276; size_t x_277; uint8_t x_278; 
lean_dec_ref(x_275);
x_276 = lean_ptr_addr(x_192);
x_277 = lean_ptr_addr(x_264);
x_278 = lean_usize_dec_eq(x_276, x_277);
if (x_278 == 0)
{
x_10 = lean_box(0);
x_11 = x_200;
x_12 = x_264;
x_13 = x_278;
goto block_17;
}
else
{
size_t x_279; size_t x_280; uint8_t x_281; 
x_279 = lean_ptr_addr(x_191);
x_280 = lean_ptr_addr(x_200);
x_281 = lean_usize_dec_eq(x_279, x_280);
x_10 = lean_box(0);
x_11 = x_200;
x_12 = x_264;
x_13 = x_281;
goto block_17;
}
}
else
{
uint8_t x_282; 
lean_dec(x_264);
lean_dec_ref(x_200);
lean_dec_ref(x_1);
x_282 = !lean_is_exclusive(x_275);
if (x_282 == 0)
{
return x_275;
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_275, 0);
lean_inc(x_283);
lean_dec(x_275);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_283);
return x_284;
}
}
}
}
else
{
uint8_t x_285; 
lean_dec(x_264);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_285 = !lean_is_exclusive(x_265);
if (x_285 == 0)
{
return x_265;
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_265, 0);
lean_inc(x_286);
lean_dec(x_265);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_286);
return x_287;
}
}
}
else
{
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
return x_263;
}
}
}
else
{
uint8_t x_288; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_288 = !lean_is_exclusive(x_247);
if (x_288 == 0)
{
return x_247;
}
else
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_247, 0);
lean_inc(x_289);
lean_dec(x_247);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
return x_290;
}
}
}
}
else
{
uint8_t x_291; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_291 = !lean_is_exclusive(x_237);
if (x_291 == 0)
{
return x_237;
}
else
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_237, 0);
lean_inc(x_292);
lean_dec(x_237);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
return x_293;
}
}
}
}
}
else
{
uint8_t x_294; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_294 = !lean_is_exclusive(x_213);
if (x_294 == 0)
{
return x_213;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_213, 0);
lean_inc(x_295);
lean_dec(x_213);
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
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
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
x_300 = lean_st_ref_take(x_195);
x_301 = !lean_is_exclusive(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_302 = lean_ctor_get(x_200, 0);
x_303 = lean_ctor_get(x_300, 0);
x_304 = lean_box(0);
lean_inc(x_302);
x_305 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_303, x_302, x_304);
lean_ctor_set(x_300, 0, x_305);
x_306 = lean_st_ref_set(x_195, x_300);
x_307 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_198);
lean_dec_ref(x_200);
if (lean_obj_tag(x_307) == 0)
{
lean_dec_ref(x_307);
x_1 = x_192;
x_2 = x_193;
x_3 = x_195;
x_4 = x_201;
x_5 = x_197;
x_6 = x_198;
x_7 = x_196;
x_8 = x_199;
goto _start;
}
else
{
uint8_t x_309; 
lean_dec_ref(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
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
x_312 = lean_ctor_get(x_200, 0);
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
x_324 = lean_st_ref_set(x_195, x_323);
x_325 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_198);
lean_dec_ref(x_200);
if (lean_obj_tag(x_325) == 0)
{
lean_dec_ref(x_325);
x_1 = x_192;
x_2 = x_193;
x_3 = x_195;
x_4 = x_201;
x_5 = x_197;
x_6 = x_198;
x_7 = x_196;
x_8 = x_199;
goto _start;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec_ref(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_193);
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
x_193 = x_334;
x_194 = lean_box(0);
x_195 = x_335;
x_196 = x_339;
x_197 = x_337;
x_198 = x_338;
x_199 = x_340;
x_200 = x_331;
x_201 = x_336;
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
x_193 = x_334;
x_194 = lean_box(0);
x_195 = x_335;
x_196 = x_339;
x_197 = x_337;
x_198 = x_338;
x_199 = x_340;
x_200 = x_331;
x_201 = x_336;
x_202 = x_342;
goto block_330;
}
else
{
x_193 = x_334;
x_194 = lean_box(0);
x_195 = x_335;
x_196 = x_339;
x_197 = x_337;
x_198 = x_338;
x_199 = x_340;
x_200 = x_331;
x_201 = x_336;
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
if (lean_obj_tag(x_411) == 1)
{
lean_object* x_412; 
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_390);
lean_dec_ref(x_1);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
lean_dec_ref(x_411);
x_1 = x_412;
goto _start;
}
else
{
lean_object* x_414; 
lean_dec(x_411);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_390);
x_414 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_390, x_3);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; uint8_t x_417; 
lean_dec_ref(x_414);
x_415 = lean_unsigned_to_nat(0u);
x_416 = lean_array_get_size(x_392);
x_417 = lean_nat_dec_lt(x_415, x_416);
if (x_417 == 0)
{
lean_dec(x_416);
lean_dec(x_3);
x_404 = lean_box(0);
goto block_409;
}
else
{
uint8_t x_418; 
x_418 = lean_nat_dec_le(x_416, x_416);
if (x_418 == 0)
{
lean_dec(x_416);
lean_dec(x_3);
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_419; size_t x_420; size_t x_421; lean_object* x_422; 
x_419 = lean_box(0);
x_420 = 0;
x_421 = lean_usize_of_nat(x_416);
lean_dec(x_416);
x_422 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_392, x_420, x_421, x_419, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_422) == 0)
{
lean_dec_ref(x_422);
x_404 = lean_box(0);
goto block_409;
}
else
{
uint8_t x_423; 
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_390);
lean_dec_ref(x_1);
x_423 = !lean_is_exclusive(x_422);
if (x_423 == 0)
{
return x_422;
}
else
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
lean_dec(x_422);
x_425 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_425, 0, x_424);
return x_425;
}
}
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_390);
lean_dec(x_3);
lean_dec_ref(x_1);
x_426 = !lean_is_exclusive(x_414);
if (x_426 == 0)
{
return x_414;
}
else
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_414, 0);
lean_inc(x_427);
lean_dec(x_414);
x_428 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_428, 0, x_427);
return x_428;
}
}
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
if (lean_obj_tag(x_436) == 1)
{
lean_object* x_437; 
lean_dec_ref(x_433);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
lean_dec_ref(x_436);
lean_ctor_set(x_434, 0, x_437);
return x_434;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_436);
x_438 = lean_st_ref_get(x_3);
x_439 = lean_ctor_get(x_433, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_433, 1);
lean_inc_ref(x_440);
x_441 = lean_ctor_get(x_433, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_433, 3);
lean_inc_ref(x_442);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_443 = x_433;
} else {
 lean_dec_ref(x_433);
 x_443 = lean_box(0);
}
x_444 = lean_ctor_get(x_438, 0);
lean_inc_ref(x_444);
lean_dec_ref(x_438);
lean_inc(x_441);
x_445 = l_Lean_Compiler_LCNF_normFVarImp(x_444, x_441, x_122);
lean_dec_ref(x_444);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 x_447 = x_445;
} else {
 lean_dec_ref(x_445);
 x_447 = lean_box(0);
}
x_448 = lean_st_ref_get(x_3);
x_449 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_442);
lean_inc(x_446);
x_450 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_446, x_122, x_449, x_442, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 x_452 = x_450;
} else {
 lean_dec_ref(x_450);
 x_452 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_453 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_451, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_463; uint8_t x_464; lean_object* x_468; lean_object* x_469; lean_object* x_481; uint8_t x_482; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 x_455 = x_453;
} else {
 lean_dec_ref(x_453);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_448, 0);
lean_inc_ref(x_456);
lean_dec_ref(x_448);
lean_inc_ref(x_440);
x_457 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_456, x_122, x_440);
lean_dec_ref(x_456);
x_481 = lean_array_get_size(x_454);
x_482 = lean_nat_dec_eq(x_481, x_189);
lean_dec(x_481);
if (x_482 == 0)
{
lean_free_object(x_434);
lean_dec(x_6);
x_468 = x_3;
x_469 = lean_box(0);
goto block_480;
}
else
{
lean_object* x_483; 
x_483 = lean_array_fget_borrowed(x_454, x_449);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_495; lean_object* x_496; uint8_t x_507; lean_object* x_508; uint8_t x_510; 
lean_free_object(x_434);
x_484 = lean_ctor_get(x_483, 1);
x_485 = lean_ctor_get(x_483, 2);
x_495 = lean_array_get_size(x_484);
x_510 = lean_nat_dec_lt(x_449, x_495);
if (x_510 == 0)
{
x_507 = x_122;
x_508 = lean_box(0);
goto block_509;
}
else
{
if (x_510 == 0)
{
x_507 = x_122;
x_508 = lean_box(0);
goto block_509;
}
else
{
size_t x_511; size_t x_512; lean_object* x_513; 
x_511 = 0;
x_512 = lean_usize_of_nat(x_495);
x_513 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_484, x_511, x_512, x_3);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; uint8_t x_515; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
lean_dec_ref(x_513);
x_515 = lean_unbox(x_514);
lean_dec(x_514);
x_507 = x_515;
x_508 = lean_box(0);
goto block_509;
}
else
{
uint8_t x_516; 
lean_dec(x_495);
lean_dec_ref(x_457);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_516 = !lean_is_exclusive(x_513);
if (x_516 == 0)
{
return x_513;
}
else
{
lean_object* x_517; lean_object* x_518; 
x_517 = lean_ctor_get(x_513, 0);
lean_inc(x_517);
lean_dec(x_513);
x_518 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_518, 0, x_517);
return x_518;
}
}
}
}
block_494:
{
lean_object* x_487; 
x_487 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_487) == 0)
{
uint8_t x_488; 
x_488 = !lean_is_exclusive(x_487);
if (x_488 == 0)
{
lean_object* x_489; 
x_489 = lean_ctor_get(x_487, 0);
lean_dec(x_489);
lean_ctor_set(x_487, 0, x_485);
return x_487;
}
else
{
lean_object* x_490; 
lean_dec(x_487);
x_490 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_490, 0, x_485);
return x_490;
}
}
else
{
uint8_t x_491; 
lean_dec_ref(x_485);
x_491 = !lean_is_exclusive(x_487);
if (x_491 == 0)
{
return x_487;
}
else
{
lean_object* x_492; lean_object* x_493; 
x_492 = lean_ctor_get(x_487, 0);
lean_inc(x_492);
lean_dec(x_487);
x_493 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_493, 0, x_492);
return x_493;
}
}
}
block_506:
{
uint8_t x_497; 
x_497 = lean_nat_dec_lt(x_449, x_495);
if (x_497 == 0)
{
lean_dec(x_495);
lean_dec_ref(x_484);
lean_dec(x_6);
x_486 = lean_box(0);
goto block_494;
}
else
{
uint8_t x_498; 
x_498 = lean_nat_dec_le(x_495, x_495);
if (x_498 == 0)
{
lean_dec(x_495);
lean_dec_ref(x_484);
lean_dec(x_6);
x_486 = lean_box(0);
goto block_494;
}
else
{
lean_object* x_499; size_t x_500; size_t x_501; lean_object* x_502; 
x_499 = lean_box(0);
x_500 = 0;
x_501 = lean_usize_of_nat(x_495);
lean_dec(x_495);
x_502 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_484, x_500, x_501, x_499, x_6);
lean_dec(x_6);
lean_dec_ref(x_484);
if (lean_obj_tag(x_502) == 0)
{
lean_dec_ref(x_502);
x_486 = lean_box(0);
goto block_494;
}
else
{
uint8_t x_503; 
lean_dec_ref(x_485);
lean_dec(x_3);
x_503 = !lean_is_exclusive(x_502);
if (x_503 == 0)
{
return x_502;
}
else
{
lean_object* x_504; lean_object* x_505; 
x_504 = lean_ctor_get(x_502, 0);
lean_inc(x_504);
lean_dec(x_502);
x_505 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_505, 0, x_504);
return x_505;
}
}
}
}
}
block_509:
{
if (x_507 == 0)
{
lean_inc_ref(x_485);
lean_inc_ref(x_484);
lean_dec_ref(x_457);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec_ref(x_1);
x_496 = lean_box(0);
goto block_506;
}
else
{
if (x_122 == 0)
{
lean_dec(x_495);
lean_dec(x_6);
x_468 = x_3;
x_469 = lean_box(0);
goto block_480;
}
else
{
lean_inc_ref(x_485);
lean_inc_ref(x_484);
lean_dec_ref(x_457);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec_ref(x_1);
x_496 = lean_box(0);
goto block_506;
}
}
}
}
else
{
lean_object* x_519; 
lean_inc_ref(x_483);
lean_dec_ref(x_457);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_519 = lean_ctor_get(x_483, 0);
lean_inc_ref(x_519);
lean_dec_ref(x_483);
lean_ctor_set(x_434, 0, x_519);
return x_434;
}
}
block_462:
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
if (lean_is_scalar(x_443)) {
 x_459 = lean_alloc_ctor(0, 4, 0);
} else {
 x_459 = x_443;
}
lean_ctor_set(x_459, 0, x_439);
lean_ctor_set(x_459, 1, x_457);
lean_ctor_set(x_459, 2, x_446);
lean_ctor_set(x_459, 3, x_454);
if (lean_is_scalar(x_447)) {
 x_460 = lean_alloc_ctor(4, 1, 0);
} else {
 x_460 = x_447;
 lean_ctor_set_tag(x_460, 4);
}
lean_ctor_set(x_460, 0, x_459);
if (lean_is_scalar(x_455)) {
 x_461 = lean_alloc_ctor(0, 1, 0);
} else {
 x_461 = x_455;
}
lean_ctor_set(x_461, 0, x_460);
return x_461;
}
block_467:
{
if (x_464 == 0)
{
lean_dec(x_452);
lean_dec(x_441);
lean_dec_ref(x_1);
x_458 = lean_box(0);
goto block_462;
}
else
{
uint8_t x_465; 
x_465 = l_Lean_instBEqFVarId_beq(x_441, x_446);
lean_dec(x_441);
if (x_465 == 0)
{
lean_dec(x_452);
lean_dec_ref(x_1);
x_458 = lean_box(0);
goto block_462;
}
else
{
lean_object* x_466; 
lean_dec_ref(x_457);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_443);
lean_dec(x_439);
if (lean_is_scalar(x_452)) {
 x_466 = lean_alloc_ctor(0, 1, 0);
} else {
 x_466 = x_452;
}
lean_ctor_set(x_466, 0, x_1);
return x_466;
}
}
}
block_480:
{
lean_object* x_470; 
lean_inc(x_446);
x_470 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_446, x_468);
lean_dec(x_468);
if (lean_obj_tag(x_470) == 0)
{
size_t x_471; size_t x_472; uint8_t x_473; 
lean_dec_ref(x_470);
x_471 = lean_ptr_addr(x_442);
lean_dec_ref(x_442);
x_472 = lean_ptr_addr(x_454);
x_473 = lean_usize_dec_eq(x_471, x_472);
if (x_473 == 0)
{
lean_dec_ref(x_440);
x_463 = lean_box(0);
x_464 = x_473;
goto block_467;
}
else
{
size_t x_474; size_t x_475; uint8_t x_476; 
x_474 = lean_ptr_addr(x_440);
lean_dec_ref(x_440);
x_475 = lean_ptr_addr(x_457);
x_476 = lean_usize_dec_eq(x_474, x_475);
x_463 = lean_box(0);
x_464 = x_476;
goto block_467;
}
}
else
{
uint8_t x_477; 
lean_dec_ref(x_457);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec_ref(x_1);
x_477 = !lean_is_exclusive(x_470);
if (x_477 == 0)
{
return x_470;
}
else
{
lean_object* x_478; lean_object* x_479; 
x_478 = lean_ctor_get(x_470, 0);
lean_inc(x_478);
lean_dec(x_470);
x_479 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_479, 0, x_478);
return x_479;
}
}
}
}
else
{
uint8_t x_520; 
lean_dec(x_452);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_free_object(x_434);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_520 = !lean_is_exclusive(x_453);
if (x_520 == 0)
{
return x_453;
}
else
{
lean_object* x_521; lean_object* x_522; 
x_521 = lean_ctor_get(x_453, 0);
lean_inc(x_521);
lean_dec(x_453);
x_522 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_522, 0, x_521);
return x_522;
}
}
}
else
{
uint8_t x_523; 
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_free_object(x_434);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_523 = !lean_is_exclusive(x_450);
if (x_523 == 0)
{
return x_450;
}
else
{
lean_object* x_524; lean_object* x_525; 
x_524 = lean_ctor_get(x_450, 0);
lean_inc(x_524);
lean_dec(x_450);
x_525 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_525, 0, x_524);
return x_525;
}
}
}
else
{
lean_object* x_526; 
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_free_object(x_434);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_526 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_526;
}
}
}
else
{
lean_object* x_527; 
x_527 = lean_ctor_get(x_434, 0);
lean_inc(x_527);
lean_dec(x_434);
if (lean_obj_tag(x_527) == 1)
{
lean_object* x_528; lean_object* x_529; 
lean_dec_ref(x_433);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
lean_dec_ref(x_527);
x_529 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_529, 0, x_528);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_527);
x_530 = lean_st_ref_get(x_3);
x_531 = lean_ctor_get(x_433, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_433, 1);
lean_inc_ref(x_532);
x_533 = lean_ctor_get(x_433, 2);
lean_inc(x_533);
x_534 = lean_ctor_get(x_433, 3);
lean_inc_ref(x_534);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_535 = x_433;
} else {
 lean_dec_ref(x_433);
 x_535 = lean_box(0);
}
x_536 = lean_ctor_get(x_530, 0);
lean_inc_ref(x_536);
lean_dec_ref(x_530);
lean_inc(x_533);
x_537 = l_Lean_Compiler_LCNF_normFVarImp(x_536, x_533, x_122);
lean_dec_ref(x_536);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 x_539 = x_537;
} else {
 lean_dec_ref(x_537);
 x_539 = lean_box(0);
}
x_540 = lean_st_ref_get(x_3);
x_541 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_534);
lean_inc(x_538);
x_542 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_538, x_122, x_541, x_534, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 x_544 = x_542;
} else {
 lean_dec_ref(x_542);
 x_544 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_545 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_543, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_555; uint8_t x_556; lean_object* x_560; lean_object* x_561; lean_object* x_573; uint8_t x_574; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 x_547 = x_545;
} else {
 lean_dec_ref(x_545);
 x_547 = lean_box(0);
}
x_548 = lean_ctor_get(x_540, 0);
lean_inc_ref(x_548);
lean_dec_ref(x_540);
lean_inc_ref(x_532);
x_549 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_548, x_122, x_532);
lean_dec_ref(x_548);
x_573 = lean_array_get_size(x_546);
x_574 = lean_nat_dec_eq(x_573, x_189);
lean_dec(x_573);
if (x_574 == 0)
{
lean_dec(x_6);
x_560 = x_3;
x_561 = lean_box(0);
goto block_572;
}
else
{
lean_object* x_575; 
x_575 = lean_array_fget_borrowed(x_546, x_541);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_586; lean_object* x_587; uint8_t x_598; lean_object* x_599; uint8_t x_601; 
x_576 = lean_ctor_get(x_575, 1);
x_577 = lean_ctor_get(x_575, 2);
x_586 = lean_array_get_size(x_576);
x_601 = lean_nat_dec_lt(x_541, x_586);
if (x_601 == 0)
{
x_598 = x_122;
x_599 = lean_box(0);
goto block_600;
}
else
{
if (x_601 == 0)
{
x_598 = x_122;
x_599 = lean_box(0);
goto block_600;
}
else
{
size_t x_602; size_t x_603; lean_object* x_604; 
x_602 = 0;
x_603 = lean_usize_of_nat(x_586);
x_604 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_576, x_602, x_603, x_3);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; uint8_t x_606; 
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
lean_dec_ref(x_604);
x_606 = lean_unbox(x_605);
lean_dec(x_605);
x_598 = x_606;
x_599 = lean_box(0);
goto block_600;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
lean_dec(x_586);
lean_dec_ref(x_549);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_544);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_535);
lean_dec_ref(x_534);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_607 = lean_ctor_get(x_604, 0);
lean_inc(x_607);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 x_608 = x_604;
} else {
 lean_dec_ref(x_604);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_609 = lean_alloc_ctor(1, 1, 0);
} else {
 x_609 = x_608;
}
lean_ctor_set(x_609, 0, x_607);
return x_609;
}
}
}
block_585:
{
lean_object* x_579; 
x_579 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; 
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 x_580 = x_579;
} else {
 lean_dec_ref(x_579);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_580)) {
 x_581 = lean_alloc_ctor(0, 1, 0);
} else {
 x_581 = x_580;
}
lean_ctor_set(x_581, 0, x_577);
return x_581;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_dec_ref(x_577);
x_582 = lean_ctor_get(x_579, 0);
lean_inc(x_582);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 x_583 = x_579;
} else {
 lean_dec_ref(x_579);
 x_583 = lean_box(0);
}
if (lean_is_scalar(x_583)) {
 x_584 = lean_alloc_ctor(1, 1, 0);
} else {
 x_584 = x_583;
}
lean_ctor_set(x_584, 0, x_582);
return x_584;
}
}
block_597:
{
uint8_t x_588; 
x_588 = lean_nat_dec_lt(x_541, x_586);
if (x_588 == 0)
{
lean_dec(x_586);
lean_dec_ref(x_576);
lean_dec(x_6);
x_578 = lean_box(0);
goto block_585;
}
else
{
uint8_t x_589; 
x_589 = lean_nat_dec_le(x_586, x_586);
if (x_589 == 0)
{
lean_dec(x_586);
lean_dec_ref(x_576);
lean_dec(x_6);
x_578 = lean_box(0);
goto block_585;
}
else
{
lean_object* x_590; size_t x_591; size_t x_592; lean_object* x_593; 
x_590 = lean_box(0);
x_591 = 0;
x_592 = lean_usize_of_nat(x_586);
lean_dec(x_586);
x_593 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_576, x_591, x_592, x_590, x_6);
lean_dec(x_6);
lean_dec_ref(x_576);
if (lean_obj_tag(x_593) == 0)
{
lean_dec_ref(x_593);
x_578 = lean_box(0);
goto block_585;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec_ref(x_577);
lean_dec(x_3);
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 x_595 = x_593;
} else {
 lean_dec_ref(x_593);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(1, 1, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_594);
return x_596;
}
}
}
}
block_600:
{
if (x_598 == 0)
{
lean_inc_ref(x_577);
lean_inc_ref(x_576);
lean_dec_ref(x_549);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_544);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_535);
lean_dec_ref(x_534);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_1);
x_587 = lean_box(0);
goto block_597;
}
else
{
if (x_122 == 0)
{
lean_dec(x_586);
lean_dec(x_6);
x_560 = x_3;
x_561 = lean_box(0);
goto block_572;
}
else
{
lean_inc_ref(x_577);
lean_inc_ref(x_576);
lean_dec_ref(x_549);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_544);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_535);
lean_dec_ref(x_534);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_1);
x_587 = lean_box(0);
goto block_597;
}
}
}
}
else
{
lean_object* x_610; lean_object* x_611; 
lean_inc_ref(x_575);
lean_dec_ref(x_549);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_544);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_535);
lean_dec_ref(x_534);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_610 = lean_ctor_get(x_575, 0);
lean_inc_ref(x_610);
lean_dec_ref(x_575);
x_611 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_611, 0, x_610);
return x_611;
}
}
block_554:
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
if (lean_is_scalar(x_535)) {
 x_551 = lean_alloc_ctor(0, 4, 0);
} else {
 x_551 = x_535;
}
lean_ctor_set(x_551, 0, x_531);
lean_ctor_set(x_551, 1, x_549);
lean_ctor_set(x_551, 2, x_538);
lean_ctor_set(x_551, 3, x_546);
if (lean_is_scalar(x_539)) {
 x_552 = lean_alloc_ctor(4, 1, 0);
} else {
 x_552 = x_539;
 lean_ctor_set_tag(x_552, 4);
}
lean_ctor_set(x_552, 0, x_551);
if (lean_is_scalar(x_547)) {
 x_553 = lean_alloc_ctor(0, 1, 0);
} else {
 x_553 = x_547;
}
lean_ctor_set(x_553, 0, x_552);
return x_553;
}
block_559:
{
if (x_556 == 0)
{
lean_dec(x_544);
lean_dec(x_533);
lean_dec_ref(x_1);
x_550 = lean_box(0);
goto block_554;
}
else
{
uint8_t x_557; 
x_557 = l_Lean_instBEqFVarId_beq(x_533, x_538);
lean_dec(x_533);
if (x_557 == 0)
{
lean_dec(x_544);
lean_dec_ref(x_1);
x_550 = lean_box(0);
goto block_554;
}
else
{
lean_object* x_558; 
lean_dec_ref(x_549);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_535);
lean_dec(x_531);
if (lean_is_scalar(x_544)) {
 x_558 = lean_alloc_ctor(0, 1, 0);
} else {
 x_558 = x_544;
}
lean_ctor_set(x_558, 0, x_1);
return x_558;
}
}
}
block_572:
{
lean_object* x_562; 
lean_inc(x_538);
x_562 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_538, x_560);
lean_dec(x_560);
if (lean_obj_tag(x_562) == 0)
{
size_t x_563; size_t x_564; uint8_t x_565; 
lean_dec_ref(x_562);
x_563 = lean_ptr_addr(x_534);
lean_dec_ref(x_534);
x_564 = lean_ptr_addr(x_546);
x_565 = lean_usize_dec_eq(x_563, x_564);
if (x_565 == 0)
{
lean_dec_ref(x_532);
x_555 = lean_box(0);
x_556 = x_565;
goto block_559;
}
else
{
size_t x_566; size_t x_567; uint8_t x_568; 
x_566 = lean_ptr_addr(x_532);
lean_dec_ref(x_532);
x_567 = lean_ptr_addr(x_549);
x_568 = lean_usize_dec_eq(x_566, x_567);
x_555 = lean_box(0);
x_556 = x_568;
goto block_559;
}
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
lean_dec_ref(x_549);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_544);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_535);
lean_dec_ref(x_534);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_1);
x_569 = lean_ctor_get(x_562, 0);
lean_inc(x_569);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 x_570 = x_562;
} else {
 lean_dec_ref(x_562);
 x_570 = lean_box(0);
}
if (lean_is_scalar(x_570)) {
 x_571 = lean_alloc_ctor(1, 1, 0);
} else {
 x_571 = x_570;
}
lean_ctor_set(x_571, 0, x_569);
return x_571;
}
}
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_dec(x_544);
lean_dec_ref(x_540);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_535);
lean_dec_ref(x_534);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_612 = lean_ctor_get(x_545, 0);
lean_inc(x_612);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 x_613 = x_545;
} else {
 lean_dec_ref(x_545);
 x_613 = lean_box(0);
}
if (lean_is_scalar(x_613)) {
 x_614 = lean_alloc_ctor(1, 1, 0);
} else {
 x_614 = x_613;
}
lean_ctor_set(x_614, 0, x_612);
return x_614;
}
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec_ref(x_540);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_535);
lean_dec_ref(x_534);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_615 = lean_ctor_get(x_542, 0);
lean_inc(x_615);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 x_616 = x_542;
} else {
 lean_dec_ref(x_542);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(1, 1, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_615);
return x_617;
}
}
else
{
lean_object* x_618; 
lean_dec(x_535);
lean_dec_ref(x_534);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_618 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_618;
}
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
x_89 = x_142;
x_90 = x_157;
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
x_89 = x_142;
x_90 = x_159;
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
x_89 = x_142;
x_90 = x_167;
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
if (lean_obj_tag(x_857) == 1)
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
else
{
lean_dec(x_857);
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
lean_inc(x_713);
lean_inc_ref(x_710);
lean_inc(x_712);
lean_inc_ref(x_711);
lean_inc_ref(x_714);
x_717 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_714, x_711, x_712, x_710, x_713);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
lean_dec_ref(x_717);
if (lean_obj_tag(x_718) == 1)
{
lean_object* x_719; lean_object* x_720; 
lean_dec_ref(x_714);
lean_inc_ref(x_706);
lean_dec_ref(x_1);
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
lean_dec_ref(x_718);
x_720 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_709);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; 
lean_dec_ref(x_720);
lean_inc(x_713);
lean_inc_ref(x_710);
lean_inc(x_712);
lean_inc_ref(x_711);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_707);
x_721 = l_Lean_Compiler_LCNF_Simp_simp(x_706, x_707, x_709, x_715, x_711, x_712, x_710, x_713);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
lean_dec_ref(x_721);
x_723 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_719, x_722, x_707, x_709, x_715, x_711, x_712, x_710, x_713);
lean_dec(x_713);
lean_dec_ref(x_710);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_715);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec(x_719);
return x_723;
}
else
{
lean_dec(x_719);
lean_dec_ref(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
return x_721;
}
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec(x_719);
lean_dec_ref(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec_ref(x_706);
x_724 = lean_ctor_get(x_720, 0);
lean_inc(x_724);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 x_725 = x_720;
} else {
 lean_dec_ref(x_720);
 x_725 = lean_box(0);
}
if (lean_is_scalar(x_725)) {
 x_726 = lean_alloc_ctor(1, 1, 0);
} else {
 x_726 = x_725;
}
lean_ctor_set(x_726, 0, x_724);
return x_726;
}
}
else
{
lean_object* x_727; 
lean_dec(x_718);
lean_inc(x_713);
lean_inc_ref(x_710);
lean_inc(x_712);
lean_inc_ref(x_711);
lean_inc_ref(x_714);
x_727 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_714, x_707, x_709, x_711, x_712, x_710, x_713);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
lean_dec_ref(x_727);
if (lean_obj_tag(x_728) == 1)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
lean_dec_ref(x_714);
lean_inc_ref(x_706);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_729 = x_1;
} else {
 lean_dec_ref(x_1);
 x_729 = lean_box(0);
}
x_730 = lean_ctor_get(x_728, 0);
lean_inc(x_730);
lean_dec_ref(x_728);
if (lean_is_scalar(x_729)) {
 x_731 = lean_alloc_ctor(1, 2, 0);
} else {
 x_731 = x_729;
 lean_ctor_set_tag(x_731, 1);
}
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_706);
x_1 = x_731;
x_2 = x_707;
x_3 = x_709;
x_4 = x_715;
x_5 = x_711;
x_6 = x_712;
x_7 = x_710;
x_8 = x_713;
goto _start;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
lean_dec(x_728);
x_733 = lean_ctor_get(x_714, 0);
x_734 = lean_ctor_get(x_714, 3);
x_735 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_734);
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
lean_dec_ref(x_735);
if (lean_obj_tag(x_736) == 1)
{
lean_object* x_737; lean_object* x_738; 
lean_inc_ref(x_706);
lean_dec_ref(x_1);
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
lean_dec_ref(x_736);
lean_inc(x_733);
x_738 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_733, x_737, x_709, x_712, x_710, x_713);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; 
lean_dec_ref(x_738);
x_739 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_714, x_709, x_712);
lean_dec_ref(x_714);
if (lean_obj_tag(x_739) == 0)
{
lean_dec_ref(x_739);
x_1 = x_706;
x_2 = x_707;
x_3 = x_709;
x_4 = x_715;
x_5 = x_711;
x_6 = x_712;
x_7 = x_710;
x_8 = x_713;
goto _start;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
lean_dec_ref(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec_ref(x_706);
x_741 = lean_ctor_get(x_739, 0);
lean_inc(x_741);
if (lean_is_exclusive(x_739)) {
 lean_ctor_release(x_739, 0);
 x_742 = x_739;
} else {
 lean_dec_ref(x_739);
 x_742 = lean_box(0);
}
if (lean_is_scalar(x_742)) {
 x_743 = lean_alloc_ctor(1, 1, 0);
} else {
 x_743 = x_742;
}
lean_ctor_set(x_743, 0, x_741);
return x_743;
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec_ref(x_706);
x_744 = lean_ctor_get(x_738, 0);
lean_inc(x_744);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 x_745 = x_738;
} else {
 lean_dec_ref(x_738);
 x_745 = lean_box(0);
}
if (lean_is_scalar(x_745)) {
 x_746 = lean_alloc_ctor(1, 1, 0);
} else {
 x_746 = x_745;
}
lean_ctor_set(x_746, 0, x_744);
return x_746;
}
}
else
{
lean_object* x_747; 
lean_dec(x_736);
lean_inc(x_713);
lean_inc_ref(x_710);
lean_inc(x_712);
lean_inc_ref(x_711);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_707);
lean_inc_ref(x_706);
lean_inc_ref(x_714);
x_747 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_714, x_706, x_707, x_709, x_715, x_711, x_712, x_710, x_713);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; 
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
lean_dec_ref(x_747);
if (lean_obj_tag(x_748) == 1)
{
lean_object* x_749; lean_object* x_750; 
lean_dec_ref(x_715);
lean_dec(x_713);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec_ref(x_707);
lean_dec_ref(x_1);
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
lean_dec_ref(x_748);
x_750 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_714, x_709, x_712);
lean_dec(x_712);
lean_dec(x_709);
lean_dec_ref(x_714);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; 
if (lean_is_exclusive(x_750)) {
 lean_ctor_release(x_750, 0);
 x_751 = x_750;
} else {
 lean_dec_ref(x_750);
 x_751 = lean_box(0);
}
if (lean_is_scalar(x_751)) {
 x_752 = lean_alloc_ctor(0, 1, 0);
} else {
 x_752 = x_751;
}
lean_ctor_set(x_752, 0, x_749);
return x_752;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
lean_dec(x_749);
x_753 = lean_ctor_get(x_750, 0);
lean_inc(x_753);
if (lean_is_exclusive(x_750)) {
 lean_ctor_release(x_750, 0);
 x_754 = x_750;
} else {
 lean_dec_ref(x_750);
 x_754 = lean_box(0);
}
if (lean_is_scalar(x_754)) {
 x_755 = lean_alloc_ctor(1, 1, 0);
} else {
 x_755 = x_754;
}
lean_ctor_set(x_755, 0, x_753);
return x_755;
}
}
else
{
lean_object* x_756; 
lean_dec(x_748);
lean_inc(x_713);
lean_inc_ref(x_710);
lean_inc(x_712);
lean_inc_ref(x_711);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_707);
lean_inc(x_734);
x_756 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_734, x_707, x_709, x_715, x_711, x_712, x_710, x_713);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; 
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
lean_dec_ref(x_756);
if (lean_obj_tag(x_757) == 1)
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
lean_inc_ref(x_706);
lean_dec_ref(x_1);
x_758 = lean_ctor_get(x_757, 0);
lean_inc(x_758);
lean_dec_ref(x_757);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
lean_inc(x_733);
x_761 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_733, x_760, x_709, x_712, x_710, x_713);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; 
lean_dec_ref(x_761);
x_762 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_714, x_709, x_712);
lean_dec_ref(x_714);
if (lean_obj_tag(x_762) == 0)
{
lean_object* x_763; 
lean_dec_ref(x_762);
lean_inc(x_713);
lean_inc_ref(x_710);
lean_inc(x_712);
lean_inc_ref(x_711);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_707);
x_763 = l_Lean_Compiler_LCNF_Simp_simp(x_706, x_707, x_709, x_715, x_711, x_712, x_710, x_713);
if (lean_obj_tag(x_763) == 0)
{
lean_object* x_764; lean_object* x_765; 
x_764 = lean_ctor_get(x_763, 0);
lean_inc(x_764);
lean_dec_ref(x_763);
x_765 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_759, x_764, x_707, x_709, x_715, x_711, x_712, x_710, x_713);
lean_dec(x_713);
lean_dec_ref(x_710);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_715);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec(x_759);
return x_765;
}
else
{
lean_dec(x_759);
lean_dec_ref(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
return x_763;
}
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_759);
lean_dec_ref(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec_ref(x_706);
x_766 = lean_ctor_get(x_762, 0);
lean_inc(x_766);
if (lean_is_exclusive(x_762)) {
 lean_ctor_release(x_762, 0);
 x_767 = x_762;
} else {
 lean_dec_ref(x_762);
 x_767 = lean_box(0);
}
if (lean_is_scalar(x_767)) {
 x_768 = lean_alloc_ctor(1, 1, 0);
} else {
 x_768 = x_767;
}
lean_ctor_set(x_768, 0, x_766);
return x_768;
}
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_759);
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec_ref(x_706);
x_769 = lean_ctor_get(x_761, 0);
lean_inc(x_769);
if (lean_is_exclusive(x_761)) {
 lean_ctor_release(x_761, 0);
 x_770 = x_761;
} else {
 lean_dec_ref(x_761);
 x_770 = lean_box(0);
}
if (lean_is_scalar(x_770)) {
 x_771 = lean_alloc_ctor(1, 1, 0);
} else {
 x_771 = x_770;
}
lean_ctor_set(x_771, 0, x_769);
return x_771;
}
}
else
{
lean_object* x_772; 
lean_dec(x_757);
lean_inc(x_713);
lean_inc_ref(x_710);
lean_inc(x_712);
lean_inc_ref(x_711);
lean_inc_ref(x_715);
lean_inc(x_709);
lean_inc_ref(x_707);
lean_inc_ref(x_706);
x_772 = l_Lean_Compiler_LCNF_Simp_simp(x_706, x_707, x_709, x_715, x_711, x_712, x_710, x_713);
if (lean_obj_tag(x_772) == 0)
{
lean_object* x_773; lean_object* x_774; 
x_773 = lean_ctor_get(x_772, 0);
lean_inc(x_773);
lean_dec_ref(x_772);
x_774 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_733, x_709);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; uint8_t x_776; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
lean_dec_ref(x_774);
x_776 = lean_unbox(x_775);
lean_dec(x_775);
if (x_776 == 0)
{
lean_object* x_777; 
lean_dec_ref(x_715);
lean_dec(x_713);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec_ref(x_707);
lean_dec_ref(x_1);
x_777 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_714, x_709, x_712);
lean_dec(x_712);
lean_dec(x_709);
lean_dec_ref(x_714);
if (lean_obj_tag(x_777) == 0)
{
lean_object* x_778; lean_object* x_779; 
if (lean_is_exclusive(x_777)) {
 lean_ctor_release(x_777, 0);
 x_778 = x_777;
} else {
 lean_dec_ref(x_777);
 x_778 = lean_box(0);
}
if (lean_is_scalar(x_778)) {
 x_779 = lean_alloc_ctor(0, 1, 0);
} else {
 x_779 = x_778;
}
lean_ctor_set(x_779, 0, x_773);
return x_779;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
lean_dec(x_773);
x_780 = lean_ctor_get(x_777, 0);
lean_inc(x_780);
if (lean_is_exclusive(x_777)) {
 lean_ctor_release(x_777, 0);
 x_781 = x_777;
} else {
 lean_dec_ref(x_777);
 x_781 = lean_box(0);
}
if (lean_is_scalar(x_781)) {
 x_782 = lean_alloc_ctor(1, 1, 0);
} else {
 x_782 = x_781;
}
lean_ctor_set(x_782, 0, x_780);
return x_782;
}
}
else
{
lean_object* x_783; 
lean_inc_ref(x_714);
x_783 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_714, x_707, x_709, x_715, x_711, x_712, x_710, x_713);
lean_dec(x_713);
lean_dec_ref(x_710);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_715);
lean_dec(x_709);
lean_dec_ref(x_707);
if (lean_obj_tag(x_783) == 0)
{
size_t x_784; size_t x_785; uint8_t x_786; 
lean_dec_ref(x_783);
x_784 = lean_ptr_addr(x_706);
x_785 = lean_ptr_addr(x_773);
x_786 = lean_usize_dec_eq(x_784, x_785);
if (x_786 == 0)
{
x_10 = lean_box(0);
x_11 = x_714;
x_12 = x_773;
x_13 = x_786;
goto block_17;
}
else
{
size_t x_787; size_t x_788; uint8_t x_789; 
x_787 = lean_ptr_addr(x_705);
x_788 = lean_ptr_addr(x_714);
x_789 = lean_usize_dec_eq(x_787, x_788);
x_10 = lean_box(0);
x_11 = x_714;
x_12 = x_773;
x_13 = x_789;
goto block_17;
}
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
lean_dec(x_773);
lean_dec_ref(x_714);
lean_dec_ref(x_1);
x_790 = lean_ctor_get(x_783, 0);
lean_inc(x_790);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 x_791 = x_783;
} else {
 lean_dec_ref(x_783);
 x_791 = lean_box(0);
}
if (lean_is_scalar(x_791)) {
 x_792 = lean_alloc_ctor(1, 1, 0);
} else {
 x_792 = x_791;
}
lean_ctor_set(x_792, 0, x_790);
return x_792;
}
}
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_773);
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec_ref(x_1);
x_793 = lean_ctor_get(x_774, 0);
lean_inc(x_793);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_794 = x_774;
} else {
 lean_dec_ref(x_774);
 x_794 = lean_box(0);
}
if (lean_is_scalar(x_794)) {
 x_795 = lean_alloc_ctor(1, 1, 0);
} else {
 x_795 = x_794;
}
lean_ctor_set(x_795, 0, x_793);
return x_795;
}
}
else
{
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec_ref(x_1);
return x_772;
}
}
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec_ref(x_1);
x_796 = lean_ctor_get(x_756, 0);
lean_inc(x_796);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 x_797 = x_756;
} else {
 lean_dec_ref(x_756);
 x_797 = lean_box(0);
}
if (lean_is_scalar(x_797)) {
 x_798 = lean_alloc_ctor(1, 1, 0);
} else {
 x_798 = x_797;
}
lean_ctor_set(x_798, 0, x_796);
return x_798;
}
}
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec_ref(x_1);
x_799 = lean_ctor_get(x_747, 0);
lean_inc(x_799);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 x_800 = x_747;
} else {
 lean_dec_ref(x_747);
 x_800 = lean_box(0);
}
if (lean_is_scalar(x_800)) {
 x_801 = lean_alloc_ctor(1, 1, 0);
} else {
 x_801 = x_800;
}
lean_ctor_set(x_801, 0, x_799);
return x_801;
}
}
}
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
lean_dec_ref(x_1);
x_802 = lean_ctor_get(x_727, 0);
lean_inc(x_802);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 x_803 = x_727;
} else {
 lean_dec_ref(x_727);
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
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
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
x_808 = lean_st_ref_take(x_709);
x_809 = lean_ctor_get(x_714, 0);
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
x_822 = lean_st_ref_set(x_709, x_821);
x_823 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_714, x_709, x_712);
lean_dec_ref(x_714);
if (lean_obj_tag(x_823) == 0)
{
lean_dec_ref(x_823);
x_1 = x_706;
x_2 = x_707;
x_3 = x_709;
x_4 = x_715;
x_5 = x_711;
x_6 = x_712;
x_7 = x_710;
x_8 = x_713;
goto _start;
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
lean_dec_ref(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_710);
lean_dec(x_709);
lean_dec_ref(x_707);
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
x_707 = x_832;
x_708 = lean_box(0);
x_709 = x_833;
x_710 = x_837;
x_711 = x_835;
x_712 = x_836;
x_713 = x_838;
x_714 = x_829;
x_715 = x_834;
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
x_707 = x_832;
x_708 = lean_box(0);
x_709 = x_833;
x_710 = x_837;
x_711 = x_835;
x_712 = x_836;
x_713 = x_838;
x_714 = x_829;
x_715 = x_834;
x_716 = x_840;
goto block_828;
}
else
{
x_707 = x_832;
x_708 = lean_box(0);
x_709 = x_833;
x_710 = x_837;
x_711 = x_835;
x_712 = x_836;
x_713 = x_838;
x_714 = x_829;
x_715 = x_834;
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
if (lean_obj_tag(x_906) == 1)
{
lean_object* x_907; 
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_888);
lean_dec_ref(x_1);
x_907 = lean_ctor_get(x_906, 0);
lean_inc(x_907);
lean_dec_ref(x_906);
x_1 = x_907;
goto _start;
}
else
{
lean_object* x_909; 
lean_dec(x_906);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_888);
x_909 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_888, x_3);
if (lean_obj_tag(x_909) == 0)
{
lean_object* x_910; lean_object* x_911; uint8_t x_912; 
lean_dec_ref(x_909);
x_910 = lean_unsigned_to_nat(0u);
x_911 = lean_array_get_size(x_890);
x_912 = lean_nat_dec_lt(x_910, x_911);
if (x_912 == 0)
{
lean_dec(x_911);
lean_dec(x_3);
x_899 = lean_box(0);
goto block_904;
}
else
{
uint8_t x_913; 
x_913 = lean_nat_dec_le(x_911, x_911);
if (x_913 == 0)
{
lean_dec(x_911);
lean_dec(x_3);
x_899 = lean_box(0);
goto block_904;
}
else
{
lean_object* x_914; size_t x_915; size_t x_916; lean_object* x_917; 
x_914 = lean_box(0);
x_915 = 0;
x_916 = lean_usize_of_nat(x_911);
lean_dec(x_911);
x_917 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_890, x_915, x_916, x_914, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_917) == 0)
{
lean_dec_ref(x_917);
x_899 = lean_box(0);
goto block_904;
}
else
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; 
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_888);
lean_dec_ref(x_1);
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 x_919 = x_917;
} else {
 lean_dec_ref(x_917);
 x_919 = lean_box(0);
}
if (lean_is_scalar(x_919)) {
 x_920 = lean_alloc_ctor(1, 1, 0);
} else {
 x_920 = x_919;
}
lean_ctor_set(x_920, 0, x_918);
return x_920;
}
}
}
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; 
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_888);
lean_dec(x_3);
lean_dec_ref(x_1);
x_921 = lean_ctor_get(x_909, 0);
lean_inc(x_921);
if (lean_is_exclusive(x_909)) {
 lean_ctor_release(x_909, 0);
 x_922 = x_909;
} else {
 lean_dec_ref(x_909);
 x_922 = lean_box(0);
}
if (lean_is_scalar(x_922)) {
 x_923 = lean_alloc_ctor(1, 1, 0);
} else {
 x_923 = x_922;
}
lean_ctor_set(x_923, 0, x_921);
return x_923;
}
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
if (lean_obj_tag(x_930) == 1)
{
lean_object* x_932; lean_object* x_933; 
lean_dec_ref(x_928);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_932 = lean_ctor_get(x_930, 0);
lean_inc(x_932);
lean_dec_ref(x_930);
if (lean_is_scalar(x_931)) {
 x_933 = lean_alloc_ctor(0, 1, 0);
} else {
 x_933 = x_931;
}
lean_ctor_set(x_933, 0, x_932);
return x_933;
}
else
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec(x_930);
x_934 = lean_st_ref_get(x_3);
x_935 = lean_ctor_get(x_928, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_928, 1);
lean_inc_ref(x_936);
x_937 = lean_ctor_get(x_928, 2);
lean_inc(x_937);
x_938 = lean_ctor_get(x_928, 3);
lean_inc_ref(x_938);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 lean_ctor_release(x_928, 2);
 lean_ctor_release(x_928, 3);
 x_939 = x_928;
} else {
 lean_dec_ref(x_928);
 x_939 = lean_box(0);
}
x_940 = lean_ctor_get(x_934, 0);
lean_inc_ref(x_940);
lean_dec_ref(x_934);
lean_inc(x_937);
x_941 = l_Lean_Compiler_LCNF_normFVarImp(x_940, x_937, x_122);
lean_dec_ref(x_940);
if (lean_obj_tag(x_941) == 0)
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; 
x_942 = lean_ctor_get(x_941, 0);
lean_inc(x_942);
if (lean_is_exclusive(x_941)) {
 lean_ctor_release(x_941, 0);
 x_943 = x_941;
} else {
 lean_dec_ref(x_941);
 x_943 = lean_box(0);
}
x_944 = lean_st_ref_get(x_3);
x_945 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_938);
lean_inc(x_942);
x_946 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_942, x_122, x_945, x_938, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_946) == 0)
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_947 = lean_ctor_get(x_946, 0);
lean_inc(x_947);
if (lean_is_exclusive(x_946)) {
 lean_ctor_release(x_946, 0);
 x_948 = x_946;
} else {
 lean_dec_ref(x_946);
 x_948 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_949 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_947, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_949) == 0)
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_959; uint8_t x_960; lean_object* x_964; lean_object* x_965; lean_object* x_977; uint8_t x_978; 
x_950 = lean_ctor_get(x_949, 0);
lean_inc(x_950);
if (lean_is_exclusive(x_949)) {
 lean_ctor_release(x_949, 0);
 x_951 = x_949;
} else {
 lean_dec_ref(x_949);
 x_951 = lean_box(0);
}
x_952 = lean_ctor_get(x_944, 0);
lean_inc_ref(x_952);
lean_dec_ref(x_944);
lean_inc_ref(x_936);
x_953 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_952, x_122, x_936);
lean_dec_ref(x_952);
x_977 = lean_array_get_size(x_950);
x_978 = lean_nat_dec_eq(x_977, x_703);
lean_dec(x_977);
if (x_978 == 0)
{
lean_dec(x_931);
lean_dec(x_6);
x_964 = x_3;
x_965 = lean_box(0);
goto block_976;
}
else
{
lean_object* x_979; 
x_979 = lean_array_fget_borrowed(x_950, x_945);
if (lean_obj_tag(x_979) == 0)
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_990; lean_object* x_991; uint8_t x_1002; lean_object* x_1003; uint8_t x_1005; 
lean_dec(x_931);
x_980 = lean_ctor_get(x_979, 1);
x_981 = lean_ctor_get(x_979, 2);
x_990 = lean_array_get_size(x_980);
x_1005 = lean_nat_dec_lt(x_945, x_990);
if (x_1005 == 0)
{
x_1002 = x_122;
x_1003 = lean_box(0);
goto block_1004;
}
else
{
if (x_1005 == 0)
{
x_1002 = x_122;
x_1003 = lean_box(0);
goto block_1004;
}
else
{
size_t x_1006; size_t x_1007; lean_object* x_1008; 
x_1006 = 0;
x_1007 = lean_usize_of_nat(x_990);
x_1008 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_980, x_1006, x_1007, x_3);
if (lean_obj_tag(x_1008) == 0)
{
lean_object* x_1009; uint8_t x_1010; 
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
lean_dec_ref(x_1008);
x_1010 = lean_unbox(x_1009);
lean_dec(x_1009);
x_1002 = x_1010;
x_1003 = lean_box(0);
goto block_1004;
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
lean_dec(x_990);
lean_dec_ref(x_953);
lean_dec(x_951);
lean_dec(x_950);
lean_dec(x_948);
lean_dec(x_943);
lean_dec(x_942);
lean_dec(x_939);
lean_dec_ref(x_938);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1011 = lean_ctor_get(x_1008, 0);
lean_inc(x_1011);
if (lean_is_exclusive(x_1008)) {
 lean_ctor_release(x_1008, 0);
 x_1012 = x_1008;
} else {
 lean_dec_ref(x_1008);
 x_1012 = lean_box(0);
}
if (lean_is_scalar(x_1012)) {
 x_1013 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1013 = x_1012;
}
lean_ctor_set(x_1013, 0, x_1011);
return x_1013;
}
}
}
block_989:
{
lean_object* x_983; 
x_983 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_983) == 0)
{
lean_object* x_984; lean_object* x_985; 
if (lean_is_exclusive(x_983)) {
 lean_ctor_release(x_983, 0);
 x_984 = x_983;
} else {
 lean_dec_ref(x_983);
 x_984 = lean_box(0);
}
if (lean_is_scalar(x_984)) {
 x_985 = lean_alloc_ctor(0, 1, 0);
} else {
 x_985 = x_984;
}
lean_ctor_set(x_985, 0, x_981);
return x_985;
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec_ref(x_981);
x_986 = lean_ctor_get(x_983, 0);
lean_inc(x_986);
if (lean_is_exclusive(x_983)) {
 lean_ctor_release(x_983, 0);
 x_987 = x_983;
} else {
 lean_dec_ref(x_983);
 x_987 = lean_box(0);
}
if (lean_is_scalar(x_987)) {
 x_988 = lean_alloc_ctor(1, 1, 0);
} else {
 x_988 = x_987;
}
lean_ctor_set(x_988, 0, x_986);
return x_988;
}
}
block_1001:
{
uint8_t x_992; 
x_992 = lean_nat_dec_lt(x_945, x_990);
if (x_992 == 0)
{
lean_dec(x_990);
lean_dec_ref(x_980);
lean_dec(x_6);
x_982 = lean_box(0);
goto block_989;
}
else
{
uint8_t x_993; 
x_993 = lean_nat_dec_le(x_990, x_990);
if (x_993 == 0)
{
lean_dec(x_990);
lean_dec_ref(x_980);
lean_dec(x_6);
x_982 = lean_box(0);
goto block_989;
}
else
{
lean_object* x_994; size_t x_995; size_t x_996; lean_object* x_997; 
x_994 = lean_box(0);
x_995 = 0;
x_996 = lean_usize_of_nat(x_990);
lean_dec(x_990);
x_997 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_980, x_995, x_996, x_994, x_6);
lean_dec(x_6);
lean_dec_ref(x_980);
if (lean_obj_tag(x_997) == 0)
{
lean_dec_ref(x_997);
x_982 = lean_box(0);
goto block_989;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
lean_dec_ref(x_981);
lean_dec(x_3);
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
if (lean_is_exclusive(x_997)) {
 lean_ctor_release(x_997, 0);
 x_999 = x_997;
} else {
 lean_dec_ref(x_997);
 x_999 = lean_box(0);
}
if (lean_is_scalar(x_999)) {
 x_1000 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1000 = x_999;
}
lean_ctor_set(x_1000, 0, x_998);
return x_1000;
}
}
}
}
block_1004:
{
if (x_1002 == 0)
{
lean_inc_ref(x_981);
lean_inc_ref(x_980);
lean_dec_ref(x_953);
lean_dec(x_951);
lean_dec(x_950);
lean_dec(x_948);
lean_dec(x_943);
lean_dec(x_942);
lean_dec(x_939);
lean_dec_ref(x_938);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec_ref(x_1);
x_991 = lean_box(0);
goto block_1001;
}
else
{
if (x_122 == 0)
{
lean_dec(x_990);
lean_dec(x_6);
x_964 = x_3;
x_965 = lean_box(0);
goto block_976;
}
else
{
lean_inc_ref(x_981);
lean_inc_ref(x_980);
lean_dec_ref(x_953);
lean_dec(x_951);
lean_dec(x_950);
lean_dec(x_948);
lean_dec(x_943);
lean_dec(x_942);
lean_dec(x_939);
lean_dec_ref(x_938);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec_ref(x_1);
x_991 = lean_box(0);
goto block_1001;
}
}
}
}
else
{
lean_object* x_1014; lean_object* x_1015; 
lean_inc_ref(x_979);
lean_dec_ref(x_953);
lean_dec(x_951);
lean_dec(x_950);
lean_dec(x_948);
lean_dec(x_943);
lean_dec(x_942);
lean_dec(x_939);
lean_dec_ref(x_938);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1014 = lean_ctor_get(x_979, 0);
lean_inc_ref(x_1014);
lean_dec_ref(x_979);
if (lean_is_scalar(x_931)) {
 x_1015 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1015 = x_931;
}
lean_ctor_set(x_1015, 0, x_1014);
return x_1015;
}
}
block_958:
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; 
if (lean_is_scalar(x_939)) {
 x_955 = lean_alloc_ctor(0, 4, 0);
} else {
 x_955 = x_939;
}
lean_ctor_set(x_955, 0, x_935);
lean_ctor_set(x_955, 1, x_953);
lean_ctor_set(x_955, 2, x_942);
lean_ctor_set(x_955, 3, x_950);
if (lean_is_scalar(x_943)) {
 x_956 = lean_alloc_ctor(4, 1, 0);
} else {
 x_956 = x_943;
 lean_ctor_set_tag(x_956, 4);
}
lean_ctor_set(x_956, 0, x_955);
if (lean_is_scalar(x_951)) {
 x_957 = lean_alloc_ctor(0, 1, 0);
} else {
 x_957 = x_951;
}
lean_ctor_set(x_957, 0, x_956);
return x_957;
}
block_963:
{
if (x_960 == 0)
{
lean_dec(x_948);
lean_dec(x_937);
lean_dec_ref(x_1);
x_954 = lean_box(0);
goto block_958;
}
else
{
uint8_t x_961; 
x_961 = l_Lean_instBEqFVarId_beq(x_937, x_942);
lean_dec(x_937);
if (x_961 == 0)
{
lean_dec(x_948);
lean_dec_ref(x_1);
x_954 = lean_box(0);
goto block_958;
}
else
{
lean_object* x_962; 
lean_dec_ref(x_953);
lean_dec(x_951);
lean_dec(x_950);
lean_dec(x_943);
lean_dec(x_942);
lean_dec(x_939);
lean_dec(x_935);
if (lean_is_scalar(x_948)) {
 x_962 = lean_alloc_ctor(0, 1, 0);
} else {
 x_962 = x_948;
}
lean_ctor_set(x_962, 0, x_1);
return x_962;
}
}
}
block_976:
{
lean_object* x_966; 
lean_inc(x_942);
x_966 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_942, x_964);
lean_dec(x_964);
if (lean_obj_tag(x_966) == 0)
{
size_t x_967; size_t x_968; uint8_t x_969; 
lean_dec_ref(x_966);
x_967 = lean_ptr_addr(x_938);
lean_dec_ref(x_938);
x_968 = lean_ptr_addr(x_950);
x_969 = lean_usize_dec_eq(x_967, x_968);
if (x_969 == 0)
{
lean_dec_ref(x_936);
x_959 = lean_box(0);
x_960 = x_969;
goto block_963;
}
else
{
size_t x_970; size_t x_971; uint8_t x_972; 
x_970 = lean_ptr_addr(x_936);
lean_dec_ref(x_936);
x_971 = lean_ptr_addr(x_953);
x_972 = lean_usize_dec_eq(x_970, x_971);
x_959 = lean_box(0);
x_960 = x_972;
goto block_963;
}
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; 
lean_dec_ref(x_953);
lean_dec(x_951);
lean_dec(x_950);
lean_dec(x_948);
lean_dec(x_943);
lean_dec(x_942);
lean_dec(x_939);
lean_dec_ref(x_938);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec_ref(x_1);
x_973 = lean_ctor_get(x_966, 0);
lean_inc(x_973);
if (lean_is_exclusive(x_966)) {
 lean_ctor_release(x_966, 0);
 x_974 = x_966;
} else {
 lean_dec_ref(x_966);
 x_974 = lean_box(0);
}
if (lean_is_scalar(x_974)) {
 x_975 = lean_alloc_ctor(1, 1, 0);
} else {
 x_975 = x_974;
}
lean_ctor_set(x_975, 0, x_973);
return x_975;
}
}
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
lean_dec(x_948);
lean_dec_ref(x_944);
lean_dec(x_943);
lean_dec(x_942);
lean_dec(x_939);
lean_dec_ref(x_938);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec(x_931);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1016 = lean_ctor_get(x_949, 0);
lean_inc(x_1016);
if (lean_is_exclusive(x_949)) {
 lean_ctor_release(x_949, 0);
 x_1017 = x_949;
} else {
 lean_dec_ref(x_949);
 x_1017 = lean_box(0);
}
if (lean_is_scalar(x_1017)) {
 x_1018 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1018 = x_1017;
}
lean_ctor_set(x_1018, 0, x_1016);
return x_1018;
}
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
lean_dec_ref(x_944);
lean_dec(x_943);
lean_dec(x_942);
lean_dec(x_939);
lean_dec_ref(x_938);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec(x_931);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1019 = lean_ctor_get(x_946, 0);
lean_inc(x_1019);
if (lean_is_exclusive(x_946)) {
 lean_ctor_release(x_946, 0);
 x_1020 = x_946;
} else {
 lean_dec_ref(x_946);
 x_1020 = lean_box(0);
}
if (lean_is_scalar(x_1020)) {
 x_1021 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1021 = x_1020;
}
lean_ctor_set(x_1021, 0, x_1019);
return x_1021;
}
}
else
{
lean_object* x_1022; 
lean_dec(x_939);
lean_dec_ref(x_938);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec(x_935);
lean_dec(x_931);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1022 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1022;
}
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
x_89 = x_656;
x_90 = x_671;
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
x_89 = x_656;
x_90 = x_673;
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
x_89 = x_656;
x_90 = x_681;
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
if (lean_obj_tag(x_1263) == 1)
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
else
{
lean_dec(x_1263);
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
lean_inc(x_1119);
lean_inc_ref(x_1116);
lean_inc(x_1118);
lean_inc_ref(x_1117);
lean_inc_ref(x_1120);
x_1123 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_1120, x_1117, x_1118, x_1116, x_1119);
if (lean_obj_tag(x_1123) == 0)
{
lean_object* x_1124; 
x_1124 = lean_ctor_get(x_1123, 0);
lean_inc(x_1124);
lean_dec_ref(x_1123);
if (lean_obj_tag(x_1124) == 1)
{
lean_object* x_1125; lean_object* x_1126; 
lean_dec_ref(x_1120);
lean_inc_ref(x_1112);
lean_dec_ref(x_1);
x_1125 = lean_ctor_get(x_1124, 0);
lean_inc(x_1125);
lean_dec_ref(x_1124);
x_1126 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1115);
if (lean_obj_tag(x_1126) == 0)
{
lean_object* x_1127; 
lean_dec_ref(x_1126);
lean_inc(x_1119);
lean_inc_ref(x_1116);
lean_inc(x_1118);
lean_inc_ref(x_1117);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1113);
x_1127 = l_Lean_Compiler_LCNF_Simp_simp(x_1112, x_1113, x_1115, x_1121, x_1117, x_1118, x_1116, x_1119);
if (lean_obj_tag(x_1127) == 0)
{
lean_object* x_1128; lean_object* x_1129; 
x_1128 = lean_ctor_get(x_1127, 0);
lean_inc(x_1128);
lean_dec_ref(x_1127);
x_1129 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1125, x_1128, x_1113, x_1115, x_1121, x_1117, x_1118, x_1116, x_1119);
lean_dec(x_1119);
lean_dec_ref(x_1116);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1121);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec(x_1125);
return x_1129;
}
else
{
lean_dec(x_1125);
lean_dec_ref(x_1121);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
return x_1127;
}
}
else
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
lean_dec(x_1125);
lean_dec_ref(x_1121);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec_ref(x_1112);
x_1130 = lean_ctor_get(x_1126, 0);
lean_inc(x_1130);
if (lean_is_exclusive(x_1126)) {
 lean_ctor_release(x_1126, 0);
 x_1131 = x_1126;
} else {
 lean_dec_ref(x_1126);
 x_1131 = lean_box(0);
}
if (lean_is_scalar(x_1131)) {
 x_1132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1132 = x_1131;
}
lean_ctor_set(x_1132, 0, x_1130);
return x_1132;
}
}
else
{
lean_object* x_1133; 
lean_dec(x_1124);
lean_inc(x_1119);
lean_inc_ref(x_1116);
lean_inc(x_1118);
lean_inc_ref(x_1117);
lean_inc_ref(x_1120);
x_1133 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1120, x_1113, x_1115, x_1117, x_1118, x_1116, x_1119);
if (lean_obj_tag(x_1133) == 0)
{
lean_object* x_1134; 
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
lean_dec_ref(x_1133);
if (lean_obj_tag(x_1134) == 1)
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
lean_dec_ref(x_1120);
lean_inc_ref(x_1112);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1135 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1135 = lean_box(0);
}
x_1136 = lean_ctor_get(x_1134, 0);
lean_inc(x_1136);
lean_dec_ref(x_1134);
if (lean_is_scalar(x_1135)) {
 x_1137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1137 = x_1135;
 lean_ctor_set_tag(x_1137, 1);
}
lean_ctor_set(x_1137, 0, x_1136);
lean_ctor_set(x_1137, 1, x_1112);
x_1 = x_1137;
x_2 = x_1113;
x_3 = x_1115;
x_4 = x_1121;
x_5 = x_1117;
x_6 = x_1118;
x_7 = x_1116;
x_8 = x_1119;
goto _start;
}
else
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; 
lean_dec(x_1134);
x_1139 = lean_ctor_get(x_1120, 0);
x_1140 = lean_ctor_get(x_1120, 3);
x_1141 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1140);
x_1142 = lean_ctor_get(x_1141, 0);
lean_inc(x_1142);
lean_dec_ref(x_1141);
if (lean_obj_tag(x_1142) == 1)
{
lean_object* x_1143; lean_object* x_1144; 
lean_inc_ref(x_1112);
lean_dec_ref(x_1);
x_1143 = lean_ctor_get(x_1142, 0);
lean_inc(x_1143);
lean_dec_ref(x_1142);
lean_inc(x_1139);
x_1144 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1139, x_1143, x_1115, x_1118, x_1116, x_1119);
if (lean_obj_tag(x_1144) == 0)
{
lean_object* x_1145; 
lean_dec_ref(x_1144);
x_1145 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1120, x_1115, x_1118);
lean_dec_ref(x_1120);
if (lean_obj_tag(x_1145) == 0)
{
lean_dec_ref(x_1145);
x_1 = x_1112;
x_2 = x_1113;
x_3 = x_1115;
x_4 = x_1121;
x_5 = x_1117;
x_6 = x_1118;
x_7 = x_1116;
x_8 = x_1119;
goto _start;
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; 
lean_dec_ref(x_1121);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec_ref(x_1112);
x_1147 = lean_ctor_get(x_1145, 0);
lean_inc(x_1147);
if (lean_is_exclusive(x_1145)) {
 lean_ctor_release(x_1145, 0);
 x_1148 = x_1145;
} else {
 lean_dec_ref(x_1145);
 x_1148 = lean_box(0);
}
if (lean_is_scalar(x_1148)) {
 x_1149 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1149 = x_1148;
}
lean_ctor_set(x_1149, 0, x_1147);
return x_1149;
}
}
else
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec_ref(x_1112);
x_1150 = lean_ctor_get(x_1144, 0);
lean_inc(x_1150);
if (lean_is_exclusive(x_1144)) {
 lean_ctor_release(x_1144, 0);
 x_1151 = x_1144;
} else {
 lean_dec_ref(x_1144);
 x_1151 = lean_box(0);
}
if (lean_is_scalar(x_1151)) {
 x_1152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1152 = x_1151;
}
lean_ctor_set(x_1152, 0, x_1150);
return x_1152;
}
}
else
{
lean_object* x_1153; 
lean_dec(x_1142);
lean_inc(x_1119);
lean_inc_ref(x_1116);
lean_inc(x_1118);
lean_inc_ref(x_1117);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1113);
lean_inc_ref(x_1112);
lean_inc_ref(x_1120);
x_1153 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1120, x_1112, x_1113, x_1115, x_1121, x_1117, x_1118, x_1116, x_1119);
if (lean_obj_tag(x_1153) == 0)
{
lean_object* x_1154; 
x_1154 = lean_ctor_get(x_1153, 0);
lean_inc(x_1154);
lean_dec_ref(x_1153);
if (lean_obj_tag(x_1154) == 1)
{
lean_object* x_1155; lean_object* x_1156; 
lean_dec_ref(x_1121);
lean_dec(x_1119);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec_ref(x_1113);
lean_dec_ref(x_1);
x_1155 = lean_ctor_get(x_1154, 0);
lean_inc(x_1155);
lean_dec_ref(x_1154);
x_1156 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1120, x_1115, x_1118);
lean_dec(x_1118);
lean_dec(x_1115);
lean_dec_ref(x_1120);
if (lean_obj_tag(x_1156) == 0)
{
lean_object* x_1157; lean_object* x_1158; 
if (lean_is_exclusive(x_1156)) {
 lean_ctor_release(x_1156, 0);
 x_1157 = x_1156;
} else {
 lean_dec_ref(x_1156);
 x_1157 = lean_box(0);
}
if (lean_is_scalar(x_1157)) {
 x_1158 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1158 = x_1157;
}
lean_ctor_set(x_1158, 0, x_1155);
return x_1158;
}
else
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
lean_dec(x_1155);
x_1159 = lean_ctor_get(x_1156, 0);
lean_inc(x_1159);
if (lean_is_exclusive(x_1156)) {
 lean_ctor_release(x_1156, 0);
 x_1160 = x_1156;
} else {
 lean_dec_ref(x_1156);
 x_1160 = lean_box(0);
}
if (lean_is_scalar(x_1160)) {
 x_1161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1161 = x_1160;
}
lean_ctor_set(x_1161, 0, x_1159);
return x_1161;
}
}
else
{
lean_object* x_1162; 
lean_dec(x_1154);
lean_inc(x_1119);
lean_inc_ref(x_1116);
lean_inc(x_1118);
lean_inc_ref(x_1117);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1113);
lean_inc(x_1140);
x_1162 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_1140, x_1113, x_1115, x_1121, x_1117, x_1118, x_1116, x_1119);
if (lean_obj_tag(x_1162) == 0)
{
lean_object* x_1163; 
x_1163 = lean_ctor_get(x_1162, 0);
lean_inc(x_1163);
lean_dec_ref(x_1162);
if (lean_obj_tag(x_1163) == 1)
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
lean_inc_ref(x_1112);
lean_dec_ref(x_1);
x_1164 = lean_ctor_get(x_1163, 0);
lean_inc(x_1164);
lean_dec_ref(x_1163);
x_1165 = lean_ctor_get(x_1164, 0);
lean_inc(x_1165);
x_1166 = lean_ctor_get(x_1164, 1);
lean_inc(x_1166);
lean_dec(x_1164);
lean_inc(x_1139);
x_1167 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1139, x_1166, x_1115, x_1118, x_1116, x_1119);
if (lean_obj_tag(x_1167) == 0)
{
lean_object* x_1168; 
lean_dec_ref(x_1167);
x_1168 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1120, x_1115, x_1118);
lean_dec_ref(x_1120);
if (lean_obj_tag(x_1168) == 0)
{
lean_object* x_1169; 
lean_dec_ref(x_1168);
lean_inc(x_1119);
lean_inc_ref(x_1116);
lean_inc(x_1118);
lean_inc_ref(x_1117);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1113);
x_1169 = l_Lean_Compiler_LCNF_Simp_simp(x_1112, x_1113, x_1115, x_1121, x_1117, x_1118, x_1116, x_1119);
if (lean_obj_tag(x_1169) == 0)
{
lean_object* x_1170; lean_object* x_1171; 
x_1170 = lean_ctor_get(x_1169, 0);
lean_inc(x_1170);
lean_dec_ref(x_1169);
x_1171 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1165, x_1170, x_1113, x_1115, x_1121, x_1117, x_1118, x_1116, x_1119);
lean_dec(x_1119);
lean_dec_ref(x_1116);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1121);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec(x_1165);
return x_1171;
}
else
{
lean_dec(x_1165);
lean_dec_ref(x_1121);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
return x_1169;
}
}
else
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
lean_dec(x_1165);
lean_dec_ref(x_1121);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec_ref(x_1112);
x_1172 = lean_ctor_get(x_1168, 0);
lean_inc(x_1172);
if (lean_is_exclusive(x_1168)) {
 lean_ctor_release(x_1168, 0);
 x_1173 = x_1168;
} else {
 lean_dec_ref(x_1168);
 x_1173 = lean_box(0);
}
if (lean_is_scalar(x_1173)) {
 x_1174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1174 = x_1173;
}
lean_ctor_set(x_1174, 0, x_1172);
return x_1174;
}
}
else
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; 
lean_dec(x_1165);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec_ref(x_1112);
x_1175 = lean_ctor_get(x_1167, 0);
lean_inc(x_1175);
if (lean_is_exclusive(x_1167)) {
 lean_ctor_release(x_1167, 0);
 x_1176 = x_1167;
} else {
 lean_dec_ref(x_1167);
 x_1176 = lean_box(0);
}
if (lean_is_scalar(x_1176)) {
 x_1177 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1177 = x_1176;
}
lean_ctor_set(x_1177, 0, x_1175);
return x_1177;
}
}
else
{
lean_object* x_1178; 
lean_dec(x_1163);
lean_inc(x_1119);
lean_inc_ref(x_1116);
lean_inc(x_1118);
lean_inc_ref(x_1117);
lean_inc_ref(x_1121);
lean_inc(x_1115);
lean_inc_ref(x_1113);
lean_inc_ref(x_1112);
x_1178 = l_Lean_Compiler_LCNF_Simp_simp(x_1112, x_1113, x_1115, x_1121, x_1117, x_1118, x_1116, x_1119);
if (lean_obj_tag(x_1178) == 0)
{
lean_object* x_1179; lean_object* x_1180; 
x_1179 = lean_ctor_get(x_1178, 0);
lean_inc(x_1179);
lean_dec_ref(x_1178);
x_1180 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_1139, x_1115);
if (lean_obj_tag(x_1180) == 0)
{
lean_object* x_1181; uint8_t x_1182; 
x_1181 = lean_ctor_get(x_1180, 0);
lean_inc(x_1181);
lean_dec_ref(x_1180);
x_1182 = lean_unbox(x_1181);
lean_dec(x_1181);
if (x_1182 == 0)
{
lean_object* x_1183; 
lean_dec_ref(x_1121);
lean_dec(x_1119);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec_ref(x_1113);
lean_dec_ref(x_1);
x_1183 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1120, x_1115, x_1118);
lean_dec(x_1118);
lean_dec(x_1115);
lean_dec_ref(x_1120);
if (lean_obj_tag(x_1183) == 0)
{
lean_object* x_1184; lean_object* x_1185; 
if (lean_is_exclusive(x_1183)) {
 lean_ctor_release(x_1183, 0);
 x_1184 = x_1183;
} else {
 lean_dec_ref(x_1183);
 x_1184 = lean_box(0);
}
if (lean_is_scalar(x_1184)) {
 x_1185 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1185 = x_1184;
}
lean_ctor_set(x_1185, 0, x_1179);
return x_1185;
}
else
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; 
lean_dec(x_1179);
x_1186 = lean_ctor_get(x_1183, 0);
lean_inc(x_1186);
if (lean_is_exclusive(x_1183)) {
 lean_ctor_release(x_1183, 0);
 x_1187 = x_1183;
} else {
 lean_dec_ref(x_1183);
 x_1187 = lean_box(0);
}
if (lean_is_scalar(x_1187)) {
 x_1188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1188 = x_1187;
}
lean_ctor_set(x_1188, 0, x_1186);
return x_1188;
}
}
else
{
lean_object* x_1189; 
lean_inc_ref(x_1120);
x_1189 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_1120, x_1113, x_1115, x_1121, x_1117, x_1118, x_1116, x_1119);
lean_dec(x_1119);
lean_dec_ref(x_1116);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1121);
lean_dec(x_1115);
lean_dec_ref(x_1113);
if (lean_obj_tag(x_1189) == 0)
{
size_t x_1190; size_t x_1191; uint8_t x_1192; 
lean_dec_ref(x_1189);
x_1190 = lean_ptr_addr(x_1112);
x_1191 = lean_ptr_addr(x_1179);
x_1192 = lean_usize_dec_eq(x_1190, x_1191);
if (x_1192 == 0)
{
x_10 = lean_box(0);
x_11 = x_1120;
x_12 = x_1179;
x_13 = x_1192;
goto block_17;
}
else
{
size_t x_1193; size_t x_1194; uint8_t x_1195; 
x_1193 = lean_ptr_addr(x_1111);
x_1194 = lean_ptr_addr(x_1120);
x_1195 = lean_usize_dec_eq(x_1193, x_1194);
x_10 = lean_box(0);
x_11 = x_1120;
x_12 = x_1179;
x_13 = x_1195;
goto block_17;
}
}
else
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
lean_dec(x_1179);
lean_dec_ref(x_1120);
lean_dec_ref(x_1);
x_1196 = lean_ctor_get(x_1189, 0);
lean_inc(x_1196);
if (lean_is_exclusive(x_1189)) {
 lean_ctor_release(x_1189, 0);
 x_1197 = x_1189;
} else {
 lean_dec_ref(x_1189);
 x_1197 = lean_box(0);
}
if (lean_is_scalar(x_1197)) {
 x_1198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1198 = x_1197;
}
lean_ctor_set(x_1198, 0, x_1196);
return x_1198;
}
}
}
else
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; 
lean_dec(x_1179);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec_ref(x_1);
x_1199 = lean_ctor_get(x_1180, 0);
lean_inc(x_1199);
if (lean_is_exclusive(x_1180)) {
 lean_ctor_release(x_1180, 0);
 x_1200 = x_1180;
} else {
 lean_dec_ref(x_1180);
 x_1200 = lean_box(0);
}
if (lean_is_scalar(x_1200)) {
 x_1201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1201 = x_1200;
}
lean_ctor_set(x_1201, 0, x_1199);
return x_1201;
}
}
else
{
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec_ref(x_1);
return x_1178;
}
}
}
else
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec_ref(x_1);
x_1202 = lean_ctor_get(x_1162, 0);
lean_inc(x_1202);
if (lean_is_exclusive(x_1162)) {
 lean_ctor_release(x_1162, 0);
 x_1203 = x_1162;
} else {
 lean_dec_ref(x_1162);
 x_1203 = lean_box(0);
}
if (lean_is_scalar(x_1203)) {
 x_1204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1204 = x_1203;
}
lean_ctor_set(x_1204, 0, x_1202);
return x_1204;
}
}
}
else
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec_ref(x_1);
x_1205 = lean_ctor_get(x_1153, 0);
lean_inc(x_1205);
if (lean_is_exclusive(x_1153)) {
 lean_ctor_release(x_1153, 0);
 x_1206 = x_1153;
} else {
 lean_dec_ref(x_1153);
 x_1206 = lean_box(0);
}
if (lean_is_scalar(x_1206)) {
 x_1207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1207 = x_1206;
}
lean_ctor_set(x_1207, 0, x_1205);
return x_1207;
}
}
}
}
else
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; 
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
lean_dec_ref(x_1);
x_1208 = lean_ctor_get(x_1133, 0);
lean_inc(x_1208);
if (lean_is_exclusive(x_1133)) {
 lean_ctor_release(x_1133, 0);
 x_1209 = x_1133;
} else {
 lean_dec_ref(x_1133);
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
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
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
x_1214 = lean_st_ref_take(x_1115);
x_1215 = lean_ctor_get(x_1120, 0);
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
x_1228 = lean_st_ref_set(x_1115, x_1227);
x_1229 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1120, x_1115, x_1118);
lean_dec_ref(x_1120);
if (lean_obj_tag(x_1229) == 0)
{
lean_dec_ref(x_1229);
x_1 = x_1112;
x_2 = x_1113;
x_3 = x_1115;
x_4 = x_1121;
x_5 = x_1117;
x_6 = x_1118;
x_7 = x_1116;
x_8 = x_1119;
goto _start;
}
else
{
lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
lean_dec_ref(x_1121);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec_ref(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1115);
lean_dec_ref(x_1113);
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
x_1113 = x_1238;
x_1114 = lean_box(0);
x_1115 = x_1239;
x_1116 = x_1243;
x_1117 = x_1241;
x_1118 = x_1242;
x_1119 = x_1244;
x_1120 = x_1235;
x_1121 = x_1240;
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
x_1113 = x_1238;
x_1114 = lean_box(0);
x_1115 = x_1239;
x_1116 = x_1243;
x_1117 = x_1241;
x_1118 = x_1242;
x_1119 = x_1244;
x_1120 = x_1235;
x_1121 = x_1240;
x_1122 = x_1246;
goto block_1234;
}
else
{
x_1113 = x_1238;
x_1114 = lean_box(0);
x_1115 = x_1239;
x_1116 = x_1243;
x_1117 = x_1241;
x_1118 = x_1242;
x_1119 = x_1244;
x_1120 = x_1235;
x_1121 = x_1240;
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
if (lean_obj_tag(x_1312) == 1)
{
lean_object* x_1313; 
lean_dec(x_1297);
lean_dec(x_1296);
lean_dec(x_1294);
lean_dec_ref(x_1);
x_1313 = lean_ctor_get(x_1312, 0);
lean_inc(x_1313);
lean_dec_ref(x_1312);
x_1 = x_1313;
x_7 = x_1110;
goto _start;
}
else
{
lean_object* x_1315; 
lean_dec(x_1312);
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_1294);
x_1315 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1294, x_3);
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1316; lean_object* x_1317; uint8_t x_1318; 
lean_dec_ref(x_1315);
x_1316 = lean_unsigned_to_nat(0u);
x_1317 = lean_array_get_size(x_1296);
x_1318 = lean_nat_dec_lt(x_1316, x_1317);
if (x_1318 == 0)
{
lean_dec(x_1317);
lean_dec(x_3);
x_1305 = lean_box(0);
goto block_1310;
}
else
{
uint8_t x_1319; 
x_1319 = lean_nat_dec_le(x_1317, x_1317);
if (x_1319 == 0)
{
lean_dec(x_1317);
lean_dec(x_3);
x_1305 = lean_box(0);
goto block_1310;
}
else
{
lean_object* x_1320; size_t x_1321; size_t x_1322; lean_object* x_1323; 
x_1320 = lean_box(0);
x_1321 = 0;
x_1322 = lean_usize_of_nat(x_1317);
lean_dec(x_1317);
x_1323 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1296, x_1321, x_1322, x_1320, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1323) == 0)
{
lean_dec_ref(x_1323);
x_1305 = lean_box(0);
goto block_1310;
}
else
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
lean_dec(x_1297);
lean_dec(x_1296);
lean_dec(x_1294);
lean_dec_ref(x_1);
x_1324 = lean_ctor_get(x_1323, 0);
lean_inc(x_1324);
if (lean_is_exclusive(x_1323)) {
 lean_ctor_release(x_1323, 0);
 x_1325 = x_1323;
} else {
 lean_dec_ref(x_1323);
 x_1325 = lean_box(0);
}
if (lean_is_scalar(x_1325)) {
 x_1326 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1326 = x_1325;
}
lean_ctor_set(x_1326, 0, x_1324);
return x_1326;
}
}
}
}
else
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
lean_dec(x_1297);
lean_dec(x_1296);
lean_dec(x_1294);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1327 = lean_ctor_get(x_1315, 0);
lean_inc(x_1327);
if (lean_is_exclusive(x_1315)) {
 lean_ctor_release(x_1315, 0);
 x_1328 = x_1315;
} else {
 lean_dec_ref(x_1315);
 x_1328 = lean_box(0);
}
if (lean_is_scalar(x_1328)) {
 x_1329 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1329 = x_1328;
}
lean_ctor_set(x_1329, 0, x_1327);
return x_1329;
}
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
if (lean_obj_tag(x_1336) == 1)
{
lean_object* x_1338; lean_object* x_1339; 
lean_dec_ref(x_1334);
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1338 = lean_ctor_get(x_1336, 0);
lean_inc(x_1338);
lean_dec_ref(x_1336);
if (lean_is_scalar(x_1337)) {
 x_1339 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1339 = x_1337;
}
lean_ctor_set(x_1339, 0, x_1338);
return x_1339;
}
else
{
lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; 
lean_dec(x_1336);
x_1340 = lean_st_ref_get(x_3);
x_1341 = lean_ctor_get(x_1334, 0);
lean_inc(x_1341);
x_1342 = lean_ctor_get(x_1334, 1);
lean_inc_ref(x_1342);
x_1343 = lean_ctor_get(x_1334, 2);
lean_inc(x_1343);
x_1344 = lean_ctor_get(x_1334, 3);
lean_inc_ref(x_1344);
if (lean_is_exclusive(x_1334)) {
 lean_ctor_release(x_1334, 0);
 lean_ctor_release(x_1334, 1);
 lean_ctor_release(x_1334, 2);
 lean_ctor_release(x_1334, 3);
 x_1345 = x_1334;
} else {
 lean_dec_ref(x_1334);
 x_1345 = lean_box(0);
}
x_1346 = lean_ctor_get(x_1340, 0);
lean_inc_ref(x_1346);
lean_dec_ref(x_1340);
lean_inc(x_1343);
x_1347 = l_Lean_Compiler_LCNF_normFVarImp(x_1346, x_1343, x_122);
lean_dec_ref(x_1346);
if (lean_obj_tag(x_1347) == 0)
{
lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
x_1348 = lean_ctor_get(x_1347, 0);
lean_inc(x_1348);
if (lean_is_exclusive(x_1347)) {
 lean_ctor_release(x_1347, 0);
 x_1349 = x_1347;
} else {
 lean_dec_ref(x_1347);
 x_1349 = lean_box(0);
}
x_1350 = lean_st_ref_get(x_3);
x_1351 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_1110);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1344);
lean_inc(x_1348);
x_1352 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_1348, x_122, x_1351, x_1344, x_2, x_3, x_4, x_5, x_6, x_1110, x_8);
if (lean_obj_tag(x_1352) == 0)
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
x_1353 = lean_ctor_get(x_1352, 0);
lean_inc(x_1353);
if (lean_is_exclusive(x_1352)) {
 lean_ctor_release(x_1352, 0);
 x_1354 = x_1352;
} else {
 lean_dec_ref(x_1352);
 x_1354 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_1355 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1353, x_2, x_3, x_4, x_5, x_6, x_1110, x_8);
if (lean_obj_tag(x_1355) == 0)
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1365; uint8_t x_1366; lean_object* x_1370; lean_object* x_1371; lean_object* x_1383; uint8_t x_1384; 
x_1356 = lean_ctor_get(x_1355, 0);
lean_inc(x_1356);
if (lean_is_exclusive(x_1355)) {
 lean_ctor_release(x_1355, 0);
 x_1357 = x_1355;
} else {
 lean_dec_ref(x_1355);
 x_1357 = lean_box(0);
}
x_1358 = lean_ctor_get(x_1350, 0);
lean_inc_ref(x_1358);
lean_dec_ref(x_1350);
lean_inc_ref(x_1342);
x_1359 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1358, x_122, x_1342);
lean_dec_ref(x_1358);
x_1383 = lean_array_get_size(x_1356);
x_1384 = lean_nat_dec_eq(x_1383, x_1108);
lean_dec(x_1383);
if (x_1384 == 0)
{
lean_dec(x_1337);
lean_dec(x_6);
x_1370 = x_3;
x_1371 = lean_box(0);
goto block_1382;
}
else
{
lean_object* x_1385; 
x_1385 = lean_array_fget_borrowed(x_1356, x_1351);
if (lean_obj_tag(x_1385) == 0)
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1396; lean_object* x_1397; uint8_t x_1408; lean_object* x_1409; uint8_t x_1411; 
lean_dec(x_1337);
x_1386 = lean_ctor_get(x_1385, 1);
x_1387 = lean_ctor_get(x_1385, 2);
x_1396 = lean_array_get_size(x_1386);
x_1411 = lean_nat_dec_lt(x_1351, x_1396);
if (x_1411 == 0)
{
x_1408 = x_122;
x_1409 = lean_box(0);
goto block_1410;
}
else
{
if (x_1411 == 0)
{
x_1408 = x_122;
x_1409 = lean_box(0);
goto block_1410;
}
else
{
size_t x_1412; size_t x_1413; lean_object* x_1414; 
x_1412 = 0;
x_1413 = lean_usize_of_nat(x_1396);
x_1414 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1386, x_1412, x_1413, x_3);
if (lean_obj_tag(x_1414) == 0)
{
lean_object* x_1415; uint8_t x_1416; 
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
lean_dec_ref(x_1414);
x_1416 = lean_unbox(x_1415);
lean_dec(x_1415);
x_1408 = x_1416;
x_1409 = lean_box(0);
goto block_1410;
}
else
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
lean_dec(x_1396);
lean_dec_ref(x_1359);
lean_dec(x_1357);
lean_dec(x_1356);
lean_dec(x_1354);
lean_dec(x_1349);
lean_dec(x_1348);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1417 = lean_ctor_get(x_1414, 0);
lean_inc(x_1417);
if (lean_is_exclusive(x_1414)) {
 lean_ctor_release(x_1414, 0);
 x_1418 = x_1414;
} else {
 lean_dec_ref(x_1414);
 x_1418 = lean_box(0);
}
if (lean_is_scalar(x_1418)) {
 x_1419 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1419 = x_1418;
}
lean_ctor_set(x_1419, 0, x_1417);
return x_1419;
}
}
}
block_1395:
{
lean_object* x_1389; 
x_1389 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1389) == 0)
{
lean_object* x_1390; lean_object* x_1391; 
if (lean_is_exclusive(x_1389)) {
 lean_ctor_release(x_1389, 0);
 x_1390 = x_1389;
} else {
 lean_dec_ref(x_1389);
 x_1390 = lean_box(0);
}
if (lean_is_scalar(x_1390)) {
 x_1391 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1391 = x_1390;
}
lean_ctor_set(x_1391, 0, x_1387);
return x_1391;
}
else
{
lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; 
lean_dec_ref(x_1387);
x_1392 = lean_ctor_get(x_1389, 0);
lean_inc(x_1392);
if (lean_is_exclusive(x_1389)) {
 lean_ctor_release(x_1389, 0);
 x_1393 = x_1389;
} else {
 lean_dec_ref(x_1389);
 x_1393 = lean_box(0);
}
if (lean_is_scalar(x_1393)) {
 x_1394 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1394 = x_1393;
}
lean_ctor_set(x_1394, 0, x_1392);
return x_1394;
}
}
block_1407:
{
uint8_t x_1398; 
x_1398 = lean_nat_dec_lt(x_1351, x_1396);
if (x_1398 == 0)
{
lean_dec(x_1396);
lean_dec_ref(x_1386);
lean_dec(x_6);
x_1388 = lean_box(0);
goto block_1395;
}
else
{
uint8_t x_1399; 
x_1399 = lean_nat_dec_le(x_1396, x_1396);
if (x_1399 == 0)
{
lean_dec(x_1396);
lean_dec_ref(x_1386);
lean_dec(x_6);
x_1388 = lean_box(0);
goto block_1395;
}
else
{
lean_object* x_1400; size_t x_1401; size_t x_1402; lean_object* x_1403; 
x_1400 = lean_box(0);
x_1401 = 0;
x_1402 = lean_usize_of_nat(x_1396);
lean_dec(x_1396);
x_1403 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1386, x_1401, x_1402, x_1400, x_6);
lean_dec(x_6);
lean_dec_ref(x_1386);
if (lean_obj_tag(x_1403) == 0)
{
lean_dec_ref(x_1403);
x_1388 = lean_box(0);
goto block_1395;
}
else
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
lean_dec_ref(x_1387);
lean_dec(x_3);
x_1404 = lean_ctor_get(x_1403, 0);
lean_inc(x_1404);
if (lean_is_exclusive(x_1403)) {
 lean_ctor_release(x_1403, 0);
 x_1405 = x_1403;
} else {
 lean_dec_ref(x_1403);
 x_1405 = lean_box(0);
}
if (lean_is_scalar(x_1405)) {
 x_1406 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1406 = x_1405;
}
lean_ctor_set(x_1406, 0, x_1404);
return x_1406;
}
}
}
}
block_1410:
{
if (x_1408 == 0)
{
lean_inc_ref(x_1387);
lean_inc_ref(x_1386);
lean_dec_ref(x_1359);
lean_dec(x_1357);
lean_dec(x_1356);
lean_dec(x_1354);
lean_dec(x_1349);
lean_dec(x_1348);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec_ref(x_1);
x_1397 = lean_box(0);
goto block_1407;
}
else
{
if (x_122 == 0)
{
lean_dec(x_1396);
lean_dec(x_6);
x_1370 = x_3;
x_1371 = lean_box(0);
goto block_1382;
}
else
{
lean_inc_ref(x_1387);
lean_inc_ref(x_1386);
lean_dec_ref(x_1359);
lean_dec(x_1357);
lean_dec(x_1356);
lean_dec(x_1354);
lean_dec(x_1349);
lean_dec(x_1348);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec_ref(x_1);
x_1397 = lean_box(0);
goto block_1407;
}
}
}
}
else
{
lean_object* x_1420; lean_object* x_1421; 
lean_inc_ref(x_1385);
lean_dec_ref(x_1359);
lean_dec(x_1357);
lean_dec(x_1356);
lean_dec(x_1354);
lean_dec(x_1349);
lean_dec(x_1348);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1420 = lean_ctor_get(x_1385, 0);
lean_inc_ref(x_1420);
lean_dec_ref(x_1385);
if (lean_is_scalar(x_1337)) {
 x_1421 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1421 = x_1337;
}
lean_ctor_set(x_1421, 0, x_1420);
return x_1421;
}
}
block_1364:
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
if (lean_is_scalar(x_1345)) {
 x_1361 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1361 = x_1345;
}
lean_ctor_set(x_1361, 0, x_1341);
lean_ctor_set(x_1361, 1, x_1359);
lean_ctor_set(x_1361, 2, x_1348);
lean_ctor_set(x_1361, 3, x_1356);
if (lean_is_scalar(x_1349)) {
 x_1362 = lean_alloc_ctor(4, 1, 0);
} else {
 x_1362 = x_1349;
 lean_ctor_set_tag(x_1362, 4);
}
lean_ctor_set(x_1362, 0, x_1361);
if (lean_is_scalar(x_1357)) {
 x_1363 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1363 = x_1357;
}
lean_ctor_set(x_1363, 0, x_1362);
return x_1363;
}
block_1369:
{
if (x_1366 == 0)
{
lean_dec(x_1354);
lean_dec(x_1343);
lean_dec_ref(x_1);
x_1360 = lean_box(0);
goto block_1364;
}
else
{
uint8_t x_1367; 
x_1367 = l_Lean_instBEqFVarId_beq(x_1343, x_1348);
lean_dec(x_1343);
if (x_1367 == 0)
{
lean_dec(x_1354);
lean_dec_ref(x_1);
x_1360 = lean_box(0);
goto block_1364;
}
else
{
lean_object* x_1368; 
lean_dec_ref(x_1359);
lean_dec(x_1357);
lean_dec(x_1356);
lean_dec(x_1349);
lean_dec(x_1348);
lean_dec(x_1345);
lean_dec(x_1341);
if (lean_is_scalar(x_1354)) {
 x_1368 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1368 = x_1354;
}
lean_ctor_set(x_1368, 0, x_1);
return x_1368;
}
}
}
block_1382:
{
lean_object* x_1372; 
lean_inc(x_1348);
x_1372 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1348, x_1370);
lean_dec(x_1370);
if (lean_obj_tag(x_1372) == 0)
{
size_t x_1373; size_t x_1374; uint8_t x_1375; 
lean_dec_ref(x_1372);
x_1373 = lean_ptr_addr(x_1344);
lean_dec_ref(x_1344);
x_1374 = lean_ptr_addr(x_1356);
x_1375 = lean_usize_dec_eq(x_1373, x_1374);
if (x_1375 == 0)
{
lean_dec_ref(x_1342);
x_1365 = lean_box(0);
x_1366 = x_1375;
goto block_1369;
}
else
{
size_t x_1376; size_t x_1377; uint8_t x_1378; 
x_1376 = lean_ptr_addr(x_1342);
lean_dec_ref(x_1342);
x_1377 = lean_ptr_addr(x_1359);
x_1378 = lean_usize_dec_eq(x_1376, x_1377);
x_1365 = lean_box(0);
x_1366 = x_1378;
goto block_1369;
}
}
else
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
lean_dec_ref(x_1359);
lean_dec(x_1357);
lean_dec(x_1356);
lean_dec(x_1354);
lean_dec(x_1349);
lean_dec(x_1348);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec_ref(x_1);
x_1379 = lean_ctor_get(x_1372, 0);
lean_inc(x_1379);
if (lean_is_exclusive(x_1372)) {
 lean_ctor_release(x_1372, 0);
 x_1380 = x_1372;
} else {
 lean_dec_ref(x_1372);
 x_1380 = lean_box(0);
}
if (lean_is_scalar(x_1380)) {
 x_1381 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1381 = x_1380;
}
lean_ctor_set(x_1381, 0, x_1379);
return x_1381;
}
}
}
else
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; 
lean_dec(x_1354);
lean_dec_ref(x_1350);
lean_dec(x_1349);
lean_dec(x_1348);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec(x_1337);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1422 = lean_ctor_get(x_1355, 0);
lean_inc(x_1422);
if (lean_is_exclusive(x_1355)) {
 lean_ctor_release(x_1355, 0);
 x_1423 = x_1355;
} else {
 lean_dec_ref(x_1355);
 x_1423 = lean_box(0);
}
if (lean_is_scalar(x_1423)) {
 x_1424 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1424 = x_1423;
}
lean_ctor_set(x_1424, 0, x_1422);
return x_1424;
}
}
else
{
lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; 
lean_dec_ref(x_1350);
lean_dec(x_1349);
lean_dec(x_1348);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec(x_1337);
lean_dec_ref(x_1110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1425 = lean_ctor_get(x_1352, 0);
lean_inc(x_1425);
if (lean_is_exclusive(x_1352)) {
 lean_ctor_release(x_1352, 0);
 x_1426 = x_1352;
} else {
 lean_dec_ref(x_1352);
 x_1426 = lean_box(0);
}
if (lean_is_scalar(x_1426)) {
 x_1427 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1427 = x_1426;
}
lean_ctor_set(x_1427, 0, x_1425);
return x_1427;
}
}
else
{
lean_object* x_1428; 
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1341);
lean_dec(x_1337);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1428 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1110, x_8);
lean_dec(x_8);
lean_dec_ref(x_1110);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1428;
}
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
x_89 = x_1061;
x_90 = x_1076;
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
x_89 = x_1061;
x_90 = x_1078;
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
x_89 = x_1061;
x_90 = x_1086;
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
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
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
x_57 = x_90;
x_58 = x_89;
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
lean_dec_ref(x_89);
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
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_22 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_20);
x_23 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_ctor_set_tag(x_14, 4);
lean_ctor_set(x_14, 0, x_26);
x_27 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_14, x_6);
lean_dec_ref(x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec_ref(x_27);
x_28 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_dec_ref(x_28);
if (lean_obj_tag(x_25) == 0)
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_free_object(x_23);
x_29 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_30);
lean_dec_ref(x_25);
x_31 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_32);
lean_dec_ref(x_20);
x_54 = lean_ctor_get(x_31, 3);
lean_inc(x_54);
lean_dec_ref(x_31);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get_size(x_32);
x_57 = lean_nat_dec_le(x_54, x_55);
if (x_57 == 0)
{
x_33 = x_54;
x_34 = x_56;
goto block_53;
}
else
{
lean_dec(x_54);
x_33 = x_55;
x_34 = x_56;
goto block_53;
}
block_53:
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = l_Array_toSubarray___redArg(x_32, x_33, x_34);
x_36 = lean_array_size(x_29);
x_37 = 0;
x_38 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_29, x_36, x_37, x_35, x_3);
lean_dec_ref(x_38);
lean_inc(x_6);
x_39 = l_Lean_Compiler_LCNF_Simp_simp(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_29, x_6);
lean_dec(x_6);
lean_dec_ref(x_29);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
if (lean_is_scalar(x_21)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_21;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
if (lean_is_scalar(x_21)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_21;
}
lean_ctor_set(x_45, 0, x_40);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_40);
lean_dec(x_21);
x_47 = !lean_is_exclusive(x_41);
if (x_47 == 0)
{
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec_ref(x_29);
lean_dec(x_21);
lean_dec(x_6);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
lean_dec(x_39);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_59);
lean_dec_ref(x_25);
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_20, 0);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_61, x_62);
if (x_63 == 1)
{
lean_object* x_64; 
lean_free_object(x_20);
lean_dec(x_61);
lean_dec_ref(x_58);
lean_free_object(x_23);
x_64 = l_Lean_Compiler_LCNF_Simp_simp(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
if (lean_is_scalar(x_21)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_21;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
lean_dec(x_64);
if (lean_is_scalar(x_21)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_21;
}
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_21);
x_71 = !lean_is_exclusive(x_64);
if (x_71 == 0)
{
return x_64;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_64, 0);
lean_inc(x_72);
lean_dec(x_64);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_sub(x_61, x_74);
lean_dec(x_61);
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_75);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_20);
x_77 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_78 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_76, x_77, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_81 = lean_array_get_borrowed(x_80, x_58, x_62);
x_82 = lean_ctor_get(x_81, 0);
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
lean_inc(x_82);
x_84 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_82, x_83, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
lean_dec_ref(x_84);
lean_inc(x_6);
x_85 = l_Lean_Compiler_LCNF_Simp_simp(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_58, x_6);
lean_dec(x_6);
lean_dec_ref(x_58);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
lean_ctor_set(x_23, 1, x_86);
lean_ctor_set(x_23, 0, x_79);
if (lean_is_scalar(x_21)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_21;
}
lean_ctor_set(x_90, 0, x_23);
lean_ctor_set(x_87, 0, x_90);
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_87);
lean_ctor_set(x_23, 1, x_86);
lean_ctor_set(x_23, 0, x_79);
if (lean_is_scalar(x_21)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_21;
}
lean_ctor_set(x_91, 0, x_23);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec(x_86);
lean_dec(x_79);
lean_free_object(x_23);
lean_dec(x_21);
x_93 = !lean_is_exclusive(x_87);
if (x_93 == 0)
{
return x_87;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_79);
lean_dec_ref(x_58);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_6);
x_96 = !lean_is_exclusive(x_85);
if (x_96 == 0)
{
return x_85;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_85, 0);
lean_inc(x_97);
lean_dec(x_85);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_79);
lean_dec_ref(x_59);
lean_dec_ref(x_58);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_99 = !lean_is_exclusive(x_84);
if (x_99 == 0)
{
return x_84;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_84, 0);
lean_inc(x_100);
lean_dec(x_84);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec_ref(x_59);
lean_dec_ref(x_58);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_102 = !lean_is_exclusive(x_78);
if (x_102 == 0)
{
return x_78;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_78, 0);
lean_inc(x_103);
lean_dec(x_78);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_20, 0);
lean_inc(x_105);
lean_dec(x_20);
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_nat_dec_eq(x_105, x_106);
if (x_107 == 1)
{
lean_object* x_108; 
lean_dec(x_105);
lean_dec_ref(x_58);
lean_free_object(x_23);
x_108 = l_Lean_Compiler_LCNF_Simp_simp(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_21;
}
lean_ctor_set(x_111, 0, x_109);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 1, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_21);
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_114 = x_108;
} else {
 lean_dec_ref(x_108);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_unsigned_to_nat(1u);
x_117 = lean_nat_sub(x_105, x_116);
lean_dec(x_105);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_121 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_119, x_120, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_124 = lean_array_get_borrowed(x_123, x_58, x_106);
x_125 = lean_ctor_get(x_124, 0);
x_126 = lean_ctor_get(x_122, 0);
lean_inc(x_126);
lean_inc(x_125);
x_127 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_125, x_126, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
lean_dec_ref(x_127);
lean_inc(x_6);
x_128 = l_Lean_Compiler_LCNF_Simp_simp(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_58, x_6);
lean_dec(x_6);
lean_dec_ref(x_58);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_131 = x_130;
} else {
 lean_dec_ref(x_130);
 x_131 = lean_box(0);
}
lean_ctor_set(x_23, 1, x_129);
lean_ctor_set(x_23, 0, x_122);
if (lean_is_scalar(x_21)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_21;
}
lean_ctor_set(x_132, 0, x_23);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 1, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_122);
lean_free_object(x_23);
lean_dec(x_21);
x_134 = lean_ctor_get(x_130, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_122);
lean_dec_ref(x_58);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_6);
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_138 = x_128;
} else {
 lean_dec_ref(x_128);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_122);
lean_dec_ref(x_59);
lean_dec_ref(x_58);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_140 = lean_ctor_get(x_127, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_141 = x_127;
} else {
 lean_dec_ref(x_127);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec_ref(x_59);
lean_dec_ref(x_58);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_143 = lean_ctor_get(x_121, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_144 = x_121;
} else {
 lean_dec_ref(x_121);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_free_object(x_23);
lean_dec(x_20);
x_146 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_146);
lean_dec_ref(x_25);
x_147 = l_Lean_Compiler_LCNF_Simp_simp(x_146, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_147, 0);
if (lean_is_scalar(x_21)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_21;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_147, 0, x_150);
return x_147;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_147, 0);
lean_inc(x_151);
lean_dec(x_147);
if (lean_is_scalar(x_21)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_21;
}
lean_ctor_set(x_152, 0, x_151);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
else
{
uint8_t x_154; 
lean_dec(x_21);
x_154 = !lean_is_exclusive(x_147);
if (x_154 == 0)
{
return x_147;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_147, 0);
lean_inc(x_155);
lean_dec(x_147);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
}
}
else
{
uint8_t x_157; 
lean_free_object(x_23);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_157 = !lean_is_exclusive(x_28);
if (x_157 == 0)
{
return x_28;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_28, 0);
lean_inc(x_158);
lean_dec(x_28);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_free_object(x_23);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_160 = !lean_is_exclusive(x_27);
if (x_160 == 0)
{
return x_27;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_27, 0);
lean_inc(x_161);
lean_dec(x_27);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_23, 0);
x_164 = lean_ctor_get(x_23, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_23);
lean_ctor_set_tag(x_14, 4);
lean_ctor_set(x_14, 0, x_164);
x_165 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_14, x_6);
lean_dec_ref(x_14);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
lean_dec_ref(x_165);
x_166 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_166) == 0)
{
lean_dec_ref(x_166);
if (lean_obj_tag(x_163) == 0)
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_167 = lean_ctor_get(x_163, 1);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_163, 2);
lean_inc_ref(x_168);
lean_dec_ref(x_163);
x_169 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_169);
x_170 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_170);
lean_dec_ref(x_20);
x_190 = lean_ctor_get(x_169, 3);
lean_inc(x_190);
lean_dec_ref(x_169);
x_191 = lean_unsigned_to_nat(0u);
x_192 = lean_array_get_size(x_170);
x_193 = lean_nat_dec_le(x_190, x_191);
if (x_193 == 0)
{
x_171 = x_190;
x_172 = x_192;
goto block_189;
}
else
{
lean_dec(x_190);
x_171 = x_191;
x_172 = x_192;
goto block_189;
}
block_189:
{
lean_object* x_173; size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; 
x_173 = l_Array_toSubarray___redArg(x_170, x_171, x_172);
x_174 = lean_array_size(x_167);
x_175 = 0;
x_176 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_167, x_174, x_175, x_173, x_3);
lean_dec_ref(x_176);
lean_inc(x_6);
x_177 = l_Lean_Compiler_LCNF_Simp_simp(x_168, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_167, x_6);
lean_dec(x_6);
lean_dec_ref(x_167);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 x_180 = x_179;
} else {
 lean_dec_ref(x_179);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_21;
}
lean_ctor_set(x_181, 0, x_178);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 1, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_181);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_178);
lean_dec(x_21);
x_183 = lean_ctor_get(x_179, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 x_184 = x_179;
} else {
 lean_dec_ref(x_179);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec_ref(x_167);
lean_dec(x_21);
lean_dec(x_6);
x_186 = lean_ctor_get(x_177, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_187 = x_177;
} else {
 lean_dec_ref(x_177);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_186);
return x_188;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_194 = lean_ctor_get(x_163, 1);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_163, 2);
lean_inc_ref(x_195);
lean_dec_ref(x_163);
x_196 = lean_ctor_get(x_20, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_197 = x_20;
} else {
 lean_dec_ref(x_20);
 x_197 = lean_box(0);
}
x_198 = lean_unsigned_to_nat(0u);
x_199 = lean_nat_dec_eq(x_196, x_198);
if (x_199 == 1)
{
lean_object* x_200; 
lean_dec(x_197);
lean_dec(x_196);
lean_dec_ref(x_194);
x_200 = l_Lean_Compiler_LCNF_Simp_simp(x_195, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_202 = x_200;
} else {
 lean_dec_ref(x_200);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_203 = lean_alloc_ctor(1, 1, 0);
} else {
 x_203 = x_21;
}
lean_ctor_set(x_203, 0, x_201);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 1, 0);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_21);
x_205 = lean_ctor_get(x_200, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_206 = x_200;
} else {
 lean_dec_ref(x_200);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_sub(x_196, x_208);
lean_dec(x_196);
if (lean_is_scalar(x_197)) {
 x_210 = lean_alloc_ctor(0, 1, 0);
} else {
 x_210 = x_197;
 lean_ctor_set_tag(x_210, 0);
}
lean_ctor_set(x_210, 0, x_209);
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_213 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_211, x_212, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
x_215 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_216 = lean_array_get_borrowed(x_215, x_194, x_198);
x_217 = lean_ctor_get(x_216, 0);
x_218 = lean_ctor_get(x_214, 0);
lean_inc(x_218);
lean_inc(x_217);
x_219 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_217, x_218, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
lean_dec_ref(x_219);
lean_inc(x_6);
x_220 = l_Lean_Compiler_LCNF_Simp_simp(x_195, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_194, x_6);
lean_dec(x_6);
lean_dec_ref(x_194);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_223 = x_222;
} else {
 lean_dec_ref(x_222);
 x_223 = lean_box(0);
}
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_214);
lean_ctor_set(x_224, 1, x_221);
if (lean_is_scalar(x_21)) {
 x_225 = lean_alloc_ctor(1, 1, 0);
} else {
 x_225 = x_21;
}
lean_ctor_set(x_225, 0, x_224);
if (lean_is_scalar(x_223)) {
 x_226 = lean_alloc_ctor(0, 1, 0);
} else {
 x_226 = x_223;
}
lean_ctor_set(x_226, 0, x_225);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_221);
lean_dec(x_214);
lean_dec(x_21);
x_227 = lean_ctor_get(x_222, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_228 = x_222;
} else {
 lean_dec_ref(x_222);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 1, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_214);
lean_dec_ref(x_194);
lean_dec(x_21);
lean_dec(x_6);
x_230 = lean_ctor_get(x_220, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_231 = x_220;
} else {
 lean_dec_ref(x_220);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 1, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_230);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_214);
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_233 = lean_ctor_get(x_219, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_234 = x_219;
} else {
 lean_dec_ref(x_219);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 1, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_233);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_236 = lean_ctor_get(x_213, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_237 = x_213;
} else {
 lean_dec_ref(x_213);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 1, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_236);
return x_238;
}
}
}
}
else
{
lean_object* x_239; lean_object* x_240; 
lean_dec(x_20);
x_239 = lean_ctor_get(x_163, 0);
lean_inc_ref(x_239);
lean_dec_ref(x_163);
x_240 = l_Lean_Compiler_LCNF_Simp_simp(x_239, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 x_242 = x_240;
} else {
 lean_dec_ref(x_240);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_243 = lean_alloc_ctor(1, 1, 0);
} else {
 x_243 = x_21;
}
lean_ctor_set(x_243, 0, x_241);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 1, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_243);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_21);
x_245 = lean_ctor_get(x_240, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 x_246 = x_240;
} else {
 lean_dec_ref(x_240);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 1, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_245);
return x_247;
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_163);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_248 = lean_ctor_get(x_166, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_249 = x_166;
} else {
 lean_dec_ref(x_166);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 1, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_248);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_163);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_251 = lean_ctor_get(x_165, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_252 = x_165;
} else {
 lean_dec_ref(x_165);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 1, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_251);
return x_253;
}
}
}
else
{
lean_object* x_254; 
lean_dec(x_19);
lean_free_object(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_254 = lean_box(0);
lean_ctor_set(x_17, 0, x_254);
return x_17;
}
}
else
{
lean_object* x_255; 
x_255 = lean_ctor_get(x_17, 0);
lean_inc(x_255);
lean_dec(x_17);
if (lean_obj_tag(x_255) == 1)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
x_258 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_256);
x_259 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_258);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_262 = x_259;
} else {
 lean_dec_ref(x_259);
 x_262 = lean_box(0);
}
lean_ctor_set_tag(x_14, 4);
lean_ctor_set(x_14, 0, x_261);
x_263 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_14, x_6);
lean_dec_ref(x_14);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; 
lean_dec_ref(x_263);
x_264 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_264) == 0)
{
lean_dec_ref(x_264);
if (lean_obj_tag(x_260) == 0)
{
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
lean_dec(x_262);
x_265 = lean_ctor_get(x_260, 1);
lean_inc_ref(x_265);
x_266 = lean_ctor_get(x_260, 2);
lean_inc_ref(x_266);
lean_dec_ref(x_260);
x_267 = lean_ctor_get(x_256, 0);
lean_inc_ref(x_267);
x_268 = lean_ctor_get(x_256, 1);
lean_inc_ref(x_268);
lean_dec_ref(x_256);
x_288 = lean_ctor_get(x_267, 3);
lean_inc(x_288);
lean_dec_ref(x_267);
x_289 = lean_unsigned_to_nat(0u);
x_290 = lean_array_get_size(x_268);
x_291 = lean_nat_dec_le(x_288, x_289);
if (x_291 == 0)
{
x_269 = x_288;
x_270 = x_290;
goto block_287;
}
else
{
lean_dec(x_288);
x_269 = x_289;
x_270 = x_290;
goto block_287;
}
block_287:
{
lean_object* x_271; size_t x_272; size_t x_273; lean_object* x_274; lean_object* x_275; 
x_271 = l_Array_toSubarray___redArg(x_268, x_269, x_270);
x_272 = lean_array_size(x_265);
x_273 = 0;
x_274 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_265, x_272, x_273, x_271, x_3);
lean_dec_ref(x_274);
lean_inc(x_6);
x_275 = l_Lean_Compiler_LCNF_Simp_simp(x_266, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec_ref(x_275);
x_277 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_265, x_6);
lean_dec(x_6);
lean_dec_ref(x_265);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 x_278 = x_277;
} else {
 lean_dec_ref(x_277);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_279 = lean_alloc_ctor(1, 1, 0);
} else {
 x_279 = x_257;
}
lean_ctor_set(x_279, 0, x_276);
if (lean_is_scalar(x_278)) {
 x_280 = lean_alloc_ctor(0, 1, 0);
} else {
 x_280 = x_278;
}
lean_ctor_set(x_280, 0, x_279);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_276);
lean_dec(x_257);
x_281 = lean_ctor_get(x_277, 0);
lean_inc(x_281);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 x_282 = x_277;
} else {
 lean_dec_ref(x_277);
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
lean_dec_ref(x_265);
lean_dec(x_257);
lean_dec(x_6);
x_284 = lean_ctor_get(x_275, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_285 = x_275;
} else {
 lean_dec_ref(x_275);
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
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_292 = lean_ctor_get(x_260, 1);
lean_inc_ref(x_292);
x_293 = lean_ctor_get(x_260, 2);
lean_inc_ref(x_293);
lean_dec_ref(x_260);
x_294 = lean_ctor_get(x_256, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_295 = x_256;
} else {
 lean_dec_ref(x_256);
 x_295 = lean_box(0);
}
x_296 = lean_unsigned_to_nat(0u);
x_297 = lean_nat_dec_eq(x_294, x_296);
if (x_297 == 1)
{
lean_object* x_298; 
lean_dec(x_295);
lean_dec(x_294);
lean_dec_ref(x_292);
lean_dec(x_262);
x_298 = l_Lean_Compiler_LCNF_Simp_simp(x_293, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 x_300 = x_298;
} else {
 lean_dec_ref(x_298);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_257;
}
lean_ctor_set(x_301, 0, x_299);
if (lean_is_scalar(x_300)) {
 x_302 = lean_alloc_ctor(0, 1, 0);
} else {
 x_302 = x_300;
}
lean_ctor_set(x_302, 0, x_301);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_257);
x_303 = lean_ctor_get(x_298, 0);
lean_inc(x_303);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 x_304 = x_298;
} else {
 lean_dec_ref(x_298);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 1, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_303);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_306 = lean_unsigned_to_nat(1u);
x_307 = lean_nat_sub(x_294, x_306);
lean_dec(x_294);
if (lean_is_scalar(x_295)) {
 x_308 = lean_alloc_ctor(0, 1, 0);
} else {
 x_308 = x_295;
 lean_ctor_set_tag(x_308, 0);
}
lean_ctor_set(x_308, 0, x_307);
x_309 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_309, 0, x_308);
x_310 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_311 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_309, x_310, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
lean_dec_ref(x_311);
x_313 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_314 = lean_array_get_borrowed(x_313, x_292, x_296);
x_315 = lean_ctor_get(x_314, 0);
x_316 = lean_ctor_get(x_312, 0);
lean_inc(x_316);
lean_inc(x_315);
x_317 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_315, x_316, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; 
lean_dec_ref(x_317);
lean_inc(x_6);
x_318 = l_Lean_Compiler_LCNF_Simp_simp(x_293, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
lean_dec_ref(x_318);
x_320 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_292, x_6);
lean_dec(x_6);
lean_dec_ref(x_292);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_321 = x_320;
} else {
 lean_dec_ref(x_320);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_262;
}
lean_ctor_set(x_322, 0, x_312);
lean_ctor_set(x_322, 1, x_319);
if (lean_is_scalar(x_257)) {
 x_323 = lean_alloc_ctor(1, 1, 0);
} else {
 x_323 = x_257;
}
lean_ctor_set(x_323, 0, x_322);
if (lean_is_scalar(x_321)) {
 x_324 = lean_alloc_ctor(0, 1, 0);
} else {
 x_324 = x_321;
}
lean_ctor_set(x_324, 0, x_323);
return x_324;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_319);
lean_dec(x_312);
lean_dec(x_262);
lean_dec(x_257);
x_325 = lean_ctor_get(x_320, 0);
lean_inc(x_325);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_326 = x_320;
} else {
 lean_dec_ref(x_320);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 1, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_325);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_312);
lean_dec_ref(x_292);
lean_dec(x_262);
lean_dec(x_257);
lean_dec(x_6);
x_328 = lean_ctor_get(x_318, 0);
lean_inc(x_328);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_329 = x_318;
} else {
 lean_dec_ref(x_318);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 1, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_328);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_312);
lean_dec_ref(x_293);
lean_dec_ref(x_292);
lean_dec(x_262);
lean_dec(x_257);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_331 = lean_ctor_get(x_317, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 x_332 = x_317;
} else {
 lean_dec_ref(x_317);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 1, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_331);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec_ref(x_293);
lean_dec_ref(x_292);
lean_dec(x_262);
lean_dec(x_257);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_334 = lean_ctor_get(x_311, 0);
lean_inc(x_334);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 x_335 = x_311;
} else {
 lean_dec_ref(x_311);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 1, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_334);
return x_336;
}
}
}
}
else
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_262);
lean_dec(x_256);
x_337 = lean_ctor_get(x_260, 0);
lean_inc_ref(x_337);
lean_dec_ref(x_260);
x_338 = l_Lean_Compiler_LCNF_Simp_simp(x_337, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_340 = x_338;
} else {
 lean_dec_ref(x_338);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_341 = lean_alloc_ctor(1, 1, 0);
} else {
 x_341 = x_257;
}
lean_ctor_set(x_341, 0, x_339);
if (lean_is_scalar(x_340)) {
 x_342 = lean_alloc_ctor(0, 1, 0);
} else {
 x_342 = x_340;
}
lean_ctor_set(x_342, 0, x_341);
return x_342;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_257);
x_343 = lean_ctor_get(x_338, 0);
lean_inc(x_343);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_344 = x_338;
} else {
 lean_dec_ref(x_338);
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
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_346 = lean_ctor_get(x_264, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 x_347 = x_264;
} else {
 lean_dec_ref(x_264);
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
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_349 = lean_ctor_get(x_263, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_350 = x_263;
} else {
 lean_dec_ref(x_263);
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
lean_object* x_352; lean_object* x_353; 
lean_dec(x_255);
lean_free_object(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_352 = lean_box(0);
x_353 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_353, 0, x_352);
return x_353;
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
if (lean_obj_tag(x_359) == 1)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_360);
x_361 = lean_ctor_get(x_359, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 x_362 = x_359;
} else {
 lean_dec_ref(x_359);
 x_362 = lean_box(0);
}
x_363 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_361);
x_364 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_363);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_367 = x_364;
} else {
 lean_dec_ref(x_364);
 x_367 = lean_box(0);
}
x_368 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_368, 0, x_366);
x_369 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_368, x_6);
lean_dec_ref(x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; 
lean_dec_ref(x_369);
x_370 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_370) == 0)
{
lean_dec_ref(x_370);
if (lean_obj_tag(x_365) == 0)
{
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
lean_dec(x_367);
x_371 = lean_ctor_get(x_365, 1);
lean_inc_ref(x_371);
x_372 = lean_ctor_get(x_365, 2);
lean_inc_ref(x_372);
lean_dec_ref(x_365);
x_373 = lean_ctor_get(x_361, 0);
lean_inc_ref(x_373);
x_374 = lean_ctor_get(x_361, 1);
lean_inc_ref(x_374);
lean_dec_ref(x_361);
x_394 = lean_ctor_get(x_373, 3);
lean_inc(x_394);
lean_dec_ref(x_373);
x_395 = lean_unsigned_to_nat(0u);
x_396 = lean_array_get_size(x_374);
x_397 = lean_nat_dec_le(x_394, x_395);
if (x_397 == 0)
{
x_375 = x_394;
x_376 = x_396;
goto block_393;
}
else
{
lean_dec(x_394);
x_375 = x_395;
x_376 = x_396;
goto block_393;
}
block_393:
{
lean_object* x_377; size_t x_378; size_t x_379; lean_object* x_380; lean_object* x_381; 
x_377 = l_Array_toSubarray___redArg(x_374, x_375, x_376);
x_378 = lean_array_size(x_371);
x_379 = 0;
x_380 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_371, x_378, x_379, x_377, x_3);
lean_dec_ref(x_380);
lean_inc(x_6);
x_381 = l_Lean_Compiler_LCNF_Simp_simp(x_372, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
lean_dec_ref(x_381);
x_383 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_371, x_6);
lean_dec(x_6);
lean_dec_ref(x_371);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 x_384 = x_383;
} else {
 lean_dec_ref(x_383);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_385 = lean_alloc_ctor(1, 1, 0);
} else {
 x_385 = x_362;
}
lean_ctor_set(x_385, 0, x_382);
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(0, 1, 0);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_385);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_382);
lean_dec(x_362);
x_387 = lean_ctor_get(x_383, 0);
lean_inc(x_387);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 x_388 = x_383;
} else {
 lean_dec_ref(x_383);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 1, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_387);
return x_389;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec_ref(x_371);
lean_dec(x_362);
lean_dec(x_6);
x_390 = lean_ctor_get(x_381, 0);
lean_inc(x_390);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 x_391 = x_381;
} else {
 lean_dec_ref(x_381);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 1, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_390);
return x_392;
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_398 = lean_ctor_get(x_365, 1);
lean_inc_ref(x_398);
x_399 = lean_ctor_get(x_365, 2);
lean_inc_ref(x_399);
lean_dec_ref(x_365);
x_400 = lean_ctor_get(x_361, 0);
lean_inc(x_400);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 x_401 = x_361;
} else {
 lean_dec_ref(x_361);
 x_401 = lean_box(0);
}
x_402 = lean_unsigned_to_nat(0u);
x_403 = lean_nat_dec_eq(x_400, x_402);
if (x_403 == 1)
{
lean_object* x_404; 
lean_dec(x_401);
lean_dec(x_400);
lean_dec_ref(x_398);
lean_dec(x_367);
x_404 = l_Lean_Compiler_LCNF_Simp_simp(x_399, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 x_406 = x_404;
} else {
 lean_dec_ref(x_404);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_407 = lean_alloc_ctor(1, 1, 0);
} else {
 x_407 = x_362;
}
lean_ctor_set(x_407, 0, x_405);
if (lean_is_scalar(x_406)) {
 x_408 = lean_alloc_ctor(0, 1, 0);
} else {
 x_408 = x_406;
}
lean_ctor_set(x_408, 0, x_407);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_362);
x_409 = lean_ctor_get(x_404, 0);
lean_inc(x_409);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 x_410 = x_404;
} else {
 lean_dec_ref(x_404);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 1, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_409);
return x_411;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_412 = lean_unsigned_to_nat(1u);
x_413 = lean_nat_sub(x_400, x_412);
lean_dec(x_400);
if (lean_is_scalar(x_401)) {
 x_414 = lean_alloc_ctor(0, 1, 0);
} else {
 x_414 = x_401;
 lean_ctor_set_tag(x_414, 0);
}
lean_ctor_set(x_414, 0, x_413);
x_415 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_415, 0, x_414);
x_416 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_417 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_415, x_416, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
lean_dec_ref(x_417);
x_419 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_420 = lean_array_get_borrowed(x_419, x_398, x_402);
x_421 = lean_ctor_get(x_420, 0);
x_422 = lean_ctor_get(x_418, 0);
lean_inc(x_422);
lean_inc(x_421);
x_423 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_421, x_422, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; 
lean_dec_ref(x_423);
lean_inc(x_6);
x_424 = l_Lean_Compiler_LCNF_Simp_simp(x_399, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
lean_dec_ref(x_424);
x_426 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_398, x_6);
lean_dec(x_6);
lean_dec_ref(x_398);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_427 = x_426;
} else {
 lean_dec_ref(x_426);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_367;
}
lean_ctor_set(x_428, 0, x_418);
lean_ctor_set(x_428, 1, x_425);
if (lean_is_scalar(x_362)) {
 x_429 = lean_alloc_ctor(1, 1, 0);
} else {
 x_429 = x_362;
}
lean_ctor_set(x_429, 0, x_428);
if (lean_is_scalar(x_427)) {
 x_430 = lean_alloc_ctor(0, 1, 0);
} else {
 x_430 = x_427;
}
lean_ctor_set(x_430, 0, x_429);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_425);
lean_dec(x_418);
lean_dec(x_367);
lean_dec(x_362);
x_431 = lean_ctor_get(x_426, 0);
lean_inc(x_431);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_432 = x_426;
} else {
 lean_dec_ref(x_426);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(1, 1, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_431);
return x_433;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_418);
lean_dec_ref(x_398);
lean_dec(x_367);
lean_dec(x_362);
lean_dec(x_6);
x_434 = lean_ctor_get(x_424, 0);
lean_inc(x_434);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 x_435 = x_424;
} else {
 lean_dec_ref(x_424);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 1, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_434);
return x_436;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_418);
lean_dec_ref(x_399);
lean_dec_ref(x_398);
lean_dec(x_367);
lean_dec(x_362);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_437 = lean_ctor_get(x_423, 0);
lean_inc(x_437);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_438 = x_423;
} else {
 lean_dec_ref(x_423);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 1, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_437);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec_ref(x_399);
lean_dec_ref(x_398);
lean_dec(x_367);
lean_dec(x_362);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_440 = lean_ctor_get(x_417, 0);
lean_inc(x_440);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 x_441 = x_417;
} else {
 lean_dec_ref(x_417);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 1, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_440);
return x_442;
}
}
}
}
else
{
lean_object* x_443; lean_object* x_444; 
lean_dec(x_367);
lean_dec(x_361);
x_443 = lean_ctor_get(x_365, 0);
lean_inc_ref(x_443);
lean_dec_ref(x_365);
x_444 = l_Lean_Compiler_LCNF_Simp_simp(x_443, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 x_446 = x_444;
} else {
 lean_dec_ref(x_444);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_447 = lean_alloc_ctor(1, 1, 0);
} else {
 x_447 = x_362;
}
lean_ctor_set(x_447, 0, x_445);
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(0, 1, 0);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_447);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_362);
x_449 = lean_ctor_get(x_444, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 x_450 = x_444;
} else {
 lean_dec_ref(x_444);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 1, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_449);
return x_451;
}
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_367);
lean_dec(x_365);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_452 = lean_ctor_get(x_370, 0);
lean_inc(x_452);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 x_453 = x_370;
} else {
 lean_dec_ref(x_370);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 1, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_452);
return x_454;
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_367);
lean_dec(x_365);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_455 = lean_ctor_get(x_369, 0);
lean_inc(x_455);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 x_456 = x_369;
} else {
 lean_dec_ref(x_369);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 1, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_455);
return x_457;
}
}
else
{
lean_object* x_458; lean_object* x_459; 
lean_dec(x_359);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_458 = lean_box(0);
if (lean_is_scalar(x_360)) {
 x_459 = lean_alloc_ctor(0, 1, 0);
} else {
 x_459 = x_360;
}
lean_ctor_set(x_459, 0, x_458);
return x_459;
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
