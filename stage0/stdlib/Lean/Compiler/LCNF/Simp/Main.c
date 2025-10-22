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
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
uint8_t l_Lean_Compiler_LCNF_instBEqLetDecl_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_hasLocalInst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___boxed(lean_object**);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__0;
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__2;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2;
lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqLetValue_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getCode(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0;
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__1;
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object* x_1) {
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
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(x_1, x_2, x_7);
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
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_2, x_20);
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
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(x_25);
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
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(x_2, x_3, x_20);
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
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_2, x_52);
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
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(x_57);
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
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
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
x_25 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_10, x_21, x_22);
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
x_35 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_10, x_30, x_31);
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
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
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
x_54 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_40, x_49, x_50);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_3, x_4, x_5, x_6, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_8);
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
x_25 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_24, x_21, x_16, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = 0;
x_29 = l_Lean_Compiler_LCNF_mkAuxParam(x_26, x_28, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_15, x_33);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_34);
x_35 = lean_array_push(x_20, x_30);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_32);
lean_inc(x_23);
x_37 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_21, x_23, x_36);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_3, 0, x_35);
x_8 = x_31;
goto _start;
}
else
{
uint8_t x_39; 
lean_free_object(x_3);
lean_dec(x_21);
lean_dec(x_20);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_free_object(x_3);
lean_dec(x_21);
lean_dec(x_20);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
return x_25;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_25, 0);
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_25);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_3);
x_50 = lean_array_fget_borrowed(x_47, x_15);
x_51 = lean_ctor_get(x_50, 0);
x_52 = lean_ctor_get(x_50, 2);
lean_inc_ref(x_52);
x_53 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_52, x_49, x_16, x_8);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = 0;
x_57 = l_Lean_Compiler_LCNF_mkAuxParam(x_54, x_56, x_4, x_5, x_6, x_7, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_15, x_61);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_62);
x_63 = lean_array_push(x_48, x_58);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_60);
lean_inc(x_51);
x_65 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_49, x_51, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_3 = x_66;
x_8 = x_59;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_70 = x_57;
} else {
 lean_dec_ref(x_57);
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
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_72 = lean_ctor_get(x_53, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_53, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_74 = x_53;
} else {
 lean_dec_ref(x_53);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_9, 0);
lean_inc(x_76);
lean_dec(x_9);
x_77 = lean_nat_dec_lt(x_76, x_12);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_76);
lean_free_object(x_2);
lean_dec(x_12);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_3);
lean_ctor_set(x_78, 1, x_8);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_1, 0);
x_80 = lean_ctor_get(x_3, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_3, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_82 = x_3;
} else {
 lean_dec_ref(x_3);
 x_82 = lean_box(0);
}
x_83 = lean_array_fget_borrowed(x_79, x_76);
x_84 = lean_ctor_get(x_83, 0);
x_85 = lean_ctor_get(x_83, 2);
lean_inc_ref(x_85);
x_86 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_85, x_81, x_77, x_8);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec_ref(x_86);
x_89 = 0;
x_90 = l_Lean_Compiler_LCNF_mkAuxParam(x_87, x_89, x_4, x_5, x_6, x_7, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_76, x_94);
lean_dec(x_76);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_2, 0, x_96);
x_97 = lean_array_push(x_80, x_91);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
lean_inc(x_84);
x_99 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_81, x_84, x_98);
if (lean_is_scalar(x_82)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_82;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_3 = x_100;
x_8 = x_92;
goto _start;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_76);
lean_free_object(x_2);
lean_dec(x_12);
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_90, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_104 = x_90;
} else {
 lean_dec_ref(x_90);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_76);
lean_free_object(x_2);
lean_dec(x_12);
x_106 = lean_ctor_get(x_86, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_86, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_108 = x_86;
} else {
 lean_dec_ref(x_86);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_2, 1);
lean_inc(x_110);
lean_dec(x_2);
x_111 = lean_ctor_get(x_9, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_112 = x_9;
} else {
 lean_dec_ref(x_9);
 x_112 = lean_box(0);
}
x_113 = lean_nat_dec_lt(x_111, x_110);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_3);
lean_ctor_set(x_114, 1, x_8);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_1, 0);
x_116 = lean_ctor_get(x_3, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_3, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_118 = x_3;
} else {
 lean_dec_ref(x_3);
 x_118 = lean_box(0);
}
x_119 = lean_array_fget_borrowed(x_115, x_111);
x_120 = lean_ctor_get(x_119, 0);
x_121 = lean_ctor_get(x_119, 2);
lean_inc_ref(x_121);
x_122 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_121, x_117, x_113, x_8);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = 0;
x_126 = l_Lean_Compiler_LCNF_mkAuxParam(x_123, x_125, x_4, x_5, x_6, x_7, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_add(x_111, x_130);
lean_dec(x_111);
if (lean_is_scalar(x_112)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_112;
}
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_110);
x_134 = lean_array_push(x_116, x_127);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_129);
lean_inc(x_120);
x_136 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_117, x_120, x_135);
if (lean_is_scalar(x_118)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_118;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_136);
x_2 = x_133;
x_3 = x_137;
x_8 = x_128;
goto _start;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
x_139 = lean_ctor_get(x_126, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_126, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_141 = x_126;
} else {
 lean_dec_ref(x_126);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
x_143 = lean_ctor_get(x_122, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_122, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_145 = x_122;
} else {
 lean_dec_ref(x_122);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_1, x_6, x_7, x_13, x_14, x_15, x_16, x_17);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_61; uint8_t x_62; 
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
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_10, x_18, x_19, x_17, x_9);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_26 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
x_61 = lean_array_get_size(x_10);
x_62 = lean_nat_dec_le(x_15, x_13);
if (x_62 == 0)
{
x_27 = x_15;
x_28 = x_61;
goto block_60;
}
else
{
lean_dec(x_15);
x_27 = x_13;
x_28 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = l_Array_toSubarray___redArg(x_10, x_27, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 2);
lean_inc(x_31);
if (lean_is_scalar(x_25)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_25;
}
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_24);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
if (lean_is_scalar(x_23)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_23;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_29, x_34, x_32, x_5, x_6, x_7, x_8, x_22);
lean_dec_ref(x_29);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_40 = l_Lean_Compiler_LCNF_Code_internalize(x_11, x_39, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = 0;
lean_inc(x_41);
x_44 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_41, x_43, x_3, x_5, x_6, x_7, x_8, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_47 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_38, x_41, x_46, x_5, x_6, x_7, x_8, x_45);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
return x_40;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_40, 0);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_40);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
return x_35;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_35, 0);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_35);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___boxed(lean_object** _args) {
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
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
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
x_10 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(x_1, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec_ref(x_11);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_21, x_4, x_6, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_free_object(x_12);
lean_dec(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec_ref(x_22);
x_32 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_21, 2);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_21, 4);
lean_inc_ref(x_35);
lean_dec(x_21);
x_36 = 0;
x_37 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_34, x_35, x_2, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
lean_dec_ref(x_34);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_ctor_set(x_12, 0, x_39);
lean_ctor_set(x_37, 0, x_12);
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
lean_ctor_set(x_12, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_12);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_12);
lean_dec(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_47 = !lean_is_exclusive(x_32);
if (x_47 == 0)
{
return x_32;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_32, 0);
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_32);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_12);
lean_dec(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_12, 0);
lean_inc(x_55);
lean_dec(x_12);
x_56 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_55, x_4, x_6, x_19);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_55);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_60 = x_56;
} else {
 lean_dec_ref(x_56);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec_ref(x_56);
x_64 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = lean_ctor_get(x_55, 2);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_55, 4);
lean_inc_ref(x_67);
lean_dec(x_55);
x_68 = 0;
x_69 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_66, x_67, x_2, x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_65);
lean_dec_ref(x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
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
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_70);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_55);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_79 = lean_ctor_get(x_64, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_64, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_81 = x_64;
} else {
 lean_dec_ref(x_64);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_55);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_83 = lean_ctor_get(x_56, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_56, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_85 = x_56;
} else {
 lean_dec_ref(x_56);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_87 = !lean_is_exclusive(x_11);
if (x_87 == 0)
{
return x_11;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_11, 0);
x_89 = lean_ctor_get(x_11, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_11);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_ctor_get(x_13, 2);
x_20 = lean_st_ref_get(x_7, x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_24);
lean_dec(x_22);
x_25 = 0;
lean_inc(x_17);
x_26 = l_Lean_Environment_find_x3f(x_24, x_17, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = l_Lean_ConstantInfo_type(x_29);
lean_dec(x_29);
x_31 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_30, x_7, x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec_ref(x_31);
x_41 = l_Lean_Meta_isInstance___redArg(x_17, x_7, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec_ref(x_41);
lean_inc(x_17);
x_45 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_45, 1);
x_55 = lean_ctor_get(x_45, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_46);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_46, 0);
x_58 = lean_array_get_size(x_19);
x_59 = l_Lean_Compiler_LCNF_Decl_getArity(x_57);
lean_dec(x_57);
x_60 = lean_nat_dec_lt(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
lean_free_object(x_46);
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_61 = lean_box(0);
lean_ctor_set(x_45, 0, x_61);
return x_45;
}
else
{
lean_object* x_62; 
lean_free_object(x_45);
lean_inc_ref(x_16);
x_62 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = lean_array_size(x_63);
x_66 = 0;
lean_inc(x_63);
x_67 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_65, x_66, x_63);
x_68 = l_Array_append___redArg(x_19, x_67);
lean_dec_ref(x_67);
lean_ctor_set(x_13, 2, x_68);
x_69 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_70 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_69, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_73);
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_71);
x_74 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_75 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_63, x_20, x_74, x_4, x_5, x_6, x_7, x_72);
lean_dec_ref(x_4);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_inc(x_15);
x_79 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_78, x_3, x_5, x_6, x_7, x_77);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_80);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set(x_46, 0, x_76);
lean_ctor_set(x_81, 0, x_46);
return x_81;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
lean_ctor_set(x_46, 0, x_76);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_46);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_76);
lean_free_object(x_46);
x_86 = !lean_is_exclusive(x_81);
if (x_86 == 0)
{
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 0);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_81);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_76);
lean_free_object(x_46);
lean_dec(x_5);
lean_dec_ref(x_1);
x_90 = !lean_is_exclusive(x_79);
if (x_90 == 0)
{
return x_79;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_79, 0);
x_92 = lean_ctor_get(x_79, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_79);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_free_object(x_46);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_94 = !lean_is_exclusive(x_75);
if (x_94 == 0)
{
return x_75;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_75, 0);
x_96 = lean_ctor_get(x_75, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_75);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_63);
lean_free_object(x_46);
lean_free_object(x_26);
lean_free_object(x_20);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_98 = !lean_is_exclusive(x_70);
if (x_98 == 0)
{
return x_70;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_70, 0);
x_100 = lean_ctor_get(x_70, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_70);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_free_object(x_46);
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_102 = !lean_is_exclusive(x_62);
if (x_102 == 0)
{
return x_62;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_62, 0);
x_104 = lean_ctor_get(x_62, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_62);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_46, 0);
lean_inc(x_106);
lean_dec(x_46);
x_107 = lean_array_get_size(x_19);
x_108 = l_Lean_Compiler_LCNF_Decl_getArity(x_106);
lean_dec(x_106);
x_109 = lean_nat_dec_lt(x_107, x_108);
lean_dec(x_108);
lean_dec(x_107);
if (x_109 == 0)
{
lean_object* x_110; 
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_110 = lean_box(0);
lean_ctor_set(x_45, 0, x_110);
return x_45;
}
else
{
lean_object* x_111; 
lean_free_object(x_45);
lean_inc_ref(x_16);
x_111 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = lean_array_size(x_112);
x_115 = 0;
lean_inc(x_112);
x_116 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_114, x_115, x_112);
x_117 = l_Array_append___redArg(x_19, x_116);
lean_dec_ref(x_116);
lean_ctor_set(x_13, 2, x_117);
x_118 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_119 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_118, x_4, x_5, x_6, x_7, x_113);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_122);
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_120);
x_123 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_124 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_112, x_20, x_123, x_4, x_5, x_6, x_7, x_121);
lean_dec_ref(x_4);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_inc(x_15);
x_128 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_127, x_3, x_5, x_6, x_7, x_126);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_129);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_125);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_137 = x_130;
} else {
 lean_dec_ref(x_130);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_125);
lean_dec(x_5);
lean_dec_ref(x_1);
x_139 = lean_ctor_get(x_128, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_128, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_141 = x_128;
} else {
 lean_dec_ref(x_128);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_143 = lean_ctor_get(x_124, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_124, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_112);
lean_free_object(x_26);
lean_free_object(x_20);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_147 = lean_ctor_get(x_119, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_119, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_149 = x_119;
} else {
 lean_dec_ref(x_119);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_151 = lean_ctor_get(x_111, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_111, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_153 = x_111;
} else {
 lean_dec_ref(x_111);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_155 = lean_ctor_get(x_45, 1);
lean_inc(x_155);
lean_dec(x_45);
x_156 = lean_ctor_get(x_46, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_157 = x_46;
} else {
 lean_dec_ref(x_46);
 x_157 = lean_box(0);
}
x_158 = lean_array_get_size(x_19);
x_159 = l_Lean_Compiler_LCNF_Decl_getArity(x_156);
lean_dec(x_156);
x_160 = lean_nat_dec_lt(x_158, x_159);
lean_dec(x_159);
lean_dec(x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_157);
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_155);
return x_162;
}
else
{
lean_object* x_163; 
lean_inc_ref(x_16);
x_163 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7, x_155);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; size_t x_166; size_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec_ref(x_163);
x_166 = lean_array_size(x_164);
x_167 = 0;
lean_inc(x_164);
x_168 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_166, x_167, x_164);
x_169 = l_Array_append___redArg(x_19, x_168);
lean_dec_ref(x_168);
lean_ctor_set(x_13, 2, x_169);
x_170 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_171 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_170, x_4, x_5, x_6, x_7, x_165);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec_ref(x_171);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_174);
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_172);
x_175 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_176 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_164, x_20, x_175, x_4, x_5, x_6, x_7, x_173);
lean_dec_ref(x_4);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec_ref(x_176);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
lean_inc(x_15);
x_180 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_179, x_3, x_5, x_6, x_7, x_178);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_181);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_184 = x_182;
} else {
 lean_dec_ref(x_182);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_157;
}
lean_ctor_set(x_185, 0, x_177);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_183);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_177);
lean_dec(x_157);
x_187 = lean_ctor_get(x_182, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_182, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_189 = x_182;
} else {
 lean_dec_ref(x_182);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_177);
lean_dec(x_157);
lean_dec(x_5);
lean_dec_ref(x_1);
x_191 = lean_ctor_get(x_180, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_180, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_193 = x_180;
} else {
 lean_dec_ref(x_180);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_157);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_195 = lean_ctor_get(x_176, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_176, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_197 = x_176;
} else {
 lean_dec_ref(x_176);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_164);
lean_dec(x_157);
lean_free_object(x_26);
lean_free_object(x_20);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_199 = lean_ctor_get(x_171, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_171, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_201 = x_171;
} else {
 lean_dec_ref(x_171);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_157);
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_203 = lean_ctor_get(x_163, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_163, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_205 = x_163;
} else {
 lean_dec_ref(x_163);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
}
}
}
else
{
uint8_t x_207; 
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_207 = !lean_is_exclusive(x_45);
if (x_207 == 0)
{
return x_45;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_45, 0);
x_209 = lean_ctor_get(x_45, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_45);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_211 = !lean_is_exclusive(x_41);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_41, 0);
lean_dec(x_212);
x_213 = lean_box(0);
lean_ctor_set(x_41, 0, x_213);
return x_41;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_41, 1);
lean_inc(x_214);
lean_dec(x_41);
x_215 = lean_box(0);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
}
else
{
uint8_t x_217; 
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_217 = !lean_is_exclusive(x_41);
if (x_217 == 0)
{
return x_41;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_41, 0);
x_219 = lean_ctor_get(x_41, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_41);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
}
else
{
uint8_t x_221; 
lean_free_object(x_26);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_221 = !lean_is_exclusive(x_31);
if (x_221 == 0)
{
return x_31;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_31, 0);
x_223 = lean_ctor_get(x_31, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_31);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_26, 0);
lean_inc(x_225);
lean_dec(x_26);
x_226 = l_Lean_ConstantInfo_type(x_225);
lean_dec(x_225);
x_227 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_226, x_7, x_23);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; uint8_t x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_unbox(x_228);
lean_dec(x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_231 = x_227;
} else {
 lean_dec_ref(x_227);
 x_231 = lean_box(0);
}
x_232 = lean_box(0);
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_230);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_227, 1);
lean_inc(x_234);
lean_dec_ref(x_227);
x_235 = l_Lean_Meta_isInstance___redArg(x_17, x_7, x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; uint8_t x_237; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_unbox(x_236);
lean_dec(x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec_ref(x_235);
lean_inc(x_17);
x_239 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_242 = x_239;
} else {
 lean_dec_ref(x_239);
 x_242 = lean_box(0);
}
x_243 = lean_box(0);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_241);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_245 = lean_ctor_get(x_239, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_246 = x_239;
} else {
 lean_dec_ref(x_239);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_240, 0);
lean_inc(x_247);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 x_248 = x_240;
} else {
 lean_dec_ref(x_240);
 x_248 = lean_box(0);
}
x_249 = lean_array_get_size(x_19);
x_250 = l_Lean_Compiler_LCNF_Decl_getArity(x_247);
lean_dec(x_247);
x_251 = lean_nat_dec_lt(x_249, x_250);
lean_dec(x_250);
lean_dec(x_249);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_248);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_252 = lean_box(0);
if (lean_is_scalar(x_246)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_246;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_245);
return x_253;
}
else
{
lean_object* x_254; 
lean_dec(x_246);
lean_inc_ref(x_16);
x_254 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7, x_245);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; size_t x_257; size_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec_ref(x_254);
x_257 = lean_array_size(x_255);
x_258 = 0;
lean_inc(x_255);
x_259 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_257, x_258, x_255);
x_260 = l_Array_append___redArg(x_19, x_259);
lean_dec_ref(x_259);
lean_ctor_set(x_13, 2, x_260);
x_261 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_262 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_261, x_4, x_5, x_6, x_7, x_256);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec_ref(x_262);
x_265 = lean_ctor_get(x_263, 0);
lean_inc(x_265);
x_266 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_20, 1, x_266);
lean_ctor_set(x_20, 0, x_263);
x_267 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_268 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_255, x_20, x_267, x_4, x_5, x_6, x_7, x_264);
lean_dec_ref(x_4);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec_ref(x_268);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
lean_inc(x_15);
x_272 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_271, x_3, x_5, x_6, x_7, x_270);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
lean_dec_ref(x_272);
x_274 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_273);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_248;
}
lean_ctor_set(x_277, 0, x_269);
if (lean_is_scalar(x_276)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_276;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_275);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_269);
lean_dec(x_248);
x_279 = lean_ctor_get(x_274, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_274, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_281 = x_274;
} else {
 lean_dec_ref(x_274);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_269);
lean_dec(x_248);
lean_dec(x_5);
lean_dec_ref(x_1);
x_283 = lean_ctor_get(x_272, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_272, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_285 = x_272;
} else {
 lean_dec_ref(x_272);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_248);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_287 = lean_ctor_get(x_268, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_268, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_289 = x_268;
} else {
 lean_dec_ref(x_268);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_255);
lean_dec(x_248);
lean_free_object(x_20);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_291 = lean_ctor_get(x_262, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_262, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_293 = x_262;
} else {
 lean_dec_ref(x_262);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_248);
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_295 = lean_ctor_get(x_254, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_254, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_297 = x_254;
} else {
 lean_dec_ref(x_254);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_299 = lean_ctor_get(x_239, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_239, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_301 = x_239;
} else {
 lean_dec_ref(x_239);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_303 = lean_ctor_get(x_235, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_304 = x_235;
} else {
 lean_dec_ref(x_235);
 x_304 = lean_box(0);
}
x_305 = lean_box(0);
if (lean_is_scalar(x_304)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_304;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_303);
return x_306;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_307 = lean_ctor_get(x_235, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_235, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_309 = x_235;
} else {
 lean_dec_ref(x_235);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_free_object(x_20);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_311 = lean_ctor_get(x_227, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_227, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_313 = x_227;
} else {
 lean_dec_ref(x_227);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_315 = lean_ctor_get(x_20, 0);
x_316 = lean_ctor_get(x_20, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_20);
x_317 = lean_ctor_get(x_315, 0);
lean_inc_ref(x_317);
lean_dec(x_315);
x_318 = 0;
lean_inc(x_17);
x_319 = l_Lean_Environment_find_x3f(x_317, x_17, x_318);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_320 = lean_box(0);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_316);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_319, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 x_323 = x_319;
} else {
 lean_dec_ref(x_319);
 x_323 = lean_box(0);
}
x_324 = l_Lean_ConstantInfo_type(x_322);
lean_dec(x_322);
x_325 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_324, x_7, x_316);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; uint8_t x_327; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_unbox(x_326);
lean_dec(x_326);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_323);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_328 = lean_ctor_get(x_325, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_329 = x_325;
} else {
 lean_dec_ref(x_325);
 x_329 = lean_box(0);
}
x_330 = lean_box(0);
if (lean_is_scalar(x_329)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_329;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_328);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_325, 1);
lean_inc(x_332);
lean_dec_ref(x_325);
x_333 = l_Lean_Meta_isInstance___redArg(x_17, x_7, x_332);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; uint8_t x_335; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_unbox(x_334);
lean_dec(x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_333, 1);
lean_inc(x_336);
lean_dec_ref(x_333);
lean_inc(x_17);
x_337 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7, x_336);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_323);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_340 = x_337;
} else {
 lean_dec_ref(x_337);
 x_340 = lean_box(0);
}
x_341 = lean_box(0);
if (lean_is_scalar(x_340)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_340;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_339);
return x_342;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_343 = lean_ctor_get(x_337, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_344 = x_337;
} else {
 lean_dec_ref(x_337);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_338, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_346 = x_338;
} else {
 lean_dec_ref(x_338);
 x_346 = lean_box(0);
}
x_347 = lean_array_get_size(x_19);
x_348 = l_Lean_Compiler_LCNF_Decl_getArity(x_345);
lean_dec(x_345);
x_349 = lean_nat_dec_lt(x_347, x_348);
lean_dec(x_348);
lean_dec(x_347);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_346);
lean_dec(x_323);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_350 = lean_box(0);
if (lean_is_scalar(x_344)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_344;
}
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_343);
return x_351;
}
else
{
lean_object* x_352; 
lean_dec(x_344);
lean_inc_ref(x_16);
x_352 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7, x_343);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; size_t x_355; size_t x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec_ref(x_352);
x_355 = lean_array_size(x_353);
x_356 = 0;
lean_inc(x_353);
x_357 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_355, x_356, x_353);
x_358 = l_Array_append___redArg(x_19, x_357);
lean_dec_ref(x_357);
lean_ctor_set(x_13, 2, x_358);
x_359 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_360 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_359, x_4, x_5, x_6, x_7, x_354);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec_ref(x_360);
x_363 = lean_ctor_get(x_361, 0);
lean_inc(x_363);
if (lean_is_scalar(x_323)) {
 x_364 = lean_alloc_ctor(5, 1, 0);
} else {
 x_364 = x_323;
 lean_ctor_set_tag(x_364, 5);
}
lean_ctor_set(x_364, 0, x_363);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_361);
lean_ctor_set(x_365, 1, x_364);
x_366 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_367 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_353, x_365, x_366, x_4, x_5, x_6, x_7, x_362);
lean_dec_ref(x_4);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec_ref(x_367);
x_370 = lean_ctor_get(x_368, 0);
lean_inc(x_370);
lean_inc(x_15);
x_371 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_370, x_3, x_5, x_6, x_7, x_369);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
lean_dec_ref(x_371);
x_373 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_372);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_374 = lean_ctor_get(x_373, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_375 = x_373;
} else {
 lean_dec_ref(x_373);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_376 = lean_alloc_ctor(1, 1, 0);
} else {
 x_376 = x_346;
}
lean_ctor_set(x_376, 0, x_368);
if (lean_is_scalar(x_375)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_375;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_374);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_368);
lean_dec(x_346);
x_378 = lean_ctor_get(x_373, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_373, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_380 = x_373;
} else {
 lean_dec_ref(x_373);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_378);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_368);
lean_dec(x_346);
lean_dec(x_5);
lean_dec_ref(x_1);
x_382 = lean_ctor_get(x_371, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_371, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_384 = x_371;
} else {
 lean_dec_ref(x_371);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_382);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_346);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_386 = lean_ctor_get(x_367, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_367, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_388 = x_367;
} else {
 lean_dec_ref(x_367);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_387);
return x_389;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_353);
lean_dec(x_346);
lean_dec(x_323);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_390 = lean_ctor_get(x_360, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_360, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_392 = x_360;
} else {
 lean_dec_ref(x_360);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_391);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_346);
lean_dec(x_323);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_394 = lean_ctor_get(x_352, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_352, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_396 = x_352;
} else {
 lean_dec_ref(x_352);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_395);
return x_397;
}
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_323);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_398 = lean_ctor_get(x_337, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_337, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_400 = x_337;
} else {
 lean_dec_ref(x_337);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_323);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_402 = lean_ctor_get(x_333, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_403 = x_333;
} else {
 lean_dec_ref(x_333);
 x_403 = lean_box(0);
}
x_404 = lean_box(0);
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_403;
}
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_402);
return x_405;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_323);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_406 = lean_ctor_get(x_333, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_333, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_408 = x_333;
} else {
 lean_dec_ref(x_333);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_323);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_410 = lean_ctor_get(x_325, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_325, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_412 = x_325;
} else {
 lean_dec_ref(x_325);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 2, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_411);
return x_413;
}
}
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; 
x_414 = lean_ctor_get(x_1, 0);
x_415 = lean_ctor_get(x_1, 2);
x_416 = lean_ctor_get(x_13, 0);
x_417 = lean_ctor_get(x_13, 1);
x_418 = lean_ctor_get(x_13, 2);
lean_inc(x_418);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_13);
x_419 = lean_st_ref_get(x_7, x_8);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_422 = x_419;
} else {
 lean_dec_ref(x_419);
 x_422 = lean_box(0);
}
x_423 = lean_ctor_get(x_420, 0);
lean_inc_ref(x_423);
lean_dec(x_420);
x_424 = 0;
lean_inc(x_416);
x_425 = l_Lean_Environment_find_x3f(x_423, x_416, x_424);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; 
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_426 = lean_box(0);
if (lean_is_scalar(x_422)) {
 x_427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_427 = x_422;
}
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_421);
return x_427;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_428 = lean_ctor_get(x_425, 0);
lean_inc(x_428);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 x_429 = x_425;
} else {
 lean_dec_ref(x_425);
 x_429 = lean_box(0);
}
x_430 = l_Lean_ConstantInfo_type(x_428);
lean_dec(x_428);
x_431 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_430, x_7, x_421);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_unbox(x_432);
lean_dec(x_432);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_429);
lean_dec(x_422);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_435 = x_431;
} else {
 lean_dec_ref(x_431);
 x_435 = lean_box(0);
}
x_436 = lean_box(0);
if (lean_is_scalar(x_435)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_435;
}
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_434);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; 
x_438 = lean_ctor_get(x_431, 1);
lean_inc(x_438);
lean_dec_ref(x_431);
x_439 = l_Lean_Meta_isInstance___redArg(x_416, x_7, x_438);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; uint8_t x_441; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_unbox(x_440);
lean_dec(x_440);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; 
x_442 = lean_ctor_get(x_439, 1);
lean_inc(x_442);
lean_dec_ref(x_439);
lean_inc(x_416);
x_443 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_416, x_4, x_7, x_442);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_429);
lean_dec(x_422);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_446 = x_443;
} else {
 lean_dec_ref(x_443);
 x_446 = lean_box(0);
}
x_447 = lean_box(0);
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_445);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; 
x_449 = lean_ctor_get(x_443, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_450 = x_443;
} else {
 lean_dec_ref(x_443);
 x_450 = lean_box(0);
}
x_451 = lean_ctor_get(x_444, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 x_452 = x_444;
} else {
 lean_dec_ref(x_444);
 x_452 = lean_box(0);
}
x_453 = lean_array_get_size(x_418);
x_454 = l_Lean_Compiler_LCNF_Decl_getArity(x_451);
lean_dec(x_451);
x_455 = lean_nat_dec_lt(x_453, x_454);
lean_dec(x_454);
lean_dec(x_453);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; 
lean_dec(x_452);
lean_dec(x_429);
lean_dec(x_422);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_456 = lean_box(0);
if (lean_is_scalar(x_450)) {
 x_457 = lean_alloc_ctor(0, 2, 0);
} else {
 x_457 = x_450;
}
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_449);
return x_457;
}
else
{
lean_object* x_458; 
lean_dec(x_450);
lean_inc_ref(x_415);
x_458 = l_Lean_Compiler_LCNF_mkNewParams(x_415, x_4, x_5, x_6, x_7, x_449);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; size_t x_461; size_t x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec_ref(x_458);
x_461 = lean_array_size(x_459);
x_462 = 0;
lean_inc(x_459);
x_463 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_461, x_462, x_459);
x_464 = l_Array_append___redArg(x_418, x_463);
lean_dec_ref(x_463);
x_465 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_465, 0, x_416);
lean_ctor_set(x_465, 1, x_417);
lean_ctor_set(x_465, 2, x_464);
x_466 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_467 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_465, x_466, x_4, x_5, x_6, x_7, x_460);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec_ref(x_467);
x_470 = lean_ctor_get(x_468, 0);
lean_inc(x_470);
if (lean_is_scalar(x_429)) {
 x_471 = lean_alloc_ctor(5, 1, 0);
} else {
 x_471 = x_429;
 lean_ctor_set_tag(x_471, 5);
}
lean_ctor_set(x_471, 0, x_470);
if (lean_is_scalar(x_422)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_422;
}
lean_ctor_set(x_472, 0, x_468);
lean_ctor_set(x_472, 1, x_471);
x_473 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_474 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_459, x_472, x_473, x_4, x_5, x_6, x_7, x_469);
lean_dec_ref(x_4);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec_ref(x_474);
x_477 = lean_ctor_get(x_475, 0);
lean_inc(x_477);
lean_inc(x_414);
x_478 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_414, x_477, x_3, x_5, x_6, x_7, x_476);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_478, 1);
lean_inc(x_479);
lean_dec_ref(x_478);
x_480 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_479);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_481 = lean_ctor_get(x_480, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_482 = x_480;
} else {
 lean_dec_ref(x_480);
 x_482 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_483 = lean_alloc_ctor(1, 1, 0);
} else {
 x_483 = x_452;
}
lean_ctor_set(x_483, 0, x_475);
if (lean_is_scalar(x_482)) {
 x_484 = lean_alloc_ctor(0, 2, 0);
} else {
 x_484 = x_482;
}
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_481);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_475);
lean_dec(x_452);
x_485 = lean_ctor_get(x_480, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_480, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_487 = x_480;
} else {
 lean_dec_ref(x_480);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_485);
lean_ctor_set(x_488, 1, x_486);
return x_488;
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_475);
lean_dec(x_452);
lean_dec(x_5);
lean_dec_ref(x_1);
x_489 = lean_ctor_get(x_478, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_478, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_491 = x_478;
} else {
 lean_dec_ref(x_478);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_490);
return x_492;
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_452);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_493 = lean_ctor_get(x_474, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_474, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_495 = x_474;
} else {
 lean_dec_ref(x_474);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_459);
lean_dec(x_452);
lean_dec(x_429);
lean_dec(x_422);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_497 = lean_ctor_get(x_467, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_467, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_499 = x_467;
} else {
 lean_dec_ref(x_467);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_452);
lean_dec(x_429);
lean_dec(x_422);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_501 = lean_ctor_get(x_458, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_458, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_503 = x_458;
} else {
 lean_dec_ref(x_458);
 x_503 = lean_box(0);
}
if (lean_is_scalar(x_503)) {
 x_504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_504 = x_503;
}
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_502);
return x_504;
}
}
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_429);
lean_dec(x_422);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_505 = lean_ctor_get(x_443, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_443, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_507 = x_443;
} else {
 lean_dec_ref(x_443);
 x_507 = lean_box(0);
}
if (lean_is_scalar(x_507)) {
 x_508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_508 = x_507;
}
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_506);
return x_508;
}
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_429);
lean_dec(x_422);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_509 = lean_ctor_get(x_439, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_510 = x_439;
} else {
 lean_dec_ref(x_439);
 x_510 = lean_box(0);
}
x_511 = lean_box(0);
if (lean_is_scalar(x_510)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_510;
}
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_509);
return x_512;
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_429);
lean_dec(x_422);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_513 = lean_ctor_get(x_439, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_439, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_515 = x_439;
} else {
 lean_dec_ref(x_439);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(1, 2, 0);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_513);
lean_ctor_set(x_516, 1, x_514);
return x_516;
}
}
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_429);
lean_dec(x_422);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_517 = lean_ctor_get(x_431, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_431, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_519 = x_431;
} else {
 lean_dec_ref(x_431);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(1, 2, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_517);
lean_ctor_set(x_520, 1, x_518);
return x_520;
}
}
}
}
else
{
lean_object* x_521; lean_object* x_522; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_521 = lean_box(0);
x_522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_8);
return x_522;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_st_ref_get(x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Lean_Compiler_LCNF_normFVarImp(x_9, x_5, x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_instBEqFVarId_beq(x_12, x_2);
lean_dec(x_12);
x_14 = lean_box(x_13);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; 
x_15 = lean_box(x_10);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = l_Lean_Compiler_LCNF_normFVarImp(x_18, x_5, x_19);
lean_dec_ref(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_instBEqFVarId_beq(x_21, x_2);
lean_dec(x_21);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
}
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_1);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(x_1, x_2, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_isReturnOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 4)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_array_get_size(x_9);
lean_dec_ref(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_free_object(x_1);
lean_dec(x_8);
x_3 = x_2;
goto block_6;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_array_get_size(x_15);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_dec(x_14);
x_3 = x_2;
goto block_6;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
}
else
{
lean_dec(x_1);
x_3 = x_2;
goto block_6;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_19 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1;
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
x_38 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_35, x_36, x_37, x_4, x_5);
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
x_42 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_39, x_40, x_41, x_4, x_5);
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
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(x_3, x_48, x_49, x_50, x_51);
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
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(x_61, x_4, x_5);
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
x_67 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(x_3, x_64, x_65, x_66, x_67);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_38; 
x_38 = lean_nat_dec_lt(x_1, x_2);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_39 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3, x_6, x_8, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Compiler_LCNF_Simp_simp(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_40);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_le(x_1, x_46);
if (x_47 == 0)
{
x_15 = x_1;
x_16 = x_2;
goto block_37;
}
else
{
lean_dec(x_1);
x_15 = x_46;
x_16 = x_2;
goto block_37;
}
}
block_37:
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
x_21 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_19, x_20, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3, x_24, x_8, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_4);
x_28 = l_Lean_Compiler_LCNF_Simp_simp(x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_5, x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_apply_9(x_2, x_5, x_3, x_1, x_4, x_6, x_7, x_8, x_9, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_13 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_22 = x_14;
} else {
 lean_dec_ref(x_14);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec_ref(x_13);
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_21, 2);
x_27 = lean_ctor_get(x_21, 3);
x_28 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 2);
x_29 = lean_array_get_size(x_27);
x_30 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_21);
lean_inc_ref(x_27);
lean_inc_ref(x_2);
lean_inc(x_11);
lean_inc(x_29);
lean_inc(x_30);
x_31 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0), 14, 5);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_29);
lean_closure_set(x_31, 2, x_11);
lean_closure_set(x_31, 3, x_2);
lean_closure_set(x_31, 4, x_27);
x_32 = lean_nat_dec_lt(x_29, x_30);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_12, 0);
lean_inc(x_246);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_246);
x_247 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(x_28, x_246, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec_ref(x_247);
x_250 = !lean_is_exclusive(x_3);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_3, 2);
x_252 = lean_ctor_get(x_3, 3);
lean_inc(x_246);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_246);
lean_ctor_set(x_253, 1, x_251);
x_254 = l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_252, x_246, x_248);
lean_ctor_set(x_3, 3, x_254);
lean_ctor_set(x_3, 2, x_253);
x_201 = x_3;
x_202 = x_4;
x_203 = x_5;
x_204 = x_6;
x_205 = x_7;
x_206 = x_8;
x_207 = x_9;
x_208 = x_249;
goto block_245;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_255 = lean_ctor_get(x_3, 0);
x_256 = lean_ctor_get(x_3, 1);
x_257 = lean_ctor_get(x_3, 2);
x_258 = lean_ctor_get(x_3, 3);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_3);
lean_inc(x_246);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_246);
lean_ctor_set(x_259, 1, x_257);
x_260 = l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_258, x_246, x_248);
x_261 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_261, 0, x_255);
lean_ctor_set(x_261, 1, x_256);
lean_ctor_set(x_261, 2, x_259);
lean_ctor_set(x_261, 3, x_260);
x_201 = x_261;
x_202 = x_4;
x_203 = x_5;
x_204 = x_6;
x_205 = x_7;
x_206 = x_8;
x_207 = x_9;
x_208 = x_249;
goto block_245;
}
}
else
{
uint8_t x_262; 
lean_dec(x_246);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_262 = !lean_is_exclusive(x_247);
if (x_262 == 0)
{
return x_247;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_247, 0);
x_264 = lean_ctor_get(x_247, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_247);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
lean_dec(x_12);
x_201 = x_3;
x_202 = x_4;
x_203 = x_5;
x_204 = x_6;
x_205 = x_7;
x_206 = x_8;
x_207 = x_9;
x_208 = x_23;
goto block_245;
}
block_159:
{
lean_object* x_44; 
lean_inc(x_41);
lean_inc_ref(x_38);
lean_inc(x_42);
lean_inc_ref(x_39);
lean_inc_ref(x_43);
lean_inc(x_33);
lean_inc_ref(x_34);
x_44 = l_Lean_Compiler_LCNF_Simp_simp(x_35, x_34, x_33, x_43, x_39, x_42, x_38, x_41, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_33, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc(x_45);
x_49 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_45);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec_ref(x_36);
x_50 = l_Lean_Compiler_LCNF_inferAppType(x_26, x_40, x_39, x_42, x_38, x_41, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
lean_inc(x_51);
x_53 = l_Lean_Expr_headBeta(x_51);
x_54 = l_Lean_Expr_isForall(x_53);
lean_dec_ref(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Lean_Compiler_LCNF_mkAuxParam(x_51, x_32, x_39, x_42, x_38, x_41, x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_41);
lean_inc_ref(x_38);
lean_inc(x_42);
lean_inc_ref(x_39);
lean_inc(x_58);
x_59 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_30, x_29, x_11, x_2, x_27, x_58, x_34, x_33, x_43, x_39, x_42, x_38, x_41, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_unsigned_to_nat(1u);
x_63 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_64 = lean_array_push(x_63, x_56);
x_65 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_66 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_64, x_60, x_65, x_39, x_42, x_38, x_41, x_61);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
lean_inc(x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_62);
x_70 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_45, x_69, x_39, x_42, x_38, x_41, x_68);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_22)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_22;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_70, 0, x_74);
return x_70;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_70, 0);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_70);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_75);
if (lean_is_scalar(x_22)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_22;
}
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_67);
lean_dec(x_22);
x_80 = !lean_is_exclusive(x_70);
if (x_80 == 0)
{
return x_70;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_70, 0);
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_70);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_22);
x_84 = !lean_is_exclusive(x_66);
if (x_84 == 0)
{
return x_66;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_66, 0);
x_86 = lean_ctor_get(x_66, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_66);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_56);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_22);
x_88 = !lean_is_exclusive(x_59);
if (x_88 == 0)
{
return x_59;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_59, 0);
x_90 = lean_ctor_get(x_59, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_59);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_45);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_92 = !lean_is_exclusive(x_55);
if (x_92 == 0)
{
return x_55;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_55, 0);
x_94 = lean_ctor_get(x_55, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_55);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_51);
x_96 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
x_97 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_98 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_96, x_45, x_97, x_39, x_42, x_38, x_41, x_52);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
lean_inc(x_41);
lean_inc_ref(x_38);
lean_inc(x_42);
lean_inc_ref(x_39);
x_101 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_99, x_39, x_42, x_38, x_41, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_41);
lean_inc_ref(x_38);
lean_inc(x_42);
lean_inc_ref(x_39);
lean_inc_ref(x_43);
lean_inc(x_33);
lean_inc_ref(x_34);
lean_inc(x_104);
x_105 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_30, x_29, x_11, x_2, x_27, x_104, x_34, x_33, x_43, x_39, x_42, x_38, x_41, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_102);
x_109 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_110 = lean_array_push(x_109, x_108);
x_111 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_110, x_106, x_34, x_33, x_43, x_39, x_42, x_38, x_41, x_107);
lean_dec(x_41);
lean_dec_ref(x_38);
lean_dec(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_43);
lean_dec(x_33);
lean_dec_ref(x_34);
lean_dec_ref(x_110);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
if (lean_is_scalar(x_22)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_22;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_111, 0, x_114);
return x_111;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_111, 0);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_111);
if (lean_is_scalar(x_22)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_22;
}
lean_ctor_set(x_117, 0, x_115);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
uint8_t x_119; 
lean_dec(x_22);
x_119 = !lean_is_exclusive(x_111);
if (x_119 == 0)
{
return x_111;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_111, 0);
x_121 = lean_ctor_get(x_111, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_111);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_102);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_22);
x_123 = !lean_is_exclusive(x_105);
if (x_123 == 0)
{
return x_105;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_105, 0);
x_125 = lean_ctor_get(x_105, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_105);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_127 = !lean_is_exclusive(x_101);
if (x_127 == 0)
{
return x_101;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_101, 0);
x_129 = lean_ctor_get(x_101, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_101);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_131 = !lean_is_exclusive(x_98);
if (x_131 == 0)
{
return x_98;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_98, 0);
x_133 = lean_ctor_get(x_98, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_98);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_45);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_135 = !lean_is_exclusive(x_50);
if (x_135 == 0)
{
return x_50;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_50, 0);
x_137 = lean_ctor_get(x_50, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_50);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; 
lean_dec_ref(x_43);
lean_dec_ref(x_40);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_11);
lean_dec_ref(x_2);
x_139 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_45, x_36, x_39, x_42, x_38, x_41, x_48);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_139, 0);
if (lean_is_scalar(x_22)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_22;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_139, 0, x_142);
return x_139;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_139, 0);
x_144 = lean_ctor_get(x_139, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_139);
if (lean_is_scalar(x_22)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_22;
}
lean_ctor_set(x_145, 0, x_143);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
uint8_t x_147; 
lean_dec(x_22);
x_147 = !lean_is_exclusive(x_139);
if (x_147 == 0)
{
return x_139;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_139, 0);
x_149 = lean_ctor_get(x_139, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_139);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_45);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_151 = !lean_is_exclusive(x_47);
if (x_151 == 0)
{
return x_47;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_47, 0);
x_153 = lean_ctor_get(x_47, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_47);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
uint8_t x_155; 
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_155 = !lean_is_exclusive(x_44);
if (x_155 == 0)
{
return x_44;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_44, 0);
x_157 = lean_ctor_get(x_44, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_44);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
block_200:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_inc_ref(x_27);
x_171 = l_Array_toSubarray___redArg(x_27, x_169, x_170);
x_172 = l_Array_ofSubarray___redArg(x_171);
lean_dec_ref(x_171);
lean_inc(x_166);
lean_inc_ref(x_164);
lean_inc(x_167);
lean_inc_ref(x_165);
lean_inc_ref(x_172);
x_173 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_24, x_25, x_172, x_32, x_161, x_160, x_168, x_165, x_167, x_164, x_166, x_163);
lean_dec_ref(x_24);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec_ref(x_173);
x_176 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_11);
if (x_176 == 0)
{
x_33 = x_160;
x_34 = x_161;
x_35 = x_174;
x_36 = x_162;
x_37 = x_175;
x_38 = x_164;
x_39 = x_165;
x_40 = x_172;
x_41 = x_166;
x_42 = x_167;
x_43 = x_168;
goto block_159;
}
else
{
uint8_t x_177; 
x_177 = lean_nat_dec_eq(x_29, x_30);
if (x_177 == 0)
{
x_33 = x_160;
x_34 = x_161;
x_35 = x_174;
x_36 = x_162;
x_37 = x_175;
x_38 = x_164;
x_39 = x_165;
x_40 = x_172;
x_41 = x_166;
x_42 = x_167;
x_43 = x_168;
goto block_159;
}
else
{
lean_object* x_178; 
lean_dec_ref(x_172);
lean_dec_ref(x_162);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_178 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_160, x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec_ref(x_178);
x_180 = l_Lean_Compiler_LCNF_Simp_simp(x_174, x_161, x_160, x_168, x_165, x_167, x_164, x_166, x_179);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_180, 0, x_183);
return x_180;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_180, 0);
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_180);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_184);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_180);
if (x_188 == 0)
{
return x_180;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_180, 0);
x_190 = lean_ctor_get(x_180, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_180);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_174);
lean_dec_ref(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec_ref(x_165);
lean_dec_ref(x_164);
lean_dec_ref(x_161);
lean_dec(x_160);
x_192 = !lean_is_exclusive(x_178);
if (x_192 == 0)
{
return x_178;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_178, 0);
x_194 = lean_ctor_get(x_178, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_178);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
}
else
{
uint8_t x_196; 
lean_dec_ref(x_172);
lean_dec_ref(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec_ref(x_165);
lean_dec_ref(x_164);
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_196 = !lean_is_exclusive(x_173);
if (x_196 == 0)
{
return x_173;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_173, 0);
x_198 = lean_ctor_get(x_173, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_173);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
block_245:
{
if (x_32 == 0)
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; 
lean_inc_ref(x_27);
lean_inc_ref(x_26);
lean_inc_ref(x_25);
lean_inc_ref(x_24);
lean_dec(x_21);
lean_inc_ref(x_203);
lean_inc_ref(x_201);
lean_inc(x_202);
x_209 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2), 10, 4);
lean_closure_set(x_209, 0, x_202);
lean_closure_set(x_209, 1, x_31);
lean_closure_set(x_209, 2, x_201);
lean_closure_set(x_209, 3, x_203);
x_210 = lean_unsigned_to_nat(0u);
x_211 = lean_nat_dec_le(x_30, x_29);
if (x_211 == 0)
{
lean_inc(x_29);
x_160 = x_202;
x_161 = x_201;
x_162 = x_209;
x_163 = x_208;
x_164 = x_206;
x_165 = x_204;
x_166 = x_207;
x_167 = x_205;
x_168 = x_203;
x_169 = x_210;
x_170 = x_29;
goto block_200;
}
else
{
lean_inc(x_30);
x_160 = x_202;
x_161 = x_201;
x_162 = x_209;
x_163 = x_208;
x_164 = x_206;
x_165 = x_204;
x_166 = x_207;
x_167 = x_205;
x_168 = x_203;
x_169 = x_210;
x_170 = x_30;
goto block_200;
}
}
else
{
lean_object* x_212; 
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_22);
lean_inc(x_207);
lean_inc_ref(x_206);
lean_inc(x_205);
lean_inc_ref(x_204);
x_212 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_201, x_202, x_203, x_204, x_205, x_206, x_207, x_208);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec_ref(x_212);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
x_216 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_215, x_202, x_205, x_206, x_207, x_214);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec_ref(x_216);
x_218 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_202, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec_ref(x_218);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_213);
lean_ctor_set(x_220, 1, x_2);
x_221 = l_Lean_Compiler_LCNF_Simp_simp(x_220, x_201, x_202, x_203, x_204, x_205, x_206, x_207, x_219);
if (lean_obj_tag(x_221) == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_221, 0, x_224);
return x_221;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_221, 0);
x_226 = lean_ctor_get(x_221, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_221);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_225);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
else
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_221);
if (x_229 == 0)
{
return x_221;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_221, 0);
x_231 = lean_ctor_get(x_221, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_221);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_213);
lean_dec(x_207);
lean_dec_ref(x_206);
lean_dec(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec_ref(x_2);
x_233 = !lean_is_exclusive(x_218);
if (x_233 == 0)
{
return x_218;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_218, 0);
x_235 = lean_ctor_get(x_218, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_218);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
uint8_t x_237; 
lean_dec(x_213);
lean_dec(x_207);
lean_dec_ref(x_206);
lean_dec(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec_ref(x_2);
x_237 = !lean_is_exclusive(x_216);
if (x_237 == 0)
{
return x_216;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_216, 0);
x_239 = lean_ctor_get(x_216, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_216);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_207);
lean_dec_ref(x_206);
lean_dec(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec(x_11);
lean_dec_ref(x_2);
x_241 = !lean_is_exclusive(x_212);
if (x_241 == 0)
{
return x_212;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_212, 0);
x_243 = lean_ctor_get(x_212, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_212);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
}
}
}
else
{
uint8_t x_266; 
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
x_266 = !lean_is_exclusive(x_13);
if (x_266 == 0)
{
return x_13;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_13, 0);
x_268 = lean_ctor_get(x_13, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_13);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_st_ref_get(x_3, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
lean_inc_ref(x_6);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_11, x_1, x_6);
lean_dec_ref(x_11);
lean_inc(x_7);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_15, x_7, x_1);
lean_dec_ref(x_15);
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(x_2, x_16, x_17, x_4, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_1, x_2, x_4, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_8, x_2, x_1);
lean_dec_ref(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_12, x_2, x_1);
lean_dec_ref(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1, x_2, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(x_8, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1, x_2, x_3, x_4, x_6, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(x_8, x_4, x_5);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
return x_19;
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
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_2, x_3, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget_borrowed(x_4, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_50; uint8_t x_51; uint8_t x_74; lean_object* x_75; uint8_t x_77; lean_object* x_78; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
x_32 = lean_ctor_get(x_16, 2);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_array_get_size(x_31);
x_82 = lean_nat_dec_lt(x_80, x_81);
if (x_82 == 0)
{
lean_dec(x_81);
x_77 = x_2;
x_78 = x_12;
goto block_79;
}
else
{
if (x_82 == 0)
{
lean_dec(x_81);
x_77 = x_2;
x_78 = x_12;
goto block_79;
}
else
{
size_t x_83; size_t x_84; lean_object* x_85; 
x_83 = 0;
x_84 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_85 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_31, x_83, x_84, x_11, x_12);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = lean_unbox(x_86);
lean_dec(x_86);
x_77 = x_88;
x_78 = x_87;
goto block_79;
}
else
{
uint8_t x_89; 
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
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 0);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_85);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
block_49:
{
lean_object* x_34; 
lean_inc_ref(x_10);
lean_inc_ref(x_7);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc(x_1);
x_34 = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_30, x_31, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_32);
x_37 = l_Lean_Compiler_LCNF_Simp_simp(x_32, x_5, x_6, x_35, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
lean_inc_ref(x_16);
x_40 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_38);
x_17 = x_40;
x_18 = x_39;
goto block_29;
}
else
{
uint8_t x_41; 
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
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
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
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
block_73:
{
if (x_51 == 0)
{
x_33 = x_50;
goto block_49;
}
else
{
lean_object* x_52; 
lean_inc_ref(x_32);
x_52 = l_Lean_Compiler_LCNF_Code_inferType(x_32, x_8, x_9, x_10, x_11, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_32, x_9, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_6, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_59, 0, x_53);
lean_inc_ref(x_16);
x_60 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_59);
x_17 = x_60;
x_18 = x_58;
goto block_29;
}
else
{
uint8_t x_61; 
lean_dec(x_53);
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
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_53);
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
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
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
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
block_76:
{
if (x_2 == 0)
{
x_33 = x_75;
goto block_49;
}
else
{
x_50 = x_75;
x_51 = x_74;
goto block_73;
}
}
block_79:
{
if (lean_obj_tag(x_32) == 6)
{
x_74 = x_77;
x_75 = x_78;
goto block_76;
}
else
{
if (x_2 == 0)
{
x_50 = x_78;
x_51 = x_77;
goto block_73;
}
else
{
x_74 = x_77;
x_75 = x_78;
goto block_76;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_16, 0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_93);
x_94 = l_Lean_Compiler_LCNF_Simp_simp(x_93, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
lean_inc_ref(x_16);
x_97 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_95);
x_17 = x_97;
x_18 = x_96;
goto block_29;
}
else
{
uint8_t x_98; 
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
x_98 = !lean_is_exclusive(x_94);
if (x_98 == 0)
{
return x_94;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_94, 0);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_94);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
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
x_12 = x_18;
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
x_12 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget_borrowed(x_4, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_50; uint8_t x_51; uint8_t x_74; lean_object* x_75; uint8_t x_77; lean_object* x_78; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
x_32 = lean_ctor_get(x_16, 2);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_array_get_size(x_31);
x_82 = lean_nat_dec_lt(x_80, x_81);
if (x_82 == 0)
{
lean_dec(x_81);
x_77 = x_2;
x_78 = x_12;
goto block_79;
}
else
{
if (x_82 == 0)
{
lean_dec(x_81);
x_77 = x_2;
x_78 = x_12;
goto block_79;
}
else
{
size_t x_83; size_t x_84; lean_object* x_85; 
x_83 = 0;
x_84 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_85 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_31, x_83, x_84, x_11, x_12);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = lean_unbox(x_86);
lean_dec(x_86);
x_77 = x_88;
x_78 = x_87;
goto block_79;
}
else
{
uint8_t x_89; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 0);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_85);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
block_49:
{
lean_object* x_34; 
lean_inc_ref(x_10);
lean_inc_ref(x_7);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc(x_1);
x_34 = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_30, x_31, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_32);
x_37 = l_Lean_Compiler_LCNF_Simp_simp(x_32, x_5, x_6, x_35, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
lean_inc_ref(x_16);
x_40 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_38);
x_17 = x_40;
x_18 = x_39;
goto block_29;
}
else
{
uint8_t x_41; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
block_73:
{
if (x_51 == 0)
{
x_33 = x_50;
goto block_49;
}
else
{
lean_object* x_52; 
lean_inc_ref(x_32);
x_52 = l_Lean_Compiler_LCNF_Code_inferType(x_32, x_8, x_9, x_10, x_11, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_32, x_9, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_6, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_59, 0, x_53);
lean_inc_ref(x_16);
x_60 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_59);
x_17 = x_60;
x_18 = x_58;
goto block_29;
}
else
{
uint8_t x_61; 
lean_dec(x_53);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_53);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
block_76:
{
if (x_2 == 0)
{
x_33 = x_75;
goto block_49;
}
else
{
x_50 = x_75;
x_51 = x_74;
goto block_73;
}
}
block_79:
{
if (lean_obj_tag(x_32) == 6)
{
x_74 = x_77;
x_75 = x_78;
goto block_76;
}
else
{
if (x_2 == 0)
{
x_50 = x_78;
x_51 = x_77;
goto block_73;
}
else
{
x_74 = x_77;
x_75 = x_78;
goto block_76;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_16, 0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_93);
x_94 = l_Lean_Compiler_LCNF_Simp_simp(x_93, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
lean_inc_ref(x_16);
x_97 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_95);
x_17 = x_97;
x_18 = x_96;
goto block_29;
}
else
{
uint8_t x_98; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_94);
if (x_98 == 0)
{
return x_94;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_94, 0);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_94);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
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
x_25 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(x_1, x_2, x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(x_1, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_8, x_5, x_6);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1, x_2, x_3, x_4, x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_8, x_4, x_5);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
return x_19;
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
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_2, x_3, x_5, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(316u);
x_4 = l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__1;
x_5 = l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_14 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_24; uint8_t x_25; lean_object* x_30; lean_object* x_51; lean_object* x_52; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_51 = lean_ctor_get(x_4, 0);
x_52 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_51, x_7, x_16);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec_ref(x_52);
x_56 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(x_4, x_7, x_10, x_55);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_15);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_15);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_15);
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
if (x_3 == 0)
{
lean_object* x_65; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
lean_dec_ref(x_52);
x_30 = x_65;
goto block_50;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
lean_dec_ref(x_52);
lean_inc_ref(x_4);
x_67 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_66);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_30 = x_68;
goto block_50;
}
else
{
uint8_t x_69; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_67, 0);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_67);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_73 = !lean_is_exclusive(x_52);
if (x_73 == 0)
{
return x_52;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_52, 0);
x_75 = lean_ctor_get(x_52, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_52);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_15);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_15);
lean_dec_ref(x_4);
if (lean_is_scalar(x_17)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_17;
}
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
block_29:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_2);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_15);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_15);
lean_dec_ref(x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
block_50:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ptr_addr(x_32);
x_34 = lean_ptr_addr(x_15);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
x_18 = x_30;
x_19 = x_35;
goto block_23;
}
else
{
size_t x_36; size_t x_37; uint8_t x_38; 
x_36 = lean_ptr_addr(x_31);
x_37 = lean_ptr_addr(x_4);
x_38 = lean_usize_dec_eq(x_36, x_37);
x_18 = x_30;
x_19 = x_38;
goto block_23;
}
}
case 2:
{
lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; uint8_t x_43; 
lean_dec(x_17);
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ptr_addr(x_40);
x_42 = lean_ptr_addr(x_15);
x_43 = lean_usize_dec_eq(x_41, x_42);
if (x_43 == 0)
{
x_24 = x_30;
x_25 = x_43;
goto block_29;
}
else
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = lean_ptr_addr(x_39);
x_45 = lean_ptr_addr(x_4);
x_46 = lean_usize_dec_eq(x_44, x_45);
x_24 = x_30;
x_25 = x_46;
goto block_29;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_47 = l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3;
x_48 = l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_30);
return x_49;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get(x_7, 1);
x_40 = lean_ctor_get(x_7, 2);
x_41 = lean_ctor_get(x_7, 3);
x_42 = lean_ctor_get(x_7, 4);
x_43 = lean_ctor_get(x_7, 5);
x_44 = lean_ctor_get(x_7, 6);
x_45 = lean_ctor_get(x_7, 7);
x_46 = lean_ctor_get(x_7, 8);
x_47 = lean_ctor_get(x_7, 9);
x_48 = lean_ctor_get(x_7, 10);
x_49 = lean_ctor_get(x_7, 11);
x_50 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_51 = lean_ctor_get(x_7, 12);
x_52 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_53 = lean_ctor_get(x_7, 13);
x_54 = lean_nat_dec_eq(x_41, x_42);
if (x_54 == 0)
{
uint8_t x_55; 
lean_inc_ref(x_53);
lean_inc(x_51);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc_ref(x_38);
x_55 = !lean_is_exclusive(x_7);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_56 = lean_ctor_get(x_7, 13);
lean_dec(x_56);
x_57 = lean_ctor_get(x_7, 12);
lean_dec(x_57);
x_58 = lean_ctor_get(x_7, 11);
lean_dec(x_58);
x_59 = lean_ctor_get(x_7, 10);
lean_dec(x_59);
x_60 = lean_ctor_get(x_7, 9);
lean_dec(x_60);
x_61 = lean_ctor_get(x_7, 8);
lean_dec(x_61);
x_62 = lean_ctor_get(x_7, 7);
lean_dec(x_62);
x_63 = lean_ctor_get(x_7, 6);
lean_dec(x_63);
x_64 = lean_ctor_get(x_7, 5);
lean_dec(x_64);
x_65 = lean_ctor_get(x_7, 4);
lean_dec(x_65);
x_66 = lean_ctor_get(x_7, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_7, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_7, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_7, 0);
lean_dec(x_69);
x_70 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_136; lean_object* x_137; 
x_72 = lean_ctor_get(x_70, 1);
x_73 = lean_ctor_get(x_70, 0);
lean_dec(x_73);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_add(x_41, x_136);
lean_dec(x_41);
lean_ctor_set(x_7, 3, x_137);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_338; 
lean_free_object(x_70);
x_138 = lean_ctor_get(x_1, 0);
x_139 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_138);
x_338 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_54, x_138, x_3, x_6, x_72);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_383; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec_ref(x_338);
x_383 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_138, x_339);
if (x_383 == 0)
{
goto block_382;
}
else
{
if (x_54 == 0)
{
x_341 = x_2;
x_342 = x_3;
x_343 = x_4;
x_344 = x_5;
x_345 = x_6;
x_346 = x_7;
x_347 = x_8;
x_348 = x_340;
goto block_375;
}
else
{
goto block_382;
}
}
block_375:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_339, 2);
x_350 = lean_ctor_get(x_339, 3);
lean_inc(x_347);
lean_inc_ref(x_346);
lean_inc(x_345);
lean_inc_ref(x_344);
lean_inc_ref(x_343);
lean_inc(x_350);
x_351 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_350, x_341, x_343, x_344, x_345, x_346, x_347, x_348);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; 
lean_inc(x_350);
lean_inc_ref(x_349);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec_ref(x_351);
x_323 = x_339;
x_324 = x_349;
x_325 = x_350;
x_326 = x_341;
x_327 = x_342;
x_328 = x_343;
x_329 = x_344;
x_330 = x_345;
x_331 = x_346;
x_332 = x_347;
x_333 = x_353;
goto block_337;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_351, 1);
lean_inc(x_354);
lean_dec_ref(x_351);
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
lean_dec_ref(x_352);
x_356 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_342, x_354);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
lean_dec_ref(x_356);
x_358 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_339, x_355, x_345, x_357);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec_ref(x_358);
x_361 = lean_ctor_get(x_359, 2);
lean_inc_ref(x_361);
x_362 = lean_ctor_get(x_359, 3);
lean_inc(x_362);
x_323 = x_359;
x_324 = x_361;
x_325 = x_362;
x_326 = x_341;
x_327 = x_342;
x_328 = x_343;
x_329 = x_344;
x_330 = x_345;
x_331 = x_346;
x_332 = x_347;
x_333 = x_360;
goto block_337;
}
else
{
uint8_t x_363; 
lean_dec(x_347);
lean_dec_ref(x_346);
lean_dec(x_345);
lean_dec_ref(x_344);
lean_dec_ref(x_343);
lean_dec(x_342);
lean_dec_ref(x_341);
lean_dec_ref(x_1);
x_363 = !lean_is_exclusive(x_358);
if (x_363 == 0)
{
return x_358;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_358, 0);
x_365 = lean_ctor_get(x_358, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_358);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
}
}
else
{
uint8_t x_367; 
lean_dec(x_355);
lean_dec(x_347);
lean_dec_ref(x_346);
lean_dec(x_345);
lean_dec_ref(x_344);
lean_dec_ref(x_343);
lean_dec(x_342);
lean_dec_ref(x_341);
lean_dec(x_339);
lean_dec_ref(x_1);
x_367 = !lean_is_exclusive(x_356);
if (x_367 == 0)
{
return x_356;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_356, 0);
x_369 = lean_ctor_get(x_356, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_356);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
}
else
{
uint8_t x_371; 
lean_dec(x_347);
lean_dec_ref(x_346);
lean_dec(x_345);
lean_dec_ref(x_344);
lean_dec_ref(x_343);
lean_dec(x_342);
lean_dec_ref(x_341);
lean_dec(x_339);
lean_dec_ref(x_1);
x_371 = !lean_is_exclusive(x_351);
if (x_371 == 0)
{
return x_351;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_351, 0);
x_373 = lean_ctor_get(x_351, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_351);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
block_382:
{
lean_object* x_376; 
x_376 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_340);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
lean_dec_ref(x_376);
x_341 = x_2;
x_342 = x_3;
x_343 = x_4;
x_344 = x_5;
x_345 = x_6;
x_346 = x_7;
x_347 = x_8;
x_348 = x_377;
goto block_375;
}
else
{
uint8_t x_378; 
lean_dec(x_339);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_378 = !lean_is_exclusive(x_376);
if (x_378 == 0)
{
return x_376;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_376, 0);
x_380 = lean_ctor_get(x_376, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_376);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
}
else
{
uint8_t x_384; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_384 = !lean_is_exclusive(x_338);
if (x_384 == 0)
{
return x_338;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_338, 0);
x_386 = lean_ctor_get(x_338, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_338);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
block_322:
{
if (x_149 == 0)
{
lean_object* x_150; 
lean_inc(x_140);
lean_inc_ref(x_148);
lean_inc(x_142);
lean_inc_ref(x_144);
lean_inc_ref(x_141);
x_150 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_141, x_144, x_142, x_148, x_140, x_143);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec_ref(x_150);
lean_inc(x_140);
lean_inc_ref(x_148);
lean_inc(x_142);
lean_inc_ref(x_144);
lean_inc_ref(x_141);
x_153 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_141, x_147, x_146, x_144, x_142, x_148, x_140, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = lean_ctor_get(x_141, 0);
x_157 = lean_ctor_get(x_141, 3);
lean_inc(x_157);
x_158 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_157, x_155);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec_ref(x_158);
lean_inc(x_140);
lean_inc_ref(x_148);
lean_inc(x_142);
lean_inc_ref(x_144);
lean_inc_ref(x_145);
lean_inc(x_146);
lean_inc_ref(x_147);
lean_inc_ref(x_139);
lean_inc_ref(x_141);
x_161 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_141, x_139, x_147, x_146, x_145, x_144, x_142, x_148, x_140, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec_ref(x_161);
lean_inc(x_140);
lean_inc_ref(x_148);
lean_inc(x_142);
lean_inc_ref(x_144);
lean_inc_ref(x_145);
lean_inc(x_146);
lean_inc_ref(x_147);
lean_inc(x_157);
x_164 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_157, x_147, x_146, x_145, x_144, x_142, x_148, x_140, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec_ref(x_164);
lean_inc(x_140);
lean_inc_ref(x_148);
lean_inc(x_142);
lean_inc_ref(x_144);
lean_inc_ref(x_145);
lean_inc(x_146);
lean_inc_ref(x_147);
lean_inc_ref(x_139);
x_167 = l_Lean_Compiler_LCNF_Simp_simp(x_139, x_147, x_146, x_145, x_144, x_142, x_148, x_140, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec_ref(x_167);
x_170 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_156, x_146, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_140);
lean_dec_ref(x_1);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec_ref(x_170);
x_174 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_141, x_146, x_142, x_173);
lean_dec(x_142);
lean_dec(x_146);
lean_dec_ref(x_141);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_174, 0);
lean_dec(x_176);
lean_ctor_set(x_174, 0, x_168);
return x_174;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec(x_174);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_168);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
else
{
uint8_t x_179; 
lean_dec(x_168);
x_179 = !lean_is_exclusive(x_174);
if (x_179 == 0)
{
return x_174;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_174, 0);
x_181 = lean_ctor_get(x_174, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_174);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_170, 1);
lean_inc(x_183);
lean_dec_ref(x_170);
lean_inc_ref(x_141);
x_184 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_141, x_147, x_146, x_145, x_144, x_142, x_148, x_140, x_183);
lean_dec(x_140);
lean_dec_ref(x_148);
lean_dec(x_142);
lean_dec_ref(x_144);
lean_dec_ref(x_145);
lean_dec(x_146);
lean_dec_ref(x_147);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; size_t x_186; size_t x_187; uint8_t x_188; 
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = lean_ptr_addr(x_139);
x_187 = lean_ptr_addr(x_168);
x_188 = lean_usize_dec_eq(x_186, x_187);
if (x_188 == 0)
{
x_10 = x_141;
x_11 = x_185;
x_12 = x_168;
x_13 = x_188;
goto block_17;
}
else
{
size_t x_189; size_t x_190; uint8_t x_191; 
x_189 = lean_ptr_addr(x_138);
x_190 = lean_ptr_addr(x_141);
x_191 = lean_usize_dec_eq(x_189, x_190);
x_10 = x_141;
x_11 = x_185;
x_12 = x_168;
x_13 = x_191;
goto block_17;
}
}
else
{
uint8_t x_192; 
lean_dec(x_168);
lean_dec_ref(x_141);
lean_dec_ref(x_1);
x_192 = !lean_is_exclusive(x_184);
if (x_192 == 0)
{
return x_184;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_184, 0);
x_194 = lean_ctor_get(x_184, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_184);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_168);
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_1);
x_196 = !lean_is_exclusive(x_170);
if (x_196 == 0)
{
return x_170;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_170, 0);
x_198 = lean_ctor_get(x_170, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_170);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_1);
return x_167;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_inc_ref(x_139);
lean_dec_ref(x_1);
x_200 = lean_ctor_get(x_165, 0);
lean_inc(x_200);
lean_dec_ref(x_165);
x_201 = lean_ctor_get(x_164, 1);
lean_inc(x_201);
lean_dec_ref(x_164);
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
lean_inc(x_156);
x_204 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_156, x_203, x_146, x_142, x_148, x_140, x_201);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_141, x_146, x_142, x_205);
lean_dec_ref(x_141);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec_ref(x_206);
lean_inc(x_140);
lean_inc_ref(x_148);
lean_inc(x_142);
lean_inc_ref(x_144);
lean_inc_ref(x_145);
lean_inc(x_146);
lean_inc_ref(x_147);
x_208 = l_Lean_Compiler_LCNF_Simp_simp(x_139, x_147, x_146, x_145, x_144, x_142, x_148, x_140, x_207);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec_ref(x_208);
x_211 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_202, x_209, x_147, x_146, x_145, x_144, x_142, x_148, x_140, x_210);
lean_dec(x_140);
lean_dec_ref(x_148);
lean_dec(x_142);
lean_dec_ref(x_144);
lean_dec_ref(x_145);
lean_dec(x_146);
lean_dec_ref(x_147);
lean_dec(x_202);
return x_211;
}
else
{
lean_dec(x_202);
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec(x_140);
return x_208;
}
}
else
{
uint8_t x_212; 
lean_dec(x_202);
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec(x_140);
lean_dec_ref(x_139);
x_212 = !lean_is_exclusive(x_206);
if (x_212 == 0)
{
return x_206;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_206, 0);
x_214 = lean_ctor_get(x_206, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_206);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_202);
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_139);
x_216 = !lean_is_exclusive(x_204);
if (x_216 == 0)
{
return x_204;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_204, 0);
x_218 = lean_ctor_get(x_204, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_204);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
}
else
{
uint8_t x_220; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_1);
x_220 = !lean_is_exclusive(x_164);
if (x_220 == 0)
{
return x_164;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_164, 0);
x_222 = lean_ctor_get(x_164, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_164);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_140);
lean_dec_ref(x_1);
x_224 = lean_ctor_get(x_161, 1);
lean_inc(x_224);
lean_dec_ref(x_161);
x_225 = lean_ctor_get(x_162, 0);
lean_inc(x_225);
lean_dec_ref(x_162);
x_226 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_141, x_146, x_142, x_224);
lean_dec(x_142);
lean_dec(x_146);
lean_dec_ref(x_141);
if (lean_obj_tag(x_226) == 0)
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_226, 0);
lean_dec(x_228);
lean_ctor_set(x_226, 0, x_225);
return x_226;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
lean_dec(x_226);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_225);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
else
{
uint8_t x_231; 
lean_dec(x_225);
x_231 = !lean_is_exclusive(x_226);
if (x_231 == 0)
{
return x_226;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_226, 0);
x_233 = lean_ctor_get(x_226, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_226);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
else
{
uint8_t x_235; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_1);
x_235 = !lean_is_exclusive(x_161);
if (x_235 == 0)
{
return x_161;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_161, 0);
x_237 = lean_ctor_get(x_161, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_161);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_inc_ref(x_139);
lean_dec_ref(x_1);
x_239 = lean_ctor_get(x_158, 1);
lean_inc(x_239);
lean_dec_ref(x_158);
x_240 = lean_ctor_get(x_159, 0);
lean_inc(x_240);
lean_dec_ref(x_159);
lean_inc(x_156);
x_241 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_156, x_240, x_146, x_142, x_148, x_140, x_239);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec_ref(x_241);
x_243 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_141, x_146, x_142, x_242);
lean_dec_ref(x_141);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec_ref(x_243);
x_1 = x_139;
x_2 = x_147;
x_3 = x_146;
x_4 = x_145;
x_5 = x_144;
x_6 = x_142;
x_7 = x_148;
x_8 = x_140;
x_9 = x_244;
goto _start;
}
else
{
uint8_t x_246; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec(x_140);
lean_dec_ref(x_139);
x_246 = !lean_is_exclusive(x_243);
if (x_246 == 0)
{
return x_243;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_243, 0);
x_248 = lean_ctor_get(x_243, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_243);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_139);
x_250 = !lean_is_exclusive(x_241);
if (x_250 == 0)
{
return x_241;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_241, 0);
x_252 = lean_ctor_get(x_241, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_241);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
}
else
{
uint8_t x_254; 
lean_dec_ref(x_141);
lean_inc_ref(x_139);
x_254 = !lean_is_exclusive(x_1);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_1, 1);
lean_dec(x_255);
x_256 = lean_ctor_get(x_1, 0);
lean_dec(x_256);
x_257 = lean_ctor_get(x_153, 1);
lean_inc(x_257);
lean_dec_ref(x_153);
x_258 = lean_ctor_get(x_154, 0);
lean_inc(x_258);
lean_dec_ref(x_154);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_258);
x_2 = x_147;
x_3 = x_146;
x_4 = x_145;
x_5 = x_144;
x_6 = x_142;
x_7 = x_148;
x_8 = x_140;
x_9 = x_257;
goto _start;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_1);
x_260 = lean_ctor_get(x_153, 1);
lean_inc(x_260);
lean_dec_ref(x_153);
x_261 = lean_ctor_get(x_154, 0);
lean_inc(x_261);
lean_dec_ref(x_154);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_139);
x_1 = x_262;
x_2 = x_147;
x_3 = x_146;
x_4 = x_145;
x_5 = x_144;
x_6 = x_142;
x_7 = x_148;
x_8 = x_140;
x_9 = x_260;
goto _start;
}
}
}
else
{
uint8_t x_264; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_1);
x_264 = !lean_is_exclusive(x_153);
if (x_264 == 0)
{
return x_153;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_153, 0);
x_266 = lean_ctor_get(x_153, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_153);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec_ref(x_141);
lean_inc_ref(x_139);
lean_dec_ref(x_1);
x_268 = lean_ctor_get(x_150, 1);
lean_inc(x_268);
lean_dec_ref(x_150);
x_269 = lean_ctor_get(x_151, 0);
lean_inc(x_269);
lean_dec_ref(x_151);
x_270 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_146, x_268);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec_ref(x_270);
lean_inc(x_140);
lean_inc_ref(x_148);
lean_inc(x_142);
lean_inc_ref(x_144);
lean_inc_ref(x_145);
lean_inc(x_146);
lean_inc_ref(x_147);
x_272 = l_Lean_Compiler_LCNF_Simp_simp(x_139, x_147, x_146, x_145, x_144, x_142, x_148, x_140, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec_ref(x_272);
x_275 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_269, x_273, x_147, x_146, x_145, x_144, x_142, x_148, x_140, x_274);
lean_dec(x_140);
lean_dec_ref(x_148);
lean_dec(x_142);
lean_dec_ref(x_144);
lean_dec_ref(x_145);
lean_dec(x_146);
lean_dec_ref(x_147);
lean_dec(x_269);
return x_275;
}
else
{
lean_dec(x_269);
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec(x_140);
return x_272;
}
}
else
{
uint8_t x_276; 
lean_dec(x_269);
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec(x_140);
lean_dec_ref(x_139);
x_276 = !lean_is_exclusive(x_270);
if (x_276 == 0)
{
return x_270;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_270, 0);
x_278 = lean_ctor_get(x_270, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_270);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
}
else
{
uint8_t x_280; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_1);
x_280 = !lean_is_exclusive(x_150);
if (x_280 == 0)
{
return x_150;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_150, 0);
x_282 = lean_ctor_get(x_150, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_150);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
lean_inc_ref(x_139);
lean_dec_ref(x_1);
x_284 = lean_st_ref_take(x_146, x_143);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec_ref(x_284);
x_287 = !lean_is_exclusive(x_285);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_288 = lean_ctor_get(x_141, 0);
x_289 = lean_ctor_get(x_285, 0);
x_290 = lean_box(0);
lean_inc(x_288);
x_291 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_289, x_288, x_290);
lean_ctor_set(x_285, 0, x_291);
x_292 = lean_st_ref_set(x_146, x_285, x_286);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec_ref(x_292);
x_294 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_141, x_146, x_142, x_293);
lean_dec_ref(x_141);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec_ref(x_294);
x_1 = x_139;
x_2 = x_147;
x_3 = x_146;
x_4 = x_145;
x_5 = x_144;
x_6 = x_142;
x_7 = x_148;
x_8 = x_140;
x_9 = x_295;
goto _start;
}
else
{
uint8_t x_297; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec(x_140);
lean_dec_ref(x_139);
x_297 = !lean_is_exclusive(x_294);
if (x_297 == 0)
{
return x_294;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_294, 0);
x_299 = lean_ctor_get(x_294, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_294);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_301 = lean_ctor_get(x_141, 0);
x_302 = lean_ctor_get(x_285, 0);
x_303 = lean_ctor_get(x_285, 1);
x_304 = lean_ctor_get(x_285, 2);
x_305 = lean_ctor_get(x_285, 3);
x_306 = lean_ctor_get_uint8(x_285, sizeof(void*)*7);
x_307 = lean_ctor_get(x_285, 4);
x_308 = lean_ctor_get(x_285, 5);
x_309 = lean_ctor_get(x_285, 6);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_285);
x_310 = lean_box(0);
lean_inc(x_301);
x_311 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_302, x_301, x_310);
x_312 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_303);
lean_ctor_set(x_312, 2, x_304);
lean_ctor_set(x_312, 3, x_305);
lean_ctor_set(x_312, 4, x_307);
lean_ctor_set(x_312, 5, x_308);
lean_ctor_set(x_312, 6, x_309);
lean_ctor_set_uint8(x_312, sizeof(void*)*7, x_306);
x_313 = lean_st_ref_set(x_146, x_312, x_286);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec_ref(x_313);
x_315 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_141, x_146, x_142, x_314);
lean_dec_ref(x_141);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec_ref(x_315);
x_1 = x_139;
x_2 = x_147;
x_3 = x_146;
x_4 = x_145;
x_5 = x_144;
x_6 = x_142;
x_7 = x_148;
x_8 = x_140;
x_9 = x_316;
goto _start;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec(x_140);
lean_dec_ref(x_139);
x_318 = lean_ctor_get(x_315, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_315, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_320 = x_315;
} else {
 lean_dec_ref(x_315);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
}
}
block_337:
{
uint8_t x_334; 
x_334 = l_Lean_Expr_isErased(x_324);
lean_dec_ref(x_324);
if (x_334 == 0)
{
lean_dec(x_325);
x_140 = x_332;
x_141 = x_323;
x_142 = x_330;
x_143 = x_333;
x_144 = x_329;
x_145 = x_328;
x_146 = x_327;
x_147 = x_326;
x_148 = x_331;
x_149 = x_54;
goto block_322;
}
else
{
lean_object* x_335; uint8_t x_336; 
x_335 = lean_box(1);
x_336 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_325, x_335);
lean_dec(x_325);
if (x_336 == 0)
{
x_140 = x_332;
x_141 = x_323;
x_142 = x_330;
x_143 = x_333;
x_144 = x_329;
x_145 = x_328;
x_146 = x_327;
x_147 = x_326;
x_148 = x_331;
x_149 = x_334;
goto block_322;
}
else
{
x_140 = x_332;
x_141 = x_323;
x_142 = x_330;
x_143 = x_333;
x_144 = x_329;
x_145 = x_328;
x_146 = x_327;
x_147 = x_326;
x_148 = x_331;
x_149 = x_54;
goto block_322;
}
}
}
}
case 3:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_free_object(x_70);
x_388 = lean_ctor_get(x_1, 0);
x_389 = lean_ctor_get(x_1, 1);
x_390 = lean_st_ref_get(x_3, x_72);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec_ref(x_390);
x_393 = lean_ctor_get(x_391, 0);
lean_inc_ref(x_393);
lean_dec(x_391);
lean_inc(x_388);
x_394 = l_Lean_Compiler_LCNF_normFVarImp(x_393, x_388, x_54);
lean_dec_ref(x_393);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_410; lean_object* x_416; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
lean_dec_ref(x_394);
lean_inc_ref(x_389);
x_396 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_54, x_389, x_3, x_392);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_399 = x_396;
} else {
 lean_dec_ref(x_396);
 x_399 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_397);
x_416 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_395, x_397, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_398);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec_ref(x_416);
lean_inc(x_395);
x_419 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_395, x_3, x_418);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec_ref(x_419);
x_421 = lean_unsigned_to_nat(0u);
x_422 = lean_array_get_size(x_397);
x_423 = lean_nat_dec_lt(x_421, x_422);
if (x_423 == 0)
{
lean_dec(x_422);
lean_dec(x_3);
x_410 = x_420;
goto block_415;
}
else
{
uint8_t x_424; 
x_424 = lean_nat_dec_le(x_422, x_422);
if (x_424 == 0)
{
lean_dec(x_422);
lean_dec(x_3);
x_410 = x_420;
goto block_415;
}
else
{
lean_object* x_425; size_t x_426; size_t x_427; lean_object* x_428; 
x_425 = lean_box(0);
x_426 = 0;
x_427 = lean_usize_of_nat(x_422);
lean_dec(x_422);
x_428 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_397, x_426, x_427, x_425, x_3, x_420);
lean_dec(x_3);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; 
x_429 = lean_ctor_get(x_428, 1);
lean_inc(x_429);
lean_dec_ref(x_428);
x_410 = x_429;
goto block_415;
}
else
{
uint8_t x_430; 
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_395);
lean_dec_ref(x_1);
x_430 = !lean_is_exclusive(x_428);
if (x_430 == 0)
{
return x_428;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_428, 0);
x_432 = lean_ctor_get(x_428, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_428);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
}
}
else
{
uint8_t x_434; 
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_3);
lean_dec_ref(x_1);
x_434 = !lean_is_exclusive(x_419);
if (x_434 == 0)
{
return x_419;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_419, 0);
x_436 = lean_ctor_get(x_419, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_419);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
else
{
lean_object* x_438; lean_object* x_439; 
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_395);
lean_dec_ref(x_1);
x_438 = lean_ctor_get(x_416, 1);
lean_inc(x_438);
lean_dec_ref(x_416);
x_439 = lean_ctor_get(x_417, 0);
lean_inc(x_439);
lean_dec_ref(x_417);
x_1 = x_439;
x_9 = x_438;
goto _start;
}
}
else
{
uint8_t x_441; 
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_395);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_441 = !lean_is_exclusive(x_416);
if (x_441 == 0)
{
return x_416;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_442 = lean_ctor_get(x_416, 0);
x_443 = lean_ctor_get(x_416, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_416);
x_444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
return x_444;
}
}
block_409:
{
if (x_401 == 0)
{
uint8_t x_402; 
x_402 = !lean_is_exclusive(x_1);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_1, 1);
lean_dec(x_403);
x_404 = lean_ctor_get(x_1, 0);
lean_dec(x_404);
lean_ctor_set(x_1, 1, x_397);
lean_ctor_set(x_1, 0, x_395);
if (lean_is_scalar(x_399)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_399;
}
lean_ctor_set(x_405, 0, x_1);
lean_ctor_set(x_405, 1, x_400);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; 
lean_dec(x_1);
x_406 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_406, 0, x_395);
lean_ctor_set(x_406, 1, x_397);
if (lean_is_scalar(x_399)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_399;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_400);
return x_407;
}
}
else
{
lean_object* x_408; 
lean_dec(x_397);
lean_dec(x_395);
if (lean_is_scalar(x_399)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_399;
}
lean_ctor_set(x_408, 0, x_1);
lean_ctor_set(x_408, 1, x_400);
return x_408;
}
}
block_415:
{
uint8_t x_411; 
x_411 = l_Lean_instBEqFVarId_beq(x_388, x_395);
if (x_411 == 0)
{
x_400 = x_410;
x_401 = x_411;
goto block_409;
}
else
{
size_t x_412; size_t x_413; uint8_t x_414; 
x_412 = lean_ptr_addr(x_389);
x_413 = lean_ptr_addr(x_397);
x_414 = lean_usize_dec_eq(x_412, x_413);
x_400 = x_410;
x_401 = x_414;
goto block_409;
}
}
}
else
{
lean_object* x_445; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_445 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_392);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_445;
}
}
case 4:
{
lean_object* x_446; lean_object* x_447; 
lean_free_object(x_70);
x_446 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_446);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_446);
x_447 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_446, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
if (lean_obj_tag(x_448) == 0)
{
uint8_t x_449; 
x_449 = !lean_is_exclusive(x_447);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_450 = lean_ctor_get(x_447, 1);
x_451 = lean_ctor_get(x_447, 0);
lean_dec(x_451);
x_452 = lean_st_ref_get(x_3, x_450);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec_ref(x_452);
x_455 = lean_ctor_get(x_446, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_446, 1);
lean_inc_ref(x_456);
x_457 = lean_ctor_get(x_446, 2);
lean_inc(x_457);
x_458 = lean_ctor_get(x_446, 3);
lean_inc_ref(x_458);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 lean_ctor_release(x_446, 2);
 lean_ctor_release(x_446, 3);
 x_459 = x_446;
} else {
 lean_dec_ref(x_446);
 x_459 = lean_box(0);
}
x_460 = lean_ctor_get(x_453, 0);
lean_inc_ref(x_460);
lean_dec(x_453);
lean_inc(x_457);
x_461 = l_Lean_Compiler_LCNF_normFVarImp(x_460, x_457, x_54);
lean_dec_ref(x_460);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 x_463 = x_461;
} else {
 lean_dec_ref(x_461);
 x_463 = lean_box(0);
}
x_464 = lean_st_ref_get(x_3, x_454);
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_464, 1);
lean_inc(x_466);
lean_dec_ref(x_464);
x_467 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_458);
lean_inc(x_462);
x_468 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_462, x_54, x_467, x_458, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_466);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_471 = x_468;
} else {
 lean_dec_ref(x_468);
 x_471 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_472 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_469, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_470);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_483; uint8_t x_484; lean_object* x_488; lean_object* x_489; lean_object* x_503; uint8_t x_504; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_475 = x_472;
} else {
 lean_dec_ref(x_472);
 x_475 = lean_box(0);
}
x_476 = lean_ctor_get(x_465, 0);
lean_inc_ref(x_476);
lean_dec(x_465);
lean_inc_ref(x_456);
x_477 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_476, x_54, x_456);
lean_dec_ref(x_476);
x_503 = lean_array_get_size(x_473);
x_504 = lean_nat_dec_eq(x_503, x_136);
lean_dec(x_503);
if (x_504 == 0)
{
lean_free_object(x_447);
lean_dec(x_6);
x_488 = x_3;
x_489 = x_474;
goto block_502;
}
else
{
lean_object* x_505; 
x_505 = lean_array_fget_borrowed(x_473, x_467);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_519; lean_object* x_520; uint8_t x_533; lean_object* x_534; uint8_t x_536; 
lean_free_object(x_447);
x_506 = lean_ctor_get(x_505, 1);
x_507 = lean_ctor_get(x_505, 2);
x_519 = lean_array_get_size(x_506);
x_536 = lean_nat_dec_lt(x_467, x_519);
if (x_536 == 0)
{
x_533 = x_54;
x_534 = x_474;
goto block_535;
}
else
{
if (x_536 == 0)
{
x_533 = x_54;
x_534 = x_474;
goto block_535;
}
else
{
size_t x_537; size_t x_538; lean_object* x_539; 
x_537 = 0;
x_538 = lean_usize_of_nat(x_519);
x_539 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_506, x_537, x_538, x_3, x_474);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; uint8_t x_542; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec_ref(x_539);
x_542 = lean_unbox(x_540);
lean_dec(x_540);
x_533 = x_542;
x_534 = x_541;
goto block_535;
}
else
{
uint8_t x_543; 
lean_dec(x_519);
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_471);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_458);
lean_dec(x_457);
lean_dec_ref(x_456);
lean_dec(x_455);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_543 = !lean_is_exclusive(x_539);
if (x_543 == 0)
{
return x_539;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_544 = lean_ctor_get(x_539, 0);
x_545 = lean_ctor_get(x_539, 1);
lean_inc(x_545);
lean_inc(x_544);
lean_dec(x_539);
x_546 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_546, 0, x_544);
lean_ctor_set(x_546, 1, x_545);
return x_546;
}
}
}
}
block_518:
{
lean_object* x_509; 
x_509 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_508);
lean_dec(x_3);
if (lean_obj_tag(x_509) == 0)
{
uint8_t x_510; 
x_510 = !lean_is_exclusive(x_509);
if (x_510 == 0)
{
lean_object* x_511; 
x_511 = lean_ctor_get(x_509, 0);
lean_dec(x_511);
lean_ctor_set(x_509, 0, x_507);
return x_509;
}
else
{
lean_object* x_512; lean_object* x_513; 
x_512 = lean_ctor_get(x_509, 1);
lean_inc(x_512);
lean_dec(x_509);
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_507);
lean_ctor_set(x_513, 1, x_512);
return x_513;
}
}
else
{
uint8_t x_514; 
lean_dec_ref(x_507);
x_514 = !lean_is_exclusive(x_509);
if (x_514 == 0)
{
return x_509;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_509, 0);
x_516 = lean_ctor_get(x_509, 1);
lean_inc(x_516);
lean_inc(x_515);
lean_dec(x_509);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_515);
lean_ctor_set(x_517, 1, x_516);
return x_517;
}
}
}
block_532:
{
uint8_t x_521; 
x_521 = lean_nat_dec_lt(x_467, x_519);
if (x_521 == 0)
{
lean_dec(x_519);
lean_dec_ref(x_506);
lean_dec(x_6);
x_508 = x_520;
goto block_518;
}
else
{
uint8_t x_522; 
x_522 = lean_nat_dec_le(x_519, x_519);
if (x_522 == 0)
{
lean_dec(x_519);
lean_dec_ref(x_506);
lean_dec(x_6);
x_508 = x_520;
goto block_518;
}
else
{
lean_object* x_523; size_t x_524; size_t x_525; lean_object* x_526; 
x_523 = lean_box(0);
x_524 = 0;
x_525 = lean_usize_of_nat(x_519);
lean_dec(x_519);
x_526 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_506, x_524, x_525, x_523, x_6, x_520);
lean_dec(x_6);
lean_dec_ref(x_506);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; 
x_527 = lean_ctor_get(x_526, 1);
lean_inc(x_527);
lean_dec_ref(x_526);
x_508 = x_527;
goto block_518;
}
else
{
uint8_t x_528; 
lean_dec_ref(x_507);
lean_dec(x_3);
x_528 = !lean_is_exclusive(x_526);
if (x_528 == 0)
{
return x_526;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_526, 0);
x_530 = lean_ctor_get(x_526, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_526);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
return x_531;
}
}
}
}
}
block_535:
{
if (x_533 == 0)
{
lean_inc_ref(x_507);
lean_inc_ref(x_506);
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_471);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_458);
lean_dec(x_457);
lean_dec_ref(x_456);
lean_dec(x_455);
lean_dec_ref(x_1);
x_520 = x_534;
goto block_532;
}
else
{
if (x_54 == 0)
{
lean_dec(x_519);
lean_dec(x_6);
x_488 = x_3;
x_489 = x_534;
goto block_502;
}
else
{
lean_inc_ref(x_507);
lean_inc_ref(x_506);
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_471);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_458);
lean_dec(x_457);
lean_dec_ref(x_456);
lean_dec(x_455);
lean_dec_ref(x_1);
x_520 = x_534;
goto block_532;
}
}
}
}
else
{
lean_object* x_547; 
lean_inc_ref(x_505);
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_471);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_458);
lean_dec(x_457);
lean_dec_ref(x_456);
lean_dec(x_455);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_547 = lean_ctor_get(x_505, 0);
lean_inc_ref(x_547);
lean_dec_ref(x_505);
lean_ctor_set(x_447, 1, x_474);
lean_ctor_set(x_447, 0, x_547);
return x_447;
}
}
block_482:
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
if (lean_is_scalar(x_459)) {
 x_479 = lean_alloc_ctor(0, 4, 0);
} else {
 x_479 = x_459;
}
lean_ctor_set(x_479, 0, x_455);
lean_ctor_set(x_479, 1, x_477);
lean_ctor_set(x_479, 2, x_462);
lean_ctor_set(x_479, 3, x_473);
if (lean_is_scalar(x_463)) {
 x_480 = lean_alloc_ctor(4, 1, 0);
} else {
 x_480 = x_463;
 lean_ctor_set_tag(x_480, 4);
}
lean_ctor_set(x_480, 0, x_479);
if (lean_is_scalar(x_475)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_475;
}
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_478);
return x_481;
}
block_487:
{
if (x_484 == 0)
{
lean_dec(x_471);
lean_dec(x_457);
lean_dec_ref(x_1);
x_478 = x_483;
goto block_482;
}
else
{
uint8_t x_485; 
x_485 = l_Lean_instBEqFVarId_beq(x_457, x_462);
lean_dec(x_457);
if (x_485 == 0)
{
lean_dec(x_471);
lean_dec_ref(x_1);
x_478 = x_483;
goto block_482;
}
else
{
lean_object* x_486; 
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_459);
lean_dec(x_455);
if (lean_is_scalar(x_471)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_471;
}
lean_ctor_set(x_486, 0, x_1);
lean_ctor_set(x_486, 1, x_483);
return x_486;
}
}
}
block_502:
{
lean_object* x_490; 
lean_inc(x_462);
x_490 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_462, x_488, x_489);
lean_dec(x_488);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; size_t x_492; size_t x_493; uint8_t x_494; 
x_491 = lean_ctor_get(x_490, 1);
lean_inc(x_491);
lean_dec_ref(x_490);
x_492 = lean_ptr_addr(x_458);
lean_dec_ref(x_458);
x_493 = lean_ptr_addr(x_473);
x_494 = lean_usize_dec_eq(x_492, x_493);
if (x_494 == 0)
{
lean_dec_ref(x_456);
x_483 = x_491;
x_484 = x_494;
goto block_487;
}
else
{
size_t x_495; size_t x_496; uint8_t x_497; 
x_495 = lean_ptr_addr(x_456);
lean_dec_ref(x_456);
x_496 = lean_ptr_addr(x_477);
x_497 = lean_usize_dec_eq(x_495, x_496);
x_483 = x_491;
x_484 = x_497;
goto block_487;
}
}
else
{
uint8_t x_498; 
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_471);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_458);
lean_dec(x_457);
lean_dec_ref(x_456);
lean_dec(x_455);
lean_dec_ref(x_1);
x_498 = !lean_is_exclusive(x_490);
if (x_498 == 0)
{
return x_490;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_490, 0);
x_500 = lean_ctor_get(x_490, 1);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_490);
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
return x_501;
}
}
}
}
else
{
uint8_t x_548; 
lean_dec(x_471);
lean_dec(x_465);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_458);
lean_dec(x_457);
lean_dec_ref(x_456);
lean_dec(x_455);
lean_free_object(x_447);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_548 = !lean_is_exclusive(x_472);
if (x_548 == 0)
{
return x_472;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_472, 0);
x_550 = lean_ctor_get(x_472, 1);
lean_inc(x_550);
lean_inc(x_549);
lean_dec(x_472);
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
return x_551;
}
}
}
else
{
uint8_t x_552; 
lean_dec(x_465);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_459);
lean_dec_ref(x_458);
lean_dec(x_457);
lean_dec_ref(x_456);
lean_dec(x_455);
lean_free_object(x_447);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_552 = !lean_is_exclusive(x_468);
if (x_552 == 0)
{
return x_468;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_468, 0);
x_554 = lean_ctor_get(x_468, 1);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_468);
x_555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
return x_555;
}
}
}
else
{
lean_object* x_556; 
lean_dec(x_459);
lean_dec_ref(x_458);
lean_dec(x_457);
lean_dec_ref(x_456);
lean_dec(x_455);
lean_free_object(x_447);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_556 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_454);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_556;
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_557 = lean_ctor_get(x_447, 1);
lean_inc(x_557);
lean_dec(x_447);
x_558 = lean_st_ref_get(x_3, x_557);
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
lean_dec_ref(x_558);
x_561 = lean_ctor_get(x_446, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_446, 1);
lean_inc_ref(x_562);
x_563 = lean_ctor_get(x_446, 2);
lean_inc(x_563);
x_564 = lean_ctor_get(x_446, 3);
lean_inc_ref(x_564);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 lean_ctor_release(x_446, 2);
 lean_ctor_release(x_446, 3);
 x_565 = x_446;
} else {
 lean_dec_ref(x_446);
 x_565 = lean_box(0);
}
x_566 = lean_ctor_get(x_559, 0);
lean_inc_ref(x_566);
lean_dec(x_559);
lean_inc(x_563);
x_567 = l_Lean_Compiler_LCNF_normFVarImp(x_566, x_563, x_54);
lean_dec_ref(x_566);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 x_569 = x_567;
} else {
 lean_dec_ref(x_567);
 x_569 = lean_box(0);
}
x_570 = lean_st_ref_get(x_3, x_560);
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec_ref(x_570);
x_573 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_564);
lean_inc(x_568);
x_574 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_568, x_54, x_573, x_564, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_572);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_577 = x_574;
} else {
 lean_dec_ref(x_574);
 x_577 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_578 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_575, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_576);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_589; uint8_t x_590; lean_object* x_594; lean_object* x_595; lean_object* x_609; uint8_t x_610; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_578, 1);
lean_inc(x_580);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 x_581 = x_578;
} else {
 lean_dec_ref(x_578);
 x_581 = lean_box(0);
}
x_582 = lean_ctor_get(x_571, 0);
lean_inc_ref(x_582);
lean_dec(x_571);
lean_inc_ref(x_562);
x_583 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_582, x_54, x_562);
lean_dec_ref(x_582);
x_609 = lean_array_get_size(x_579);
x_610 = lean_nat_dec_eq(x_609, x_136);
lean_dec(x_609);
if (x_610 == 0)
{
lean_dec(x_6);
x_594 = x_3;
x_595 = x_580;
goto block_608;
}
else
{
lean_object* x_611; 
x_611 = lean_array_fget_borrowed(x_579, x_573);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_624; lean_object* x_625; uint8_t x_638; lean_object* x_639; uint8_t x_641; 
x_612 = lean_ctor_get(x_611, 1);
x_613 = lean_ctor_get(x_611, 2);
x_624 = lean_array_get_size(x_612);
x_641 = lean_nat_dec_lt(x_573, x_624);
if (x_641 == 0)
{
x_638 = x_54;
x_639 = x_580;
goto block_640;
}
else
{
if (x_641 == 0)
{
x_638 = x_54;
x_639 = x_580;
goto block_640;
}
else
{
size_t x_642; size_t x_643; lean_object* x_644; 
x_642 = 0;
x_643 = lean_usize_of_nat(x_624);
x_644 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_612, x_642, x_643, x_3, x_580);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; uint8_t x_647; 
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
lean_dec_ref(x_644);
x_647 = lean_unbox(x_645);
lean_dec(x_645);
x_638 = x_647;
x_639 = x_646;
goto block_640;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_624);
lean_dec_ref(x_583);
lean_dec(x_581);
lean_dec(x_579);
lean_dec(x_577);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_565);
lean_dec_ref(x_564);
lean_dec(x_563);
lean_dec_ref(x_562);
lean_dec(x_561);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_648 = lean_ctor_get(x_644, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_644, 1);
lean_inc(x_649);
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 lean_ctor_release(x_644, 1);
 x_650 = x_644;
} else {
 lean_dec_ref(x_644);
 x_650 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_651 = lean_alloc_ctor(1, 2, 0);
} else {
 x_651 = x_650;
}
lean_ctor_set(x_651, 0, x_648);
lean_ctor_set(x_651, 1, x_649);
return x_651;
}
}
}
block_623:
{
lean_object* x_615; 
x_615 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_614);
lean_dec(x_3);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_615, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_617 = x_615;
} else {
 lean_dec_ref(x_615);
 x_617 = lean_box(0);
}
if (lean_is_scalar(x_617)) {
 x_618 = lean_alloc_ctor(0, 2, 0);
} else {
 x_618 = x_617;
}
lean_ctor_set(x_618, 0, x_613);
lean_ctor_set(x_618, 1, x_616);
return x_618;
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_dec_ref(x_613);
x_619 = lean_ctor_get(x_615, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_615, 1);
lean_inc(x_620);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_621 = x_615;
} else {
 lean_dec_ref(x_615);
 x_621 = lean_box(0);
}
if (lean_is_scalar(x_621)) {
 x_622 = lean_alloc_ctor(1, 2, 0);
} else {
 x_622 = x_621;
}
lean_ctor_set(x_622, 0, x_619);
lean_ctor_set(x_622, 1, x_620);
return x_622;
}
}
block_637:
{
uint8_t x_626; 
x_626 = lean_nat_dec_lt(x_573, x_624);
if (x_626 == 0)
{
lean_dec(x_624);
lean_dec_ref(x_612);
lean_dec(x_6);
x_614 = x_625;
goto block_623;
}
else
{
uint8_t x_627; 
x_627 = lean_nat_dec_le(x_624, x_624);
if (x_627 == 0)
{
lean_dec(x_624);
lean_dec_ref(x_612);
lean_dec(x_6);
x_614 = x_625;
goto block_623;
}
else
{
lean_object* x_628; size_t x_629; size_t x_630; lean_object* x_631; 
x_628 = lean_box(0);
x_629 = 0;
x_630 = lean_usize_of_nat(x_624);
lean_dec(x_624);
x_631 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_612, x_629, x_630, x_628, x_6, x_625);
lean_dec(x_6);
lean_dec_ref(x_612);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; 
x_632 = lean_ctor_get(x_631, 1);
lean_inc(x_632);
lean_dec_ref(x_631);
x_614 = x_632;
goto block_623;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec_ref(x_613);
lean_dec(x_3);
x_633 = lean_ctor_get(x_631, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_631, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_635 = x_631;
} else {
 lean_dec_ref(x_631);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
return x_636;
}
}
}
}
block_640:
{
if (x_638 == 0)
{
lean_inc_ref(x_613);
lean_inc_ref(x_612);
lean_dec_ref(x_583);
lean_dec(x_581);
lean_dec(x_579);
lean_dec(x_577);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_565);
lean_dec_ref(x_564);
lean_dec(x_563);
lean_dec_ref(x_562);
lean_dec(x_561);
lean_dec_ref(x_1);
x_625 = x_639;
goto block_637;
}
else
{
if (x_54 == 0)
{
lean_dec(x_624);
lean_dec(x_6);
x_594 = x_3;
x_595 = x_639;
goto block_608;
}
else
{
lean_inc_ref(x_613);
lean_inc_ref(x_612);
lean_dec_ref(x_583);
lean_dec(x_581);
lean_dec(x_579);
lean_dec(x_577);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_565);
lean_dec_ref(x_564);
lean_dec(x_563);
lean_dec_ref(x_562);
lean_dec(x_561);
lean_dec_ref(x_1);
x_625 = x_639;
goto block_637;
}
}
}
}
else
{
lean_object* x_652; lean_object* x_653; 
lean_inc_ref(x_611);
lean_dec_ref(x_583);
lean_dec(x_581);
lean_dec(x_579);
lean_dec(x_577);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_565);
lean_dec_ref(x_564);
lean_dec(x_563);
lean_dec_ref(x_562);
lean_dec(x_561);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_652 = lean_ctor_get(x_611, 0);
lean_inc_ref(x_652);
lean_dec_ref(x_611);
x_653 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_580);
return x_653;
}
}
block_588:
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
if (lean_is_scalar(x_565)) {
 x_585 = lean_alloc_ctor(0, 4, 0);
} else {
 x_585 = x_565;
}
lean_ctor_set(x_585, 0, x_561);
lean_ctor_set(x_585, 1, x_583);
lean_ctor_set(x_585, 2, x_568);
lean_ctor_set(x_585, 3, x_579);
if (lean_is_scalar(x_569)) {
 x_586 = lean_alloc_ctor(4, 1, 0);
} else {
 x_586 = x_569;
 lean_ctor_set_tag(x_586, 4);
}
lean_ctor_set(x_586, 0, x_585);
if (lean_is_scalar(x_581)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_581;
}
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_584);
return x_587;
}
block_593:
{
if (x_590 == 0)
{
lean_dec(x_577);
lean_dec(x_563);
lean_dec_ref(x_1);
x_584 = x_589;
goto block_588;
}
else
{
uint8_t x_591; 
x_591 = l_Lean_instBEqFVarId_beq(x_563, x_568);
lean_dec(x_563);
if (x_591 == 0)
{
lean_dec(x_577);
lean_dec_ref(x_1);
x_584 = x_589;
goto block_588;
}
else
{
lean_object* x_592; 
lean_dec_ref(x_583);
lean_dec(x_581);
lean_dec(x_579);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_565);
lean_dec(x_561);
if (lean_is_scalar(x_577)) {
 x_592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_592 = x_577;
}
lean_ctor_set(x_592, 0, x_1);
lean_ctor_set(x_592, 1, x_589);
return x_592;
}
}
}
block_608:
{
lean_object* x_596; 
lean_inc(x_568);
x_596 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_568, x_594, x_595);
lean_dec(x_594);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; size_t x_598; size_t x_599; uint8_t x_600; 
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
lean_dec_ref(x_596);
x_598 = lean_ptr_addr(x_564);
lean_dec_ref(x_564);
x_599 = lean_ptr_addr(x_579);
x_600 = lean_usize_dec_eq(x_598, x_599);
if (x_600 == 0)
{
lean_dec_ref(x_562);
x_589 = x_597;
x_590 = x_600;
goto block_593;
}
else
{
size_t x_601; size_t x_602; uint8_t x_603; 
x_601 = lean_ptr_addr(x_562);
lean_dec_ref(x_562);
x_602 = lean_ptr_addr(x_583);
x_603 = lean_usize_dec_eq(x_601, x_602);
x_589 = x_597;
x_590 = x_603;
goto block_593;
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec_ref(x_583);
lean_dec(x_581);
lean_dec(x_579);
lean_dec(x_577);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_565);
lean_dec_ref(x_564);
lean_dec(x_563);
lean_dec_ref(x_562);
lean_dec(x_561);
lean_dec_ref(x_1);
x_604 = lean_ctor_get(x_596, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_596, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_606 = x_596;
} else {
 lean_dec_ref(x_596);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_606)) {
 x_607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_607 = x_606;
}
lean_ctor_set(x_607, 0, x_604);
lean_ctor_set(x_607, 1, x_605);
return x_607;
}
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_577);
lean_dec(x_571);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_565);
lean_dec_ref(x_564);
lean_dec(x_563);
lean_dec_ref(x_562);
lean_dec(x_561);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_654 = lean_ctor_get(x_578, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_578, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 x_656 = x_578;
} else {
 lean_dec_ref(x_578);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_657 = lean_alloc_ctor(1, 2, 0);
} else {
 x_657 = x_656;
}
lean_ctor_set(x_657, 0, x_654);
lean_ctor_set(x_657, 1, x_655);
return x_657;
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_571);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_565);
lean_dec_ref(x_564);
lean_dec(x_563);
lean_dec_ref(x_562);
lean_dec(x_561);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_658 = lean_ctor_get(x_574, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_574, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_660 = x_574;
} else {
 lean_dec_ref(x_574);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 2, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_658);
lean_ctor_set(x_661, 1, x_659);
return x_661;
}
}
else
{
lean_object* x_662; 
lean_dec(x_565);
lean_dec_ref(x_564);
lean_dec(x_563);
lean_dec_ref(x_562);
lean_dec(x_561);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_662 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_560);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_662;
}
}
}
else
{
uint8_t x_663; 
lean_dec_ref(x_446);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_663 = !lean_is_exclusive(x_447);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; 
x_664 = lean_ctor_get(x_447, 0);
lean_dec(x_664);
x_665 = lean_ctor_get(x_448, 0);
lean_inc(x_665);
lean_dec_ref(x_448);
lean_ctor_set(x_447, 0, x_665);
return x_447;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_ctor_get(x_447, 1);
lean_inc(x_666);
lean_dec(x_447);
x_667 = lean_ctor_get(x_448, 0);
lean_inc(x_667);
lean_dec_ref(x_448);
x_668 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_666);
return x_668;
}
}
}
else
{
uint8_t x_669; 
lean_dec_ref(x_446);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_669 = !lean_is_exclusive(x_447);
if (x_669 == 0)
{
return x_447;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_447, 0);
x_671 = lean_ctor_get(x_447, 1);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_447);
x_672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
return x_672;
}
}
}
case 5:
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_free_object(x_70);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_673 = lean_ctor_get(x_1, 0);
x_674 = lean_st_ref_get(x_3, x_72);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec_ref(x_674);
x_677 = lean_ctor_get(x_675, 0);
lean_inc_ref(x_677);
lean_dec(x_675);
lean_inc(x_673);
x_678 = l_Lean_Compiler_LCNF_normFVarImp(x_677, x_673, x_54);
lean_dec_ref(x_677);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
lean_dec_ref(x_678);
lean_inc(x_679);
x_680 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_679, x_3, x_676);
lean_dec(x_3);
if (lean_obj_tag(x_680) == 0)
{
uint8_t x_681; 
x_681 = !lean_is_exclusive(x_680);
if (x_681 == 0)
{
lean_object* x_682; uint8_t x_683; 
x_682 = lean_ctor_get(x_680, 0);
lean_dec(x_682);
x_683 = l_Lean_instBEqFVarId_beq(x_673, x_679);
if (x_683 == 0)
{
uint8_t x_684; 
x_684 = !lean_is_exclusive(x_1);
if (x_684 == 0)
{
lean_object* x_685; 
x_685 = lean_ctor_get(x_1, 0);
lean_dec(x_685);
lean_ctor_set(x_1, 0, x_679);
lean_ctor_set(x_680, 0, x_1);
return x_680;
}
else
{
lean_object* x_686; 
lean_dec(x_1);
x_686 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_686, 0, x_679);
lean_ctor_set(x_680, 0, x_686);
return x_680;
}
}
else
{
lean_dec(x_679);
lean_ctor_set(x_680, 0, x_1);
return x_680;
}
}
else
{
lean_object* x_687; uint8_t x_688; 
x_687 = lean_ctor_get(x_680, 1);
lean_inc(x_687);
lean_dec(x_680);
x_688 = l_Lean_instBEqFVarId_beq(x_673, x_679);
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_689 = x_1;
} else {
 lean_dec_ref(x_1);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(5, 1, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_679);
x_691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_687);
return x_691;
}
else
{
lean_object* x_692; 
lean_dec(x_679);
x_692 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_692, 0, x_1);
lean_ctor_set(x_692, 1, x_687);
return x_692;
}
}
}
else
{
uint8_t x_693; 
lean_dec(x_679);
lean_dec_ref(x_1);
x_693 = !lean_is_exclusive(x_680);
if (x_693 == 0)
{
return x_680;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_694 = lean_ctor_get(x_680, 0);
x_695 = lean_ctor_get(x_680, 1);
lean_inc(x_695);
lean_inc(x_694);
lean_dec(x_680);
x_696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set(x_696, 1, x_695);
return x_696;
}
}
}
else
{
lean_object* x_697; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_697 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_676);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_697;
}
}
case 6:
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; size_t x_704; size_t x_705; uint8_t x_706; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_698 = lean_ctor_get(x_1, 0);
x_699 = lean_st_ref_get(x_3, x_72);
lean_dec(x_3);
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec_ref(x_699);
x_702 = lean_ctor_get(x_700, 0);
lean_inc_ref(x_702);
lean_dec(x_700);
lean_inc_ref(x_698);
x_703 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_702, x_54, x_698);
lean_dec_ref(x_702);
x_704 = lean_ptr_addr(x_698);
x_705 = lean_ptr_addr(x_703);
x_706 = lean_usize_dec_eq(x_704, x_705);
if (x_706 == 0)
{
uint8_t x_707; 
x_707 = !lean_is_exclusive(x_1);
if (x_707 == 0)
{
lean_object* x_708; 
x_708 = lean_ctor_get(x_1, 0);
lean_dec(x_708);
lean_ctor_set(x_1, 0, x_703);
lean_ctor_set(x_70, 1, x_701);
lean_ctor_set(x_70, 0, x_1);
return x_70;
}
else
{
lean_object* x_709; 
lean_dec(x_1);
x_709 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_709, 0, x_703);
lean_ctor_set(x_70, 1, x_701);
lean_ctor_set(x_70, 0, x_709);
return x_70;
}
}
else
{
lean_dec_ref(x_703);
lean_ctor_set(x_70, 1, x_701);
lean_ctor_set(x_70, 0, x_1);
return x_70;
}
}
default: 
{
lean_object* x_710; lean_object* x_711; 
lean_free_object(x_70);
x_710 = lean_ctor_get(x_1, 0);
x_711 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_711);
lean_inc_ref(x_710);
x_74 = x_710;
x_75 = x_711;
x_76 = x_2;
x_77 = x_3;
x_78 = x_4;
x_79 = x_5;
x_80 = x_6;
x_81 = x_7;
x_82 = x_8;
goto block_135;
}
}
block_135:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_74, 0);
x_84 = lean_ctor_get(x_74, 2);
x_85 = lean_ctor_get(x_74, 3);
x_86 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_83, x_77, x_72);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec_ref(x_86);
lean_inc(x_87);
lean_inc_ref(x_1);
lean_inc_ref(x_75);
x_89 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_89, 0, x_75);
lean_closure_set(x_89, 1, x_1);
lean_closure_set(x_89, 2, x_87);
x_90 = lean_unbox(x_87);
if (x_90 == 0)
{
uint8_t x_91; 
lean_dec(x_87);
lean_dec_ref(x_75);
x_91 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_91 == 0)
{
x_18 = x_89;
x_19 = x_74;
x_20 = x_76;
x_21 = x_77;
x_22 = x_78;
x_23 = x_79;
x_24 = x_80;
x_25 = x_81;
x_26 = x_82;
x_27 = x_88;
goto block_37;
}
else
{
uint8_t x_92; 
lean_inc_ref(x_85);
x_92 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_85, x_84);
if (x_92 == 0)
{
x_18 = x_89;
x_19 = x_74;
x_20 = x_76;
x_21 = x_77;
x_22 = x_78;
x_23 = x_79;
x_24 = x_80;
x_25 = x_81;
x_26 = x_82;
x_27 = x_88;
goto block_37;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_st_ref_get(x_77, x_88);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc_ref(x_96);
lean_dec(x_94);
x_97 = l_Lean_Compiler_LCNF_normFunDeclImp(x_54, x_74, x_96, x_79, x_80, x_81, x_82, x_95);
lean_dec_ref(x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
lean_inc(x_82);
lean_inc_ref(x_81);
lean_inc(x_80);
lean_inc_ref(x_79);
x_100 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_98, x_79, x_80, x_81, x_82, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
x_103 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_77, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec_ref(x_103);
x_18 = x_89;
x_19 = x_101;
x_20 = x_76;
x_21 = x_77;
x_22 = x_78;
x_23 = x_79;
x_24 = x_80;
x_25 = x_81;
x_26 = x_82;
x_27 = x_104;
goto block_37;
}
else
{
uint8_t x_105; 
lean_dec(x_101);
lean_dec_ref(x_89);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
x_105 = !lean_is_exclusive(x_103);
if (x_105 == 0)
{
return x_103;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_103, 0);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_103);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec_ref(x_89);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
x_109 = !lean_is_exclusive(x_100);
if (x_109 == 0)
{
return x_100;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_100, 0);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_100);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec_ref(x_89);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
x_113 = !lean_is_exclusive(x_97);
if (x_113 == 0)
{
return x_97;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_97, 0);
x_115 = lean_ctor_get(x_97, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_97);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_89);
x_117 = lean_st_ref_get(x_77, x_88);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_120);
lean_dec(x_118);
x_121 = l_Lean_Compiler_LCNF_normFunDeclImp(x_54, x_74, x_120, x_79, x_80, x_81, x_82, x_119);
lean_dec_ref(x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_124 = lean_box(0);
x_125 = lean_unbox(x_87);
lean_dec(x_87);
x_126 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_75, x_1, x_125, x_122, x_124, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_123);
return x_126;
}
else
{
uint8_t x_127; 
lean_dec(x_87);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_1);
x_127 = !lean_is_exclusive(x_121);
if (x_127 == 0)
{
return x_121;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_121, 0);
x_129 = lean_ctor_get(x_121, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_121);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_1);
x_131 = !lean_is_exclusive(x_86);
if (x_131 == 0)
{
return x_86;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_86, 0);
x_133 = lean_ctor_get(x_86, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_86);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_775; lean_object* x_776; 
x_712 = lean_ctor_get(x_70, 1);
lean_inc(x_712);
lean_dec(x_70);
x_775 = lean_unsigned_to_nat(1u);
x_776 = lean_nat_add(x_41, x_775);
lean_dec(x_41);
lean_ctor_set(x_7, 3, x_776);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; uint8_t x_788; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_957; 
x_777 = lean_ctor_get(x_1, 0);
x_778 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_777);
x_957 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_54, x_777, x_3, x_6, x_712);
if (lean_obj_tag(x_957) == 0)
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; uint8_t x_1002; 
x_958 = lean_ctor_get(x_957, 0);
lean_inc(x_958);
x_959 = lean_ctor_get(x_957, 1);
lean_inc(x_959);
lean_dec_ref(x_957);
x_1002 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_777, x_958);
if (x_1002 == 0)
{
goto block_1001;
}
else
{
if (x_54 == 0)
{
x_960 = x_2;
x_961 = x_3;
x_962 = x_4;
x_963 = x_5;
x_964 = x_6;
x_965 = x_7;
x_966 = x_8;
x_967 = x_959;
goto block_994;
}
else
{
goto block_1001;
}
}
block_994:
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_968 = lean_ctor_get(x_958, 2);
x_969 = lean_ctor_get(x_958, 3);
lean_inc(x_966);
lean_inc_ref(x_965);
lean_inc(x_964);
lean_inc_ref(x_963);
lean_inc_ref(x_962);
lean_inc(x_969);
x_970 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_969, x_960, x_962, x_963, x_964, x_965, x_966, x_967);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
if (lean_obj_tag(x_971) == 0)
{
lean_object* x_972; 
lean_inc(x_969);
lean_inc_ref(x_968);
x_972 = lean_ctor_get(x_970, 1);
lean_inc(x_972);
lean_dec_ref(x_970);
x_942 = x_958;
x_943 = x_968;
x_944 = x_969;
x_945 = x_960;
x_946 = x_961;
x_947 = x_962;
x_948 = x_963;
x_949 = x_964;
x_950 = x_965;
x_951 = x_966;
x_952 = x_972;
goto block_956;
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; 
x_973 = lean_ctor_get(x_970, 1);
lean_inc(x_973);
lean_dec_ref(x_970);
x_974 = lean_ctor_get(x_971, 0);
lean_inc(x_974);
lean_dec_ref(x_971);
x_975 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_961, x_973);
if (lean_obj_tag(x_975) == 0)
{
lean_object* x_976; lean_object* x_977; 
x_976 = lean_ctor_get(x_975, 1);
lean_inc(x_976);
lean_dec_ref(x_975);
x_977 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_958, x_974, x_964, x_976);
if (lean_obj_tag(x_977) == 0)
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; 
x_978 = lean_ctor_get(x_977, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_977, 1);
lean_inc(x_979);
lean_dec_ref(x_977);
x_980 = lean_ctor_get(x_978, 2);
lean_inc_ref(x_980);
x_981 = lean_ctor_get(x_978, 3);
lean_inc(x_981);
x_942 = x_978;
x_943 = x_980;
x_944 = x_981;
x_945 = x_960;
x_946 = x_961;
x_947 = x_962;
x_948 = x_963;
x_949 = x_964;
x_950 = x_965;
x_951 = x_966;
x_952 = x_979;
goto block_956;
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_963);
lean_dec_ref(x_962);
lean_dec(x_961);
lean_dec_ref(x_960);
lean_dec_ref(x_1);
x_982 = lean_ctor_get(x_977, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_977, 1);
lean_inc(x_983);
if (lean_is_exclusive(x_977)) {
 lean_ctor_release(x_977, 0);
 lean_ctor_release(x_977, 1);
 x_984 = x_977;
} else {
 lean_dec_ref(x_977);
 x_984 = lean_box(0);
}
if (lean_is_scalar(x_984)) {
 x_985 = lean_alloc_ctor(1, 2, 0);
} else {
 x_985 = x_984;
}
lean_ctor_set(x_985, 0, x_982);
lean_ctor_set(x_985, 1, x_983);
return x_985;
}
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; 
lean_dec(x_974);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_963);
lean_dec_ref(x_962);
lean_dec(x_961);
lean_dec_ref(x_960);
lean_dec(x_958);
lean_dec_ref(x_1);
x_986 = lean_ctor_get(x_975, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_975, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 lean_ctor_release(x_975, 1);
 x_988 = x_975;
} else {
 lean_dec_ref(x_975);
 x_988 = lean_box(0);
}
if (lean_is_scalar(x_988)) {
 x_989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_989 = x_988;
}
lean_ctor_set(x_989, 0, x_986);
lean_ctor_set(x_989, 1, x_987);
return x_989;
}
}
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_963);
lean_dec_ref(x_962);
lean_dec(x_961);
lean_dec_ref(x_960);
lean_dec(x_958);
lean_dec_ref(x_1);
x_990 = lean_ctor_get(x_970, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_970, 1);
lean_inc(x_991);
if (lean_is_exclusive(x_970)) {
 lean_ctor_release(x_970, 0);
 lean_ctor_release(x_970, 1);
 x_992 = x_970;
} else {
 lean_dec_ref(x_970);
 x_992 = lean_box(0);
}
if (lean_is_scalar(x_992)) {
 x_993 = lean_alloc_ctor(1, 2, 0);
} else {
 x_993 = x_992;
}
lean_ctor_set(x_993, 0, x_990);
lean_ctor_set(x_993, 1, x_991);
return x_993;
}
}
block_1001:
{
lean_object* x_995; 
x_995 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_959);
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_996; 
x_996 = lean_ctor_get(x_995, 1);
lean_inc(x_996);
lean_dec_ref(x_995);
x_960 = x_2;
x_961 = x_3;
x_962 = x_4;
x_963 = x_5;
x_964 = x_6;
x_965 = x_7;
x_966 = x_8;
x_967 = x_996;
goto block_994;
}
else
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
lean_dec(x_958);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_997 = lean_ctor_get(x_995, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_995, 1);
lean_inc(x_998);
if (lean_is_exclusive(x_995)) {
 lean_ctor_release(x_995, 0);
 lean_ctor_release(x_995, 1);
 x_999 = x_995;
} else {
 lean_dec_ref(x_995);
 x_999 = lean_box(0);
}
if (lean_is_scalar(x_999)) {
 x_1000 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1000 = x_999;
}
lean_ctor_set(x_1000, 0, x_997);
lean_ctor_set(x_1000, 1, x_998);
return x_1000;
}
}
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1003 = lean_ctor_get(x_957, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_957, 1);
lean_inc(x_1004);
if (lean_is_exclusive(x_957)) {
 lean_ctor_release(x_957, 0);
 lean_ctor_release(x_957, 1);
 x_1005 = x_957;
} else {
 lean_dec_ref(x_957);
 x_1005 = lean_box(0);
}
if (lean_is_scalar(x_1005)) {
 x_1006 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1006 = x_1005;
}
lean_ctor_set(x_1006, 0, x_1003);
lean_ctor_set(x_1006, 1, x_1004);
return x_1006;
}
block_941:
{
if (x_788 == 0)
{
lean_object* x_789; 
lean_inc(x_779);
lean_inc_ref(x_787);
lean_inc(x_781);
lean_inc_ref(x_783);
lean_inc_ref(x_780);
x_789 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_780, x_783, x_781, x_787, x_779, x_782);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_791; lean_object* x_792; 
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec_ref(x_789);
lean_inc(x_779);
lean_inc_ref(x_787);
lean_inc(x_781);
lean_inc_ref(x_783);
lean_inc_ref(x_780);
x_792 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_780, x_786, x_785, x_783, x_781, x_787, x_779, x_791);
if (lean_obj_tag(x_792) == 0)
{
lean_object* x_793; 
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
lean_dec_ref(x_792);
x_795 = lean_ctor_get(x_780, 0);
x_796 = lean_ctor_get(x_780, 3);
lean_inc(x_796);
x_797 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_796, x_794);
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
if (lean_obj_tag(x_798) == 0)
{
lean_object* x_799; lean_object* x_800; 
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
lean_dec_ref(x_797);
lean_inc(x_779);
lean_inc_ref(x_787);
lean_inc(x_781);
lean_inc_ref(x_783);
lean_inc_ref(x_784);
lean_inc(x_785);
lean_inc_ref(x_786);
lean_inc_ref(x_778);
lean_inc_ref(x_780);
x_800 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_780, x_778, x_786, x_785, x_784, x_783, x_781, x_787, x_779, x_799);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_801; 
x_801 = lean_ctor_get(x_800, 0);
lean_inc(x_801);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; 
x_802 = lean_ctor_get(x_800, 1);
lean_inc(x_802);
lean_dec_ref(x_800);
lean_inc(x_779);
lean_inc_ref(x_787);
lean_inc(x_781);
lean_inc_ref(x_783);
lean_inc_ref(x_784);
lean_inc(x_785);
lean_inc_ref(x_786);
lean_inc(x_796);
x_803 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_796, x_786, x_785, x_784, x_783, x_781, x_787, x_779, x_802);
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_804; 
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
if (lean_obj_tag(x_804) == 0)
{
lean_object* x_805; lean_object* x_806; 
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
lean_dec_ref(x_803);
lean_inc(x_779);
lean_inc_ref(x_787);
lean_inc(x_781);
lean_inc_ref(x_783);
lean_inc_ref(x_784);
lean_inc(x_785);
lean_inc_ref(x_786);
lean_inc_ref(x_778);
x_806 = l_Lean_Compiler_LCNF_Simp_simp(x_778, x_786, x_785, x_784, x_783, x_781, x_787, x_779, x_805);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_806, 1);
lean_inc(x_808);
lean_dec_ref(x_806);
x_809 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_795, x_785, x_808);
if (lean_obj_tag(x_809) == 0)
{
lean_object* x_810; uint8_t x_811; 
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
x_811 = lean_unbox(x_810);
lean_dec(x_810);
if (x_811 == 0)
{
lean_object* x_812; lean_object* x_813; 
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_779);
lean_dec_ref(x_1);
x_812 = lean_ctor_get(x_809, 1);
lean_inc(x_812);
lean_dec_ref(x_809);
x_813 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_780, x_785, x_781, x_812);
lean_dec(x_781);
lean_dec(x_785);
lean_dec_ref(x_780);
if (lean_obj_tag(x_813) == 0)
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_814 = lean_ctor_get(x_813, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_815 = x_813;
} else {
 lean_dec_ref(x_813);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_815)) {
 x_816 = lean_alloc_ctor(0, 2, 0);
} else {
 x_816 = x_815;
}
lean_ctor_set(x_816, 0, x_807);
lean_ctor_set(x_816, 1, x_814);
return x_816;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_dec(x_807);
x_817 = lean_ctor_get(x_813, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_813, 1);
lean_inc(x_818);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_819 = x_813;
} else {
 lean_dec_ref(x_813);
 x_819 = lean_box(0);
}
if (lean_is_scalar(x_819)) {
 x_820 = lean_alloc_ctor(1, 2, 0);
} else {
 x_820 = x_819;
}
lean_ctor_set(x_820, 0, x_817);
lean_ctor_set(x_820, 1, x_818);
return x_820;
}
}
else
{
lean_object* x_821; lean_object* x_822; 
x_821 = lean_ctor_get(x_809, 1);
lean_inc(x_821);
lean_dec_ref(x_809);
lean_inc_ref(x_780);
x_822 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_780, x_786, x_785, x_784, x_783, x_781, x_787, x_779, x_821);
lean_dec(x_779);
lean_dec_ref(x_787);
lean_dec(x_781);
lean_dec_ref(x_783);
lean_dec_ref(x_784);
lean_dec(x_785);
lean_dec_ref(x_786);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_823; size_t x_824; size_t x_825; uint8_t x_826; 
x_823 = lean_ctor_get(x_822, 1);
lean_inc(x_823);
lean_dec_ref(x_822);
x_824 = lean_ptr_addr(x_778);
x_825 = lean_ptr_addr(x_807);
x_826 = lean_usize_dec_eq(x_824, x_825);
if (x_826 == 0)
{
x_10 = x_780;
x_11 = x_823;
x_12 = x_807;
x_13 = x_826;
goto block_17;
}
else
{
size_t x_827; size_t x_828; uint8_t x_829; 
x_827 = lean_ptr_addr(x_777);
x_828 = lean_ptr_addr(x_780);
x_829 = lean_usize_dec_eq(x_827, x_828);
x_10 = x_780;
x_11 = x_823;
x_12 = x_807;
x_13 = x_829;
goto block_17;
}
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
lean_dec(x_807);
lean_dec_ref(x_780);
lean_dec_ref(x_1);
x_830 = lean_ctor_get(x_822, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_822, 1);
lean_inc(x_831);
if (lean_is_exclusive(x_822)) {
 lean_ctor_release(x_822, 0);
 lean_ctor_release(x_822, 1);
 x_832 = x_822;
} else {
 lean_dec_ref(x_822);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(1, 2, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_830);
lean_ctor_set(x_833, 1, x_831);
return x_833;
}
}
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
lean_dec(x_807);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_1);
x_834 = lean_ctor_get(x_809, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_809, 1);
lean_inc(x_835);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 x_836 = x_809;
} else {
 lean_dec_ref(x_809);
 x_836 = lean_box(0);
}
if (lean_is_scalar(x_836)) {
 x_837 = lean_alloc_ctor(1, 2, 0);
} else {
 x_837 = x_836;
}
lean_ctor_set(x_837, 0, x_834);
lean_ctor_set(x_837, 1, x_835);
return x_837;
}
}
else
{
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_1);
return x_806;
}
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_inc_ref(x_778);
lean_dec_ref(x_1);
x_838 = lean_ctor_get(x_804, 0);
lean_inc(x_838);
lean_dec_ref(x_804);
x_839 = lean_ctor_get(x_803, 1);
lean_inc(x_839);
lean_dec_ref(x_803);
x_840 = lean_ctor_get(x_838, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_838, 1);
lean_inc(x_841);
lean_dec(x_838);
lean_inc(x_795);
x_842 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_795, x_841, x_785, x_781, x_787, x_779, x_839);
if (lean_obj_tag(x_842) == 0)
{
lean_object* x_843; lean_object* x_844; 
x_843 = lean_ctor_get(x_842, 1);
lean_inc(x_843);
lean_dec_ref(x_842);
x_844 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_780, x_785, x_781, x_843);
lean_dec_ref(x_780);
if (lean_obj_tag(x_844) == 0)
{
lean_object* x_845; lean_object* x_846; 
x_845 = lean_ctor_get(x_844, 1);
lean_inc(x_845);
lean_dec_ref(x_844);
lean_inc(x_779);
lean_inc_ref(x_787);
lean_inc(x_781);
lean_inc_ref(x_783);
lean_inc_ref(x_784);
lean_inc(x_785);
lean_inc_ref(x_786);
x_846 = l_Lean_Compiler_LCNF_Simp_simp(x_778, x_786, x_785, x_784, x_783, x_781, x_787, x_779, x_845);
if (lean_obj_tag(x_846) == 0)
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_847 = lean_ctor_get(x_846, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_846, 1);
lean_inc(x_848);
lean_dec_ref(x_846);
x_849 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_840, x_847, x_786, x_785, x_784, x_783, x_781, x_787, x_779, x_848);
lean_dec(x_779);
lean_dec_ref(x_787);
lean_dec(x_781);
lean_dec_ref(x_783);
lean_dec_ref(x_784);
lean_dec(x_785);
lean_dec_ref(x_786);
lean_dec(x_840);
return x_849;
}
else
{
lean_dec(x_840);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec(x_779);
return x_846;
}
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; 
lean_dec(x_840);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec(x_779);
lean_dec_ref(x_778);
x_850 = lean_ctor_get(x_844, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_844, 1);
lean_inc(x_851);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_852 = x_844;
} else {
 lean_dec_ref(x_844);
 x_852 = lean_box(0);
}
if (lean_is_scalar(x_852)) {
 x_853 = lean_alloc_ctor(1, 2, 0);
} else {
 x_853 = x_852;
}
lean_ctor_set(x_853, 0, x_850);
lean_ctor_set(x_853, 1, x_851);
return x_853;
}
}
else
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; 
lean_dec(x_840);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_778);
x_854 = lean_ctor_get(x_842, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_842, 1);
lean_inc(x_855);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 lean_ctor_release(x_842, 1);
 x_856 = x_842;
} else {
 lean_dec_ref(x_842);
 x_856 = lean_box(0);
}
if (lean_is_scalar(x_856)) {
 x_857 = lean_alloc_ctor(1, 2, 0);
} else {
 x_857 = x_856;
}
lean_ctor_set(x_857, 0, x_854);
lean_ctor_set(x_857, 1, x_855);
return x_857;
}
}
}
else
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_1);
x_858 = lean_ctor_get(x_803, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_803, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_860 = x_803;
} else {
 lean_dec_ref(x_803);
 x_860 = lean_box(0);
}
if (lean_is_scalar(x_860)) {
 x_861 = lean_alloc_ctor(1, 2, 0);
} else {
 x_861 = x_860;
}
lean_ctor_set(x_861, 0, x_858);
lean_ctor_set(x_861, 1, x_859);
return x_861;
}
}
else
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; 
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_779);
lean_dec_ref(x_1);
x_862 = lean_ctor_get(x_800, 1);
lean_inc(x_862);
lean_dec_ref(x_800);
x_863 = lean_ctor_get(x_801, 0);
lean_inc(x_863);
lean_dec_ref(x_801);
x_864 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_780, x_785, x_781, x_862);
lean_dec(x_781);
lean_dec(x_785);
lean_dec_ref(x_780);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_865 = lean_ctor_get(x_864, 1);
lean_inc(x_865);
if (lean_is_exclusive(x_864)) {
 lean_ctor_release(x_864, 0);
 lean_ctor_release(x_864, 1);
 x_866 = x_864;
} else {
 lean_dec_ref(x_864);
 x_866 = lean_box(0);
}
if (lean_is_scalar(x_866)) {
 x_867 = lean_alloc_ctor(0, 2, 0);
} else {
 x_867 = x_866;
}
lean_ctor_set(x_867, 0, x_863);
lean_ctor_set(x_867, 1, x_865);
return x_867;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; 
lean_dec(x_863);
x_868 = lean_ctor_get(x_864, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_864, 1);
lean_inc(x_869);
if (lean_is_exclusive(x_864)) {
 lean_ctor_release(x_864, 0);
 lean_ctor_release(x_864, 1);
 x_870 = x_864;
} else {
 lean_dec_ref(x_864);
 x_870 = lean_box(0);
}
if (lean_is_scalar(x_870)) {
 x_871 = lean_alloc_ctor(1, 2, 0);
} else {
 x_871 = x_870;
}
lean_ctor_set(x_871, 0, x_868);
lean_ctor_set(x_871, 1, x_869);
return x_871;
}
}
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_1);
x_872 = lean_ctor_get(x_800, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_800, 1);
lean_inc(x_873);
if (lean_is_exclusive(x_800)) {
 lean_ctor_release(x_800, 0);
 lean_ctor_release(x_800, 1);
 x_874 = x_800;
} else {
 lean_dec_ref(x_800);
 x_874 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_875 = lean_alloc_ctor(1, 2, 0);
} else {
 x_875 = x_874;
}
lean_ctor_set(x_875, 0, x_872);
lean_ctor_set(x_875, 1, x_873);
return x_875;
}
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
lean_inc_ref(x_778);
lean_dec_ref(x_1);
x_876 = lean_ctor_get(x_797, 1);
lean_inc(x_876);
lean_dec_ref(x_797);
x_877 = lean_ctor_get(x_798, 0);
lean_inc(x_877);
lean_dec_ref(x_798);
lean_inc(x_795);
x_878 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_795, x_877, x_785, x_781, x_787, x_779, x_876);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; lean_object* x_880; 
x_879 = lean_ctor_get(x_878, 1);
lean_inc(x_879);
lean_dec_ref(x_878);
x_880 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_780, x_785, x_781, x_879);
lean_dec_ref(x_780);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; 
x_881 = lean_ctor_get(x_880, 1);
lean_inc(x_881);
lean_dec_ref(x_880);
x_1 = x_778;
x_2 = x_786;
x_3 = x_785;
x_4 = x_784;
x_5 = x_783;
x_6 = x_781;
x_7 = x_787;
x_8 = x_779;
x_9 = x_881;
goto _start;
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec(x_779);
lean_dec_ref(x_778);
x_883 = lean_ctor_get(x_880, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_880, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 lean_ctor_release(x_880, 1);
 x_885 = x_880;
} else {
 lean_dec_ref(x_880);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(1, 2, 0);
} else {
 x_886 = x_885;
}
lean_ctor_set(x_886, 0, x_883);
lean_ctor_set(x_886, 1, x_884);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_778);
x_887 = lean_ctor_get(x_878, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_878, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_889 = x_878;
} else {
 lean_dec_ref(x_878);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_887);
lean_ctor_set(x_890, 1, x_888);
return x_890;
}
}
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
lean_dec_ref(x_780);
lean_inc_ref(x_778);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_891 = x_1;
} else {
 lean_dec_ref(x_1);
 x_891 = lean_box(0);
}
x_892 = lean_ctor_get(x_792, 1);
lean_inc(x_892);
lean_dec_ref(x_792);
x_893 = lean_ctor_get(x_793, 0);
lean_inc(x_893);
lean_dec_ref(x_793);
if (lean_is_scalar(x_891)) {
 x_894 = lean_alloc_ctor(1, 2, 0);
} else {
 x_894 = x_891;
 lean_ctor_set_tag(x_894, 1);
}
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_778);
x_1 = x_894;
x_2 = x_786;
x_3 = x_785;
x_4 = x_784;
x_5 = x_783;
x_6 = x_781;
x_7 = x_787;
x_8 = x_779;
x_9 = x_892;
goto _start;
}
}
else
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; 
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_1);
x_896 = lean_ctor_get(x_792, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_792, 1);
lean_inc(x_897);
if (lean_is_exclusive(x_792)) {
 lean_ctor_release(x_792, 0);
 lean_ctor_release(x_792, 1);
 x_898 = x_792;
} else {
 lean_dec_ref(x_792);
 x_898 = lean_box(0);
}
if (lean_is_scalar(x_898)) {
 x_899 = lean_alloc_ctor(1, 2, 0);
} else {
 x_899 = x_898;
}
lean_ctor_set(x_899, 0, x_896);
lean_ctor_set(x_899, 1, x_897);
return x_899;
}
}
else
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec_ref(x_780);
lean_inc_ref(x_778);
lean_dec_ref(x_1);
x_900 = lean_ctor_get(x_789, 1);
lean_inc(x_900);
lean_dec_ref(x_789);
x_901 = lean_ctor_get(x_790, 0);
lean_inc(x_901);
lean_dec_ref(x_790);
x_902 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_785, x_900);
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_903; lean_object* x_904; 
x_903 = lean_ctor_get(x_902, 1);
lean_inc(x_903);
lean_dec_ref(x_902);
lean_inc(x_779);
lean_inc_ref(x_787);
lean_inc(x_781);
lean_inc_ref(x_783);
lean_inc_ref(x_784);
lean_inc(x_785);
lean_inc_ref(x_786);
x_904 = l_Lean_Compiler_LCNF_Simp_simp(x_778, x_786, x_785, x_784, x_783, x_781, x_787, x_779, x_903);
if (lean_obj_tag(x_904) == 0)
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; 
x_905 = lean_ctor_get(x_904, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_904, 1);
lean_inc(x_906);
lean_dec_ref(x_904);
x_907 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_901, x_905, x_786, x_785, x_784, x_783, x_781, x_787, x_779, x_906);
lean_dec(x_779);
lean_dec_ref(x_787);
lean_dec(x_781);
lean_dec_ref(x_783);
lean_dec_ref(x_784);
lean_dec(x_785);
lean_dec_ref(x_786);
lean_dec(x_901);
return x_907;
}
else
{
lean_dec(x_901);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec(x_779);
return x_904;
}
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
lean_dec(x_901);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec(x_779);
lean_dec_ref(x_778);
x_908 = lean_ctor_get(x_902, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_902, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_910 = x_902;
} else {
 lean_dec_ref(x_902);
 x_910 = lean_box(0);
}
if (lean_is_scalar(x_910)) {
 x_911 = lean_alloc_ctor(1, 2, 0);
} else {
 x_911 = x_910;
}
lean_ctor_set(x_911, 0, x_908);
lean_ctor_set(x_911, 1, x_909);
return x_911;
}
}
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_1);
x_912 = lean_ctor_get(x_789, 0);
lean_inc(x_912);
x_913 = lean_ctor_get(x_789, 1);
lean_inc(x_913);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_914 = x_789;
} else {
 lean_dec_ref(x_789);
 x_914 = lean_box(0);
}
if (lean_is_scalar(x_914)) {
 x_915 = lean_alloc_ctor(1, 2, 0);
} else {
 x_915 = x_914;
}
lean_ctor_set(x_915, 0, x_912);
lean_ctor_set(x_915, 1, x_913);
return x_915;
}
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; uint8_t x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_inc_ref(x_778);
lean_dec_ref(x_1);
x_916 = lean_st_ref_take(x_785, x_782);
x_917 = lean_ctor_get(x_916, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_916, 1);
lean_inc(x_918);
lean_dec_ref(x_916);
x_919 = lean_ctor_get(x_780, 0);
x_920 = lean_ctor_get(x_917, 0);
lean_inc_ref(x_920);
x_921 = lean_ctor_get(x_917, 1);
lean_inc_ref(x_921);
x_922 = lean_ctor_get(x_917, 2);
lean_inc(x_922);
x_923 = lean_ctor_get(x_917, 3);
lean_inc_ref(x_923);
x_924 = lean_ctor_get_uint8(x_917, sizeof(void*)*7);
x_925 = lean_ctor_get(x_917, 4);
lean_inc(x_925);
x_926 = lean_ctor_get(x_917, 5);
lean_inc(x_926);
x_927 = lean_ctor_get(x_917, 6);
lean_inc(x_927);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 lean_ctor_release(x_917, 1);
 lean_ctor_release(x_917, 2);
 lean_ctor_release(x_917, 3);
 lean_ctor_release(x_917, 4);
 lean_ctor_release(x_917, 5);
 lean_ctor_release(x_917, 6);
 x_928 = x_917;
} else {
 lean_dec_ref(x_917);
 x_928 = lean_box(0);
}
x_929 = lean_box(0);
lean_inc(x_919);
x_930 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_920, x_919, x_929);
if (lean_is_scalar(x_928)) {
 x_931 = lean_alloc_ctor(0, 7, 1);
} else {
 x_931 = x_928;
}
lean_ctor_set(x_931, 0, x_930);
lean_ctor_set(x_931, 1, x_921);
lean_ctor_set(x_931, 2, x_922);
lean_ctor_set(x_931, 3, x_923);
lean_ctor_set(x_931, 4, x_925);
lean_ctor_set(x_931, 5, x_926);
lean_ctor_set(x_931, 6, x_927);
lean_ctor_set_uint8(x_931, sizeof(void*)*7, x_924);
x_932 = lean_st_ref_set(x_785, x_931, x_918);
x_933 = lean_ctor_get(x_932, 1);
lean_inc(x_933);
lean_dec_ref(x_932);
x_934 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_780, x_785, x_781, x_933);
lean_dec_ref(x_780);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; 
x_935 = lean_ctor_get(x_934, 1);
lean_inc(x_935);
lean_dec_ref(x_934);
x_1 = x_778;
x_2 = x_786;
x_3 = x_785;
x_4 = x_784;
x_5 = x_783;
x_6 = x_781;
x_7 = x_787;
x_8 = x_779;
x_9 = x_935;
goto _start;
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
lean_dec_ref(x_787);
lean_dec_ref(x_786);
lean_dec(x_785);
lean_dec_ref(x_784);
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec(x_779);
lean_dec_ref(x_778);
x_937 = lean_ctor_get(x_934, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_934, 1);
lean_inc(x_938);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 lean_ctor_release(x_934, 1);
 x_939 = x_934;
} else {
 lean_dec_ref(x_934);
 x_939 = lean_box(0);
}
if (lean_is_scalar(x_939)) {
 x_940 = lean_alloc_ctor(1, 2, 0);
} else {
 x_940 = x_939;
}
lean_ctor_set(x_940, 0, x_937);
lean_ctor_set(x_940, 1, x_938);
return x_940;
}
}
}
block_956:
{
uint8_t x_953; 
x_953 = l_Lean_Expr_isErased(x_943);
lean_dec_ref(x_943);
if (x_953 == 0)
{
lean_dec(x_944);
x_779 = x_951;
x_780 = x_942;
x_781 = x_949;
x_782 = x_952;
x_783 = x_948;
x_784 = x_947;
x_785 = x_946;
x_786 = x_945;
x_787 = x_950;
x_788 = x_54;
goto block_941;
}
else
{
lean_object* x_954; uint8_t x_955; 
x_954 = lean_box(1);
x_955 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_944, x_954);
lean_dec(x_944);
if (x_955 == 0)
{
x_779 = x_951;
x_780 = x_942;
x_781 = x_949;
x_782 = x_952;
x_783 = x_948;
x_784 = x_947;
x_785 = x_946;
x_786 = x_945;
x_787 = x_950;
x_788 = x_953;
goto block_941;
}
else
{
x_779 = x_951;
x_780 = x_942;
x_781 = x_949;
x_782 = x_952;
x_783 = x_948;
x_784 = x_947;
x_785 = x_946;
x_786 = x_945;
x_787 = x_950;
x_788 = x_54;
goto block_941;
}
}
}
}
case 3:
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1007 = lean_ctor_get(x_1, 0);
x_1008 = lean_ctor_get(x_1, 1);
x_1009 = lean_st_ref_get(x_3, x_712);
x_1010 = lean_ctor_get(x_1009, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_1009, 1);
lean_inc(x_1011);
lean_dec_ref(x_1009);
x_1012 = lean_ctor_get(x_1010, 0);
lean_inc_ref(x_1012);
lean_dec(x_1010);
lean_inc(x_1007);
x_1013 = l_Lean_Compiler_LCNF_normFVarImp(x_1012, x_1007, x_54);
lean_dec_ref(x_1012);
if (lean_obj_tag(x_1013) == 0)
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; lean_object* x_1026; lean_object* x_1032; 
x_1014 = lean_ctor_get(x_1013, 0);
lean_inc(x_1014);
lean_dec_ref(x_1013);
lean_inc_ref(x_1008);
x_1015 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_54, x_1008, x_3, x_1011);
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1015, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_1015)) {
 lean_ctor_release(x_1015, 0);
 lean_ctor_release(x_1015, 1);
 x_1018 = x_1015;
} else {
 lean_dec_ref(x_1015);
 x_1018 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1016);
x_1032 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1014, x_1016, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1017);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; 
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
if (lean_obj_tag(x_1033) == 0)
{
lean_object* x_1034; lean_object* x_1035; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec_ref(x_1032);
lean_inc(x_1014);
x_1035 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1014, x_3, x_1034);
if (lean_obj_tag(x_1035) == 0)
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; uint8_t x_1039; 
x_1036 = lean_ctor_get(x_1035, 1);
lean_inc(x_1036);
lean_dec_ref(x_1035);
x_1037 = lean_unsigned_to_nat(0u);
x_1038 = lean_array_get_size(x_1016);
x_1039 = lean_nat_dec_lt(x_1037, x_1038);
if (x_1039 == 0)
{
lean_dec(x_1038);
lean_dec(x_3);
x_1026 = x_1036;
goto block_1031;
}
else
{
uint8_t x_1040; 
x_1040 = lean_nat_dec_le(x_1038, x_1038);
if (x_1040 == 0)
{
lean_dec(x_1038);
lean_dec(x_3);
x_1026 = x_1036;
goto block_1031;
}
else
{
lean_object* x_1041; size_t x_1042; size_t x_1043; lean_object* x_1044; 
x_1041 = lean_box(0);
x_1042 = 0;
x_1043 = lean_usize_of_nat(x_1038);
lean_dec(x_1038);
x_1044 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1016, x_1042, x_1043, x_1041, x_3, x_1036);
lean_dec(x_3);
if (lean_obj_tag(x_1044) == 0)
{
lean_object* x_1045; 
x_1045 = lean_ctor_get(x_1044, 1);
lean_inc(x_1045);
lean_dec_ref(x_1044);
x_1026 = x_1045;
goto block_1031;
}
else
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
lean_dec(x_1018);
lean_dec(x_1016);
lean_dec(x_1014);
lean_dec_ref(x_1);
x_1046 = lean_ctor_get(x_1044, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1044, 1);
lean_inc(x_1047);
if (lean_is_exclusive(x_1044)) {
 lean_ctor_release(x_1044, 0);
 lean_ctor_release(x_1044, 1);
 x_1048 = x_1044;
} else {
 lean_dec_ref(x_1044);
 x_1048 = lean_box(0);
}
if (lean_is_scalar(x_1048)) {
 x_1049 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1049 = x_1048;
}
lean_ctor_set(x_1049, 0, x_1046);
lean_ctor_set(x_1049, 1, x_1047);
return x_1049;
}
}
}
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_1018);
lean_dec(x_1016);
lean_dec(x_1014);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1050 = lean_ctor_get(x_1035, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1035, 1);
lean_inc(x_1051);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 x_1052 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1052 = lean_box(0);
}
if (lean_is_scalar(x_1052)) {
 x_1053 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1053 = x_1052;
}
lean_ctor_set(x_1053, 0, x_1050);
lean_ctor_set(x_1053, 1, x_1051);
return x_1053;
}
}
else
{
lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_1018);
lean_dec(x_1016);
lean_dec(x_1014);
lean_dec_ref(x_1);
x_1054 = lean_ctor_get(x_1032, 1);
lean_inc(x_1054);
lean_dec_ref(x_1032);
x_1055 = lean_ctor_get(x_1033, 0);
lean_inc(x_1055);
lean_dec_ref(x_1033);
x_1 = x_1055;
x_9 = x_1054;
goto _start;
}
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_1018);
lean_dec(x_1016);
lean_dec(x_1014);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1057 = lean_ctor_get(x_1032, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1032, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1032)) {
 lean_ctor_release(x_1032, 0);
 lean_ctor_release(x_1032, 1);
 x_1059 = x_1032;
} else {
 lean_dec_ref(x_1032);
 x_1059 = lean_box(0);
}
if (lean_is_scalar(x_1059)) {
 x_1060 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1060 = x_1059;
}
lean_ctor_set(x_1060, 0, x_1057);
lean_ctor_set(x_1060, 1, x_1058);
return x_1060;
}
block_1025:
{
if (x_1020 == 0)
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1021 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1021 = lean_box(0);
}
if (lean_is_scalar(x_1021)) {
 x_1022 = lean_alloc_ctor(3, 2, 0);
} else {
 x_1022 = x_1021;
}
lean_ctor_set(x_1022, 0, x_1014);
lean_ctor_set(x_1022, 1, x_1016);
if (lean_is_scalar(x_1018)) {
 x_1023 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1023 = x_1018;
}
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_1019);
return x_1023;
}
else
{
lean_object* x_1024; 
lean_dec(x_1016);
lean_dec(x_1014);
if (lean_is_scalar(x_1018)) {
 x_1024 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1024 = x_1018;
}
lean_ctor_set(x_1024, 0, x_1);
lean_ctor_set(x_1024, 1, x_1019);
return x_1024;
}
}
block_1031:
{
uint8_t x_1027; 
x_1027 = l_Lean_instBEqFVarId_beq(x_1007, x_1014);
if (x_1027 == 0)
{
x_1019 = x_1026;
x_1020 = x_1027;
goto block_1025;
}
else
{
size_t x_1028; size_t x_1029; uint8_t x_1030; 
x_1028 = lean_ptr_addr(x_1008);
x_1029 = lean_ptr_addr(x_1016);
x_1030 = lean_usize_dec_eq(x_1028, x_1029);
x_1019 = x_1026;
x_1020 = x_1030;
goto block_1025;
}
}
}
else
{
lean_object* x_1061; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1061 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_1011);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1061;
}
}
case 4:
{
lean_object* x_1062; lean_object* x_1063; 
x_1062 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1062);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1062);
x_1063 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1062, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_712);
if (lean_obj_tag(x_1063) == 0)
{
lean_object* x_1064; 
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
if (lean_obj_tag(x_1064) == 0)
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
x_1065 = lean_ctor_get(x_1063, 1);
lean_inc(x_1065);
if (lean_is_exclusive(x_1063)) {
 lean_ctor_release(x_1063, 0);
 lean_ctor_release(x_1063, 1);
 x_1066 = x_1063;
} else {
 lean_dec_ref(x_1063);
 x_1066 = lean_box(0);
}
x_1067 = lean_st_ref_get(x_3, x_1065);
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1067, 1);
lean_inc(x_1069);
lean_dec_ref(x_1067);
x_1070 = lean_ctor_get(x_1062, 0);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1062, 1);
lean_inc_ref(x_1071);
x_1072 = lean_ctor_get(x_1062, 2);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1062, 3);
lean_inc_ref(x_1073);
if (lean_is_exclusive(x_1062)) {
 lean_ctor_release(x_1062, 0);
 lean_ctor_release(x_1062, 1);
 lean_ctor_release(x_1062, 2);
 lean_ctor_release(x_1062, 3);
 x_1074 = x_1062;
} else {
 lean_dec_ref(x_1062);
 x_1074 = lean_box(0);
}
x_1075 = lean_ctor_get(x_1068, 0);
lean_inc_ref(x_1075);
lean_dec(x_1068);
lean_inc(x_1072);
x_1076 = l_Lean_Compiler_LCNF_normFVarImp(x_1075, x_1072, x_54);
lean_dec_ref(x_1075);
if (lean_obj_tag(x_1076) == 0)
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1077 = lean_ctor_get(x_1076, 0);
lean_inc(x_1077);
if (lean_is_exclusive(x_1076)) {
 lean_ctor_release(x_1076, 0);
 x_1078 = x_1076;
} else {
 lean_dec_ref(x_1076);
 x_1078 = lean_box(0);
}
x_1079 = lean_st_ref_get(x_3, x_1069);
x_1080 = lean_ctor_get(x_1079, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1079, 1);
lean_inc(x_1081);
lean_dec_ref(x_1079);
x_1082 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1073);
lean_inc(x_1077);
x_1083 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_1077, x_54, x_1082, x_1073, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1081);
if (lean_obj_tag(x_1083) == 0)
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1084 = lean_ctor_get(x_1083, 0);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1083, 1);
lean_inc(x_1085);
if (lean_is_exclusive(x_1083)) {
 lean_ctor_release(x_1083, 0);
 lean_ctor_release(x_1083, 1);
 x_1086 = x_1083;
} else {
 lean_dec_ref(x_1083);
 x_1086 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_1087 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1084, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1085);
if (lean_obj_tag(x_1087) == 0)
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1098; uint8_t x_1099; lean_object* x_1103; lean_object* x_1104; lean_object* x_1118; uint8_t x_1119; 
x_1088 = lean_ctor_get(x_1087, 0);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_1087, 1);
lean_inc(x_1089);
if (lean_is_exclusive(x_1087)) {
 lean_ctor_release(x_1087, 0);
 lean_ctor_release(x_1087, 1);
 x_1090 = x_1087;
} else {
 lean_dec_ref(x_1087);
 x_1090 = lean_box(0);
}
x_1091 = lean_ctor_get(x_1080, 0);
lean_inc_ref(x_1091);
lean_dec(x_1080);
lean_inc_ref(x_1071);
x_1092 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1091, x_54, x_1071);
lean_dec_ref(x_1091);
x_1118 = lean_array_get_size(x_1088);
x_1119 = lean_nat_dec_eq(x_1118, x_775);
lean_dec(x_1118);
if (x_1119 == 0)
{
lean_dec(x_1066);
lean_dec(x_6);
x_1103 = x_3;
x_1104 = x_1089;
goto block_1117;
}
else
{
lean_object* x_1120; 
x_1120 = lean_array_fget_borrowed(x_1088, x_1082);
if (lean_obj_tag(x_1120) == 0)
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1133; lean_object* x_1134; uint8_t x_1147; lean_object* x_1148; uint8_t x_1150; 
lean_dec(x_1066);
x_1121 = lean_ctor_get(x_1120, 1);
x_1122 = lean_ctor_get(x_1120, 2);
x_1133 = lean_array_get_size(x_1121);
x_1150 = lean_nat_dec_lt(x_1082, x_1133);
if (x_1150 == 0)
{
x_1147 = x_54;
x_1148 = x_1089;
goto block_1149;
}
else
{
if (x_1150 == 0)
{
x_1147 = x_54;
x_1148 = x_1089;
goto block_1149;
}
else
{
size_t x_1151; size_t x_1152; lean_object* x_1153; 
x_1151 = 0;
x_1152 = lean_usize_of_nat(x_1133);
x_1153 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1121, x_1151, x_1152, x_3, x_1089);
if (lean_obj_tag(x_1153) == 0)
{
lean_object* x_1154; lean_object* x_1155; uint8_t x_1156; 
x_1154 = lean_ctor_get(x_1153, 0);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1153, 1);
lean_inc(x_1155);
lean_dec_ref(x_1153);
x_1156 = lean_unbox(x_1154);
lean_dec(x_1154);
x_1147 = x_1156;
x_1148 = x_1155;
goto block_1149;
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; 
lean_dec(x_1133);
lean_dec_ref(x_1092);
lean_dec(x_1090);
lean_dec(x_1088);
lean_dec(x_1086);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec(x_1074);
lean_dec_ref(x_1073);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1157 = lean_ctor_get(x_1153, 0);
lean_inc(x_1157);
x_1158 = lean_ctor_get(x_1153, 1);
lean_inc(x_1158);
if (lean_is_exclusive(x_1153)) {
 lean_ctor_release(x_1153, 0);
 lean_ctor_release(x_1153, 1);
 x_1159 = x_1153;
} else {
 lean_dec_ref(x_1153);
 x_1159 = lean_box(0);
}
if (lean_is_scalar(x_1159)) {
 x_1160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1160 = x_1159;
}
lean_ctor_set(x_1160, 0, x_1157);
lean_ctor_set(x_1160, 1, x_1158);
return x_1160;
}
}
}
block_1132:
{
lean_object* x_1124; 
x_1124 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_1123);
lean_dec(x_3);
if (lean_obj_tag(x_1124) == 0)
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
x_1125 = lean_ctor_get(x_1124, 1);
lean_inc(x_1125);
if (lean_is_exclusive(x_1124)) {
 lean_ctor_release(x_1124, 0);
 lean_ctor_release(x_1124, 1);
 x_1126 = x_1124;
} else {
 lean_dec_ref(x_1124);
 x_1126 = lean_box(0);
}
if (lean_is_scalar(x_1126)) {
 x_1127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1127 = x_1126;
}
lean_ctor_set(x_1127, 0, x_1122);
lean_ctor_set(x_1127, 1, x_1125);
return x_1127;
}
else
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
lean_dec_ref(x_1122);
x_1128 = lean_ctor_get(x_1124, 0);
lean_inc(x_1128);
x_1129 = lean_ctor_get(x_1124, 1);
lean_inc(x_1129);
if (lean_is_exclusive(x_1124)) {
 lean_ctor_release(x_1124, 0);
 lean_ctor_release(x_1124, 1);
 x_1130 = x_1124;
} else {
 lean_dec_ref(x_1124);
 x_1130 = lean_box(0);
}
if (lean_is_scalar(x_1130)) {
 x_1131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1131 = x_1130;
}
lean_ctor_set(x_1131, 0, x_1128);
lean_ctor_set(x_1131, 1, x_1129);
return x_1131;
}
}
block_1146:
{
uint8_t x_1135; 
x_1135 = lean_nat_dec_lt(x_1082, x_1133);
if (x_1135 == 0)
{
lean_dec(x_1133);
lean_dec_ref(x_1121);
lean_dec(x_6);
x_1123 = x_1134;
goto block_1132;
}
else
{
uint8_t x_1136; 
x_1136 = lean_nat_dec_le(x_1133, x_1133);
if (x_1136 == 0)
{
lean_dec(x_1133);
lean_dec_ref(x_1121);
lean_dec(x_6);
x_1123 = x_1134;
goto block_1132;
}
else
{
lean_object* x_1137; size_t x_1138; size_t x_1139; lean_object* x_1140; 
x_1137 = lean_box(0);
x_1138 = 0;
x_1139 = lean_usize_of_nat(x_1133);
lean_dec(x_1133);
x_1140 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1121, x_1138, x_1139, x_1137, x_6, x_1134);
lean_dec(x_6);
lean_dec_ref(x_1121);
if (lean_obj_tag(x_1140) == 0)
{
lean_object* x_1141; 
x_1141 = lean_ctor_get(x_1140, 1);
lean_inc(x_1141);
lean_dec_ref(x_1140);
x_1123 = x_1141;
goto block_1132;
}
else
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
lean_dec_ref(x_1122);
lean_dec(x_3);
x_1142 = lean_ctor_get(x_1140, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1140, 1);
lean_inc(x_1143);
if (lean_is_exclusive(x_1140)) {
 lean_ctor_release(x_1140, 0);
 lean_ctor_release(x_1140, 1);
 x_1144 = x_1140;
} else {
 lean_dec_ref(x_1140);
 x_1144 = lean_box(0);
}
if (lean_is_scalar(x_1144)) {
 x_1145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1145 = x_1144;
}
lean_ctor_set(x_1145, 0, x_1142);
lean_ctor_set(x_1145, 1, x_1143);
return x_1145;
}
}
}
}
block_1149:
{
if (x_1147 == 0)
{
lean_inc_ref(x_1122);
lean_inc_ref(x_1121);
lean_dec_ref(x_1092);
lean_dec(x_1090);
lean_dec(x_1088);
lean_dec(x_1086);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec(x_1074);
lean_dec_ref(x_1073);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec_ref(x_1);
x_1134 = x_1148;
goto block_1146;
}
else
{
if (x_54 == 0)
{
lean_dec(x_1133);
lean_dec(x_6);
x_1103 = x_3;
x_1104 = x_1148;
goto block_1117;
}
else
{
lean_inc_ref(x_1122);
lean_inc_ref(x_1121);
lean_dec_ref(x_1092);
lean_dec(x_1090);
lean_dec(x_1088);
lean_dec(x_1086);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec(x_1074);
lean_dec_ref(x_1073);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec_ref(x_1);
x_1134 = x_1148;
goto block_1146;
}
}
}
}
else
{
lean_object* x_1161; lean_object* x_1162; 
lean_inc_ref(x_1120);
lean_dec_ref(x_1092);
lean_dec(x_1090);
lean_dec(x_1088);
lean_dec(x_1086);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec(x_1074);
lean_dec_ref(x_1073);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1161 = lean_ctor_get(x_1120, 0);
lean_inc_ref(x_1161);
lean_dec_ref(x_1120);
if (lean_is_scalar(x_1066)) {
 x_1162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1162 = x_1066;
}
lean_ctor_set(x_1162, 0, x_1161);
lean_ctor_set(x_1162, 1, x_1089);
return x_1162;
}
}
block_1097:
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
if (lean_is_scalar(x_1074)) {
 x_1094 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1094 = x_1074;
}
lean_ctor_set(x_1094, 0, x_1070);
lean_ctor_set(x_1094, 1, x_1092);
lean_ctor_set(x_1094, 2, x_1077);
lean_ctor_set(x_1094, 3, x_1088);
if (lean_is_scalar(x_1078)) {
 x_1095 = lean_alloc_ctor(4, 1, 0);
} else {
 x_1095 = x_1078;
 lean_ctor_set_tag(x_1095, 4);
}
lean_ctor_set(x_1095, 0, x_1094);
if (lean_is_scalar(x_1090)) {
 x_1096 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1096 = x_1090;
}
lean_ctor_set(x_1096, 0, x_1095);
lean_ctor_set(x_1096, 1, x_1093);
return x_1096;
}
block_1102:
{
if (x_1099 == 0)
{
lean_dec(x_1086);
lean_dec(x_1072);
lean_dec_ref(x_1);
x_1093 = x_1098;
goto block_1097;
}
else
{
uint8_t x_1100; 
x_1100 = l_Lean_instBEqFVarId_beq(x_1072, x_1077);
lean_dec(x_1072);
if (x_1100 == 0)
{
lean_dec(x_1086);
lean_dec_ref(x_1);
x_1093 = x_1098;
goto block_1097;
}
else
{
lean_object* x_1101; 
lean_dec_ref(x_1092);
lean_dec(x_1090);
lean_dec(x_1088);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec(x_1074);
lean_dec(x_1070);
if (lean_is_scalar(x_1086)) {
 x_1101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1101 = x_1086;
}
lean_ctor_set(x_1101, 0, x_1);
lean_ctor_set(x_1101, 1, x_1098);
return x_1101;
}
}
}
block_1117:
{
lean_object* x_1105; 
lean_inc(x_1077);
x_1105 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1077, x_1103, x_1104);
lean_dec(x_1103);
if (lean_obj_tag(x_1105) == 0)
{
lean_object* x_1106; size_t x_1107; size_t x_1108; uint8_t x_1109; 
x_1106 = lean_ctor_get(x_1105, 1);
lean_inc(x_1106);
lean_dec_ref(x_1105);
x_1107 = lean_ptr_addr(x_1073);
lean_dec_ref(x_1073);
x_1108 = lean_ptr_addr(x_1088);
x_1109 = lean_usize_dec_eq(x_1107, x_1108);
if (x_1109 == 0)
{
lean_dec_ref(x_1071);
x_1098 = x_1106;
x_1099 = x_1109;
goto block_1102;
}
else
{
size_t x_1110; size_t x_1111; uint8_t x_1112; 
x_1110 = lean_ptr_addr(x_1071);
lean_dec_ref(x_1071);
x_1111 = lean_ptr_addr(x_1092);
x_1112 = lean_usize_dec_eq(x_1110, x_1111);
x_1098 = x_1106;
x_1099 = x_1112;
goto block_1102;
}
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; 
lean_dec_ref(x_1092);
lean_dec(x_1090);
lean_dec(x_1088);
lean_dec(x_1086);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec(x_1074);
lean_dec_ref(x_1073);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec_ref(x_1);
x_1113 = lean_ctor_get(x_1105, 0);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_1105, 1);
lean_inc(x_1114);
if (lean_is_exclusive(x_1105)) {
 lean_ctor_release(x_1105, 0);
 lean_ctor_release(x_1105, 1);
 x_1115 = x_1105;
} else {
 lean_dec_ref(x_1105);
 x_1115 = lean_box(0);
}
if (lean_is_scalar(x_1115)) {
 x_1116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1116 = x_1115;
}
lean_ctor_set(x_1116, 0, x_1113);
lean_ctor_set(x_1116, 1, x_1114);
return x_1116;
}
}
}
else
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; 
lean_dec(x_1086);
lean_dec(x_1080);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec(x_1074);
lean_dec_ref(x_1073);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec(x_1066);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1163 = lean_ctor_get(x_1087, 0);
lean_inc(x_1163);
x_1164 = lean_ctor_get(x_1087, 1);
lean_inc(x_1164);
if (lean_is_exclusive(x_1087)) {
 lean_ctor_release(x_1087, 0);
 lean_ctor_release(x_1087, 1);
 x_1165 = x_1087;
} else {
 lean_dec_ref(x_1087);
 x_1165 = lean_box(0);
}
if (lean_is_scalar(x_1165)) {
 x_1166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1166 = x_1165;
}
lean_ctor_set(x_1166, 0, x_1163);
lean_ctor_set(x_1166, 1, x_1164);
return x_1166;
}
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
lean_dec(x_1080);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec(x_1074);
lean_dec_ref(x_1073);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec(x_1066);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1167 = lean_ctor_get(x_1083, 0);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_1083, 1);
lean_inc(x_1168);
if (lean_is_exclusive(x_1083)) {
 lean_ctor_release(x_1083, 0);
 lean_ctor_release(x_1083, 1);
 x_1169 = x_1083;
} else {
 lean_dec_ref(x_1083);
 x_1169 = lean_box(0);
}
if (lean_is_scalar(x_1169)) {
 x_1170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1170 = x_1169;
}
lean_ctor_set(x_1170, 0, x_1167);
lean_ctor_set(x_1170, 1, x_1168);
return x_1170;
}
}
else
{
lean_object* x_1171; 
lean_dec(x_1074);
lean_dec_ref(x_1073);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec(x_1066);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1171 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_1069);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1171;
}
}
else
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
lean_dec_ref(x_1062);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1172 = lean_ctor_get(x_1063, 1);
lean_inc(x_1172);
if (lean_is_exclusive(x_1063)) {
 lean_ctor_release(x_1063, 0);
 lean_ctor_release(x_1063, 1);
 x_1173 = x_1063;
} else {
 lean_dec_ref(x_1063);
 x_1173 = lean_box(0);
}
x_1174 = lean_ctor_get(x_1064, 0);
lean_inc(x_1174);
lean_dec_ref(x_1064);
if (lean_is_scalar(x_1173)) {
 x_1175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1175 = x_1173;
}
lean_ctor_set(x_1175, 0, x_1174);
lean_ctor_set(x_1175, 1, x_1172);
return x_1175;
}
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
lean_dec_ref(x_1062);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1176 = lean_ctor_get(x_1063, 0);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1063, 1);
lean_inc(x_1177);
if (lean_is_exclusive(x_1063)) {
 lean_ctor_release(x_1063, 0);
 lean_ctor_release(x_1063, 1);
 x_1178 = x_1063;
} else {
 lean_dec_ref(x_1063);
 x_1178 = lean_box(0);
}
if (lean_is_scalar(x_1178)) {
 x_1179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1179 = x_1178;
}
lean_ctor_set(x_1179, 0, x_1176);
lean_ctor_set(x_1179, 1, x_1177);
return x_1179;
}
}
case 5:
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1180 = lean_ctor_get(x_1, 0);
x_1181 = lean_st_ref_get(x_3, x_712);
x_1182 = lean_ctor_get(x_1181, 0);
lean_inc(x_1182);
x_1183 = lean_ctor_get(x_1181, 1);
lean_inc(x_1183);
lean_dec_ref(x_1181);
x_1184 = lean_ctor_get(x_1182, 0);
lean_inc_ref(x_1184);
lean_dec(x_1182);
lean_inc(x_1180);
x_1185 = l_Lean_Compiler_LCNF_normFVarImp(x_1184, x_1180, x_54);
lean_dec_ref(x_1184);
if (lean_obj_tag(x_1185) == 0)
{
lean_object* x_1186; lean_object* x_1187; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1186 = lean_ctor_get(x_1185, 0);
lean_inc(x_1186);
lean_dec_ref(x_1185);
lean_inc(x_1186);
x_1187 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1186, x_3, x_1183);
lean_dec(x_3);
if (lean_obj_tag(x_1187) == 0)
{
lean_object* x_1188; lean_object* x_1189; uint8_t x_1190; 
x_1188 = lean_ctor_get(x_1187, 1);
lean_inc(x_1188);
if (lean_is_exclusive(x_1187)) {
 lean_ctor_release(x_1187, 0);
 lean_ctor_release(x_1187, 1);
 x_1189 = x_1187;
} else {
 lean_dec_ref(x_1187);
 x_1189 = lean_box(0);
}
x_1190 = l_Lean_instBEqFVarId_beq(x_1180, x_1186);
if (x_1190 == 0)
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1191 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1191 = lean_box(0);
}
if (lean_is_scalar(x_1191)) {
 x_1192 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1192 = x_1191;
}
lean_ctor_set(x_1192, 0, x_1186);
if (lean_is_scalar(x_1189)) {
 x_1193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1193 = x_1189;
}
lean_ctor_set(x_1193, 0, x_1192);
lean_ctor_set(x_1193, 1, x_1188);
return x_1193;
}
else
{
lean_object* x_1194; 
lean_dec(x_1186);
if (lean_is_scalar(x_1189)) {
 x_1194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1194 = x_1189;
}
lean_ctor_set(x_1194, 0, x_1);
lean_ctor_set(x_1194, 1, x_1188);
return x_1194;
}
}
else
{
lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
lean_dec(x_1186);
lean_dec_ref(x_1);
x_1195 = lean_ctor_get(x_1187, 0);
lean_inc(x_1195);
x_1196 = lean_ctor_get(x_1187, 1);
lean_inc(x_1196);
if (lean_is_exclusive(x_1187)) {
 lean_ctor_release(x_1187, 0);
 lean_ctor_release(x_1187, 1);
 x_1197 = x_1187;
} else {
 lean_dec_ref(x_1187);
 x_1197 = lean_box(0);
}
if (lean_is_scalar(x_1197)) {
 x_1198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1198 = x_1197;
}
lean_ctor_set(x_1198, 0, x_1195);
lean_ctor_set(x_1198, 1, x_1196);
return x_1198;
}
}
else
{
lean_object* x_1199; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1199 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_1183);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1199;
}
}
case 6:
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; size_t x_1206; size_t x_1207; uint8_t x_1208; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1200 = lean_ctor_get(x_1, 0);
x_1201 = lean_st_ref_get(x_3, x_712);
lean_dec(x_3);
x_1202 = lean_ctor_get(x_1201, 0);
lean_inc(x_1202);
x_1203 = lean_ctor_get(x_1201, 1);
lean_inc(x_1203);
lean_dec_ref(x_1201);
x_1204 = lean_ctor_get(x_1202, 0);
lean_inc_ref(x_1204);
lean_dec(x_1202);
lean_inc_ref(x_1200);
x_1205 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1204, x_54, x_1200);
lean_dec_ref(x_1204);
x_1206 = lean_ptr_addr(x_1200);
x_1207 = lean_ptr_addr(x_1205);
x_1208 = lean_usize_dec_eq(x_1206, x_1207);
if (x_1208 == 0)
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1209 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1209 = lean_box(0);
}
if (lean_is_scalar(x_1209)) {
 x_1210 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1210 = x_1209;
}
lean_ctor_set(x_1210, 0, x_1205);
x_1211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1211, 0, x_1210);
lean_ctor_set(x_1211, 1, x_1203);
return x_1211;
}
else
{
lean_object* x_1212; 
lean_dec_ref(x_1205);
x_1212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1212, 0, x_1);
lean_ctor_set(x_1212, 1, x_1203);
return x_1212;
}
}
default: 
{
lean_object* x_1213; lean_object* x_1214; 
x_1213 = lean_ctor_get(x_1, 0);
x_1214 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1214);
lean_inc_ref(x_1213);
x_713 = x_1213;
x_714 = x_1214;
x_715 = x_2;
x_716 = x_3;
x_717 = x_4;
x_718 = x_5;
x_719 = x_6;
x_720 = x_7;
x_721 = x_8;
goto block_774;
}
}
block_774:
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_722 = lean_ctor_get(x_713, 0);
x_723 = lean_ctor_get(x_713, 2);
x_724 = lean_ctor_get(x_713, 3);
x_725 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_722, x_716, x_712);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; 
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_725, 1);
lean_inc(x_727);
lean_dec_ref(x_725);
lean_inc(x_726);
lean_inc_ref(x_1);
lean_inc_ref(x_714);
x_728 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_728, 0, x_714);
lean_closure_set(x_728, 1, x_1);
lean_closure_set(x_728, 2, x_726);
x_729 = lean_unbox(x_726);
if (x_729 == 0)
{
uint8_t x_730; 
lean_dec(x_726);
lean_dec_ref(x_714);
x_730 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_730 == 0)
{
x_18 = x_728;
x_19 = x_713;
x_20 = x_715;
x_21 = x_716;
x_22 = x_717;
x_23 = x_718;
x_24 = x_719;
x_25 = x_720;
x_26 = x_721;
x_27 = x_727;
goto block_37;
}
else
{
uint8_t x_731; 
lean_inc_ref(x_724);
x_731 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_724, x_723);
if (x_731 == 0)
{
x_18 = x_728;
x_19 = x_713;
x_20 = x_715;
x_21 = x_716;
x_22 = x_717;
x_23 = x_718;
x_24 = x_719;
x_25 = x_720;
x_26 = x_721;
x_27 = x_727;
goto block_37;
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_732 = lean_st_ref_get(x_716, x_727);
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec_ref(x_732);
x_735 = lean_ctor_get(x_733, 0);
lean_inc_ref(x_735);
lean_dec(x_733);
x_736 = l_Lean_Compiler_LCNF_normFunDeclImp(x_54, x_713, x_735, x_718, x_719, x_720, x_721, x_734);
lean_dec_ref(x_735);
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_736, 1);
lean_inc(x_738);
lean_dec_ref(x_736);
lean_inc(x_721);
lean_inc_ref(x_720);
lean_inc(x_719);
lean_inc_ref(x_718);
x_739 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_737, x_718, x_719, x_720, x_721, x_738);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_739, 1);
lean_inc(x_741);
lean_dec_ref(x_739);
x_742 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_716, x_741);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; 
x_743 = lean_ctor_get(x_742, 1);
lean_inc(x_743);
lean_dec_ref(x_742);
x_18 = x_728;
x_19 = x_740;
x_20 = x_715;
x_21 = x_716;
x_22 = x_717;
x_23 = x_718;
x_24 = x_719;
x_25 = x_720;
x_26 = x_721;
x_27 = x_743;
goto block_37;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
lean_dec(x_740);
lean_dec_ref(x_728);
lean_dec(x_721);
lean_dec_ref(x_720);
lean_dec(x_719);
lean_dec_ref(x_718);
lean_dec_ref(x_717);
lean_dec(x_716);
lean_dec_ref(x_715);
x_744 = lean_ctor_get(x_742, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_742, 1);
lean_inc(x_745);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_746 = x_742;
} else {
 lean_dec_ref(x_742);
 x_746 = lean_box(0);
}
if (lean_is_scalar(x_746)) {
 x_747 = lean_alloc_ctor(1, 2, 0);
} else {
 x_747 = x_746;
}
lean_ctor_set(x_747, 0, x_744);
lean_ctor_set(x_747, 1, x_745);
return x_747;
}
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_dec_ref(x_728);
lean_dec(x_721);
lean_dec_ref(x_720);
lean_dec(x_719);
lean_dec_ref(x_718);
lean_dec_ref(x_717);
lean_dec(x_716);
lean_dec_ref(x_715);
x_748 = lean_ctor_get(x_739, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_739, 1);
lean_inc(x_749);
if (lean_is_exclusive(x_739)) {
 lean_ctor_release(x_739, 0);
 lean_ctor_release(x_739, 1);
 x_750 = x_739;
} else {
 lean_dec_ref(x_739);
 x_750 = lean_box(0);
}
if (lean_is_scalar(x_750)) {
 x_751 = lean_alloc_ctor(1, 2, 0);
} else {
 x_751 = x_750;
}
lean_ctor_set(x_751, 0, x_748);
lean_ctor_set(x_751, 1, x_749);
return x_751;
}
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
lean_dec_ref(x_728);
lean_dec(x_721);
lean_dec_ref(x_720);
lean_dec(x_719);
lean_dec_ref(x_718);
lean_dec_ref(x_717);
lean_dec(x_716);
lean_dec_ref(x_715);
x_752 = lean_ctor_get(x_736, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_736, 1);
lean_inc(x_753);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_754 = x_736;
} else {
 lean_dec_ref(x_736);
 x_754 = lean_box(0);
}
if (lean_is_scalar(x_754)) {
 x_755 = lean_alloc_ctor(1, 2, 0);
} else {
 x_755 = x_754;
}
lean_ctor_set(x_755, 0, x_752);
lean_ctor_set(x_755, 1, x_753);
return x_755;
}
}
}
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec_ref(x_728);
x_756 = lean_st_ref_get(x_716, x_727);
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_756, 1);
lean_inc(x_758);
lean_dec_ref(x_756);
x_759 = lean_ctor_get(x_757, 0);
lean_inc_ref(x_759);
lean_dec(x_757);
x_760 = l_Lean_Compiler_LCNF_normFunDeclImp(x_54, x_713, x_759, x_718, x_719, x_720, x_721, x_758);
lean_dec_ref(x_759);
if (lean_obj_tag(x_760) == 0)
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; uint8_t x_764; lean_object* x_765; 
x_761 = lean_ctor_get(x_760, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_760, 1);
lean_inc(x_762);
lean_dec_ref(x_760);
x_763 = lean_box(0);
x_764 = lean_unbox(x_726);
lean_dec(x_726);
x_765 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_714, x_1, x_764, x_761, x_763, x_715, x_716, x_717, x_718, x_719, x_720, x_721, x_762);
return x_765;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_726);
lean_dec(x_721);
lean_dec_ref(x_720);
lean_dec(x_719);
lean_dec_ref(x_718);
lean_dec_ref(x_717);
lean_dec(x_716);
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec_ref(x_1);
x_766 = lean_ctor_get(x_760, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_760, 1);
lean_inc(x_767);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 lean_ctor_release(x_760, 1);
 x_768 = x_760;
} else {
 lean_dec_ref(x_760);
 x_768 = lean_box(0);
}
if (lean_is_scalar(x_768)) {
 x_769 = lean_alloc_ctor(1, 2, 0);
} else {
 x_769 = x_768;
}
lean_ctor_set(x_769, 0, x_766);
lean_ctor_set(x_769, 1, x_767);
return x_769;
}
}
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_dec(x_721);
lean_dec_ref(x_720);
lean_dec(x_719);
lean_dec_ref(x_718);
lean_dec_ref(x_717);
lean_dec(x_716);
lean_dec_ref(x_715);
lean_dec_ref(x_714);
lean_dec_ref(x_713);
lean_dec_ref(x_1);
x_770 = lean_ctor_get(x_725, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_725, 1);
lean_inc(x_771);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_772 = x_725;
} else {
 lean_dec_ref(x_725);
 x_772 = lean_box(0);
}
if (lean_is_scalar(x_772)) {
 x_773 = lean_alloc_ctor(1, 2, 0);
} else {
 x_773 = x_772;
}
lean_ctor_set(x_773, 0, x_770);
lean_ctor_set(x_773, 1, x_771);
return x_773;
}
}
}
}
else
{
uint8_t x_1215; 
lean_free_object(x_7);
lean_dec_ref(x_53);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1215 = !lean_is_exclusive(x_70);
if (x_1215 == 0)
{
return x_70;
}
else
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
x_1216 = lean_ctor_get(x_70, 0);
x_1217 = lean_ctor_get(x_70, 1);
lean_inc(x_1217);
lean_inc(x_1216);
lean_dec(x_70);
x_1218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1218, 0, x_1216);
lean_ctor_set(x_1218, 1, x_1217);
return x_1218;
}
}
}
else
{
lean_object* x_1219; 
lean_dec(x_7);
x_1219 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
if (lean_obj_tag(x_1219) == 0)
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; 
x_1220 = lean_ctor_get(x_1219, 1);
lean_inc(x_1220);
if (lean_is_exclusive(x_1219)) {
 lean_ctor_release(x_1219, 0);
 lean_ctor_release(x_1219, 1);
 x_1221 = x_1219;
} else {
 lean_dec_ref(x_1219);
 x_1221 = lean_box(0);
}
x_1284 = lean_unsigned_to_nat(1u);
x_1285 = lean_nat_add(x_41, x_1284);
lean_dec(x_41);
x_1286 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_1286, 0, x_38);
lean_ctor_set(x_1286, 1, x_39);
lean_ctor_set(x_1286, 2, x_40);
lean_ctor_set(x_1286, 3, x_1285);
lean_ctor_set(x_1286, 4, x_42);
lean_ctor_set(x_1286, 5, x_43);
lean_ctor_set(x_1286, 6, x_44);
lean_ctor_set(x_1286, 7, x_45);
lean_ctor_set(x_1286, 8, x_46);
lean_ctor_set(x_1286, 9, x_47);
lean_ctor_set(x_1286, 10, x_48);
lean_ctor_set(x_1286, 11, x_49);
lean_ctor_set(x_1286, 12, x_51);
lean_ctor_set(x_1286, 13, x_53);
lean_ctor_set_uint8(x_1286, sizeof(void*)*14, x_50);
lean_ctor_set_uint8(x_1286, sizeof(void*)*14 + 1, x_52);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; uint8_t x_1298; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1467; 
lean_dec(x_1221);
x_1287 = lean_ctor_get(x_1, 0);
x_1288 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1287);
x_1467 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_54, x_1287, x_3, x_6, x_1220);
if (lean_obj_tag(x_1467) == 0)
{
lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; uint8_t x_1512; 
x_1468 = lean_ctor_get(x_1467, 0);
lean_inc(x_1468);
x_1469 = lean_ctor_get(x_1467, 1);
lean_inc(x_1469);
lean_dec_ref(x_1467);
x_1512 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_1287, x_1468);
if (x_1512 == 0)
{
goto block_1511;
}
else
{
if (x_54 == 0)
{
x_1470 = x_2;
x_1471 = x_3;
x_1472 = x_4;
x_1473 = x_5;
x_1474 = x_6;
x_1475 = x_1286;
x_1476 = x_8;
x_1477 = x_1469;
goto block_1504;
}
else
{
goto block_1511;
}
}
block_1504:
{
lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; 
x_1478 = lean_ctor_get(x_1468, 2);
x_1479 = lean_ctor_get(x_1468, 3);
lean_inc(x_1476);
lean_inc_ref(x_1475);
lean_inc(x_1474);
lean_inc_ref(x_1473);
lean_inc_ref(x_1472);
lean_inc(x_1479);
x_1480 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_1479, x_1470, x_1472, x_1473, x_1474, x_1475, x_1476, x_1477);
if (lean_obj_tag(x_1480) == 0)
{
lean_object* x_1481; 
x_1481 = lean_ctor_get(x_1480, 0);
lean_inc(x_1481);
if (lean_obj_tag(x_1481) == 0)
{
lean_object* x_1482; 
lean_inc(x_1479);
lean_inc_ref(x_1478);
x_1482 = lean_ctor_get(x_1480, 1);
lean_inc(x_1482);
lean_dec_ref(x_1480);
x_1452 = x_1468;
x_1453 = x_1478;
x_1454 = x_1479;
x_1455 = x_1470;
x_1456 = x_1471;
x_1457 = x_1472;
x_1458 = x_1473;
x_1459 = x_1474;
x_1460 = x_1475;
x_1461 = x_1476;
x_1462 = x_1482;
goto block_1466;
}
else
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; 
x_1483 = lean_ctor_get(x_1480, 1);
lean_inc(x_1483);
lean_dec_ref(x_1480);
x_1484 = lean_ctor_get(x_1481, 0);
lean_inc(x_1484);
lean_dec_ref(x_1481);
x_1485 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1471, x_1483);
if (lean_obj_tag(x_1485) == 0)
{
lean_object* x_1486; lean_object* x_1487; 
x_1486 = lean_ctor_get(x_1485, 1);
lean_inc(x_1486);
lean_dec_ref(x_1485);
x_1487 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_1468, x_1484, x_1474, x_1486);
if (lean_obj_tag(x_1487) == 0)
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
x_1488 = lean_ctor_get(x_1487, 0);
lean_inc(x_1488);
x_1489 = lean_ctor_get(x_1487, 1);
lean_inc(x_1489);
lean_dec_ref(x_1487);
x_1490 = lean_ctor_get(x_1488, 2);
lean_inc_ref(x_1490);
x_1491 = lean_ctor_get(x_1488, 3);
lean_inc(x_1491);
x_1452 = x_1488;
x_1453 = x_1490;
x_1454 = x_1491;
x_1455 = x_1470;
x_1456 = x_1471;
x_1457 = x_1472;
x_1458 = x_1473;
x_1459 = x_1474;
x_1460 = x_1475;
x_1461 = x_1476;
x_1462 = x_1489;
goto block_1466;
}
else
{
lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; 
lean_dec(x_1476);
lean_dec_ref(x_1475);
lean_dec(x_1474);
lean_dec_ref(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec_ref(x_1);
x_1492 = lean_ctor_get(x_1487, 0);
lean_inc(x_1492);
x_1493 = lean_ctor_get(x_1487, 1);
lean_inc(x_1493);
if (lean_is_exclusive(x_1487)) {
 lean_ctor_release(x_1487, 0);
 lean_ctor_release(x_1487, 1);
 x_1494 = x_1487;
} else {
 lean_dec_ref(x_1487);
 x_1494 = lean_box(0);
}
if (lean_is_scalar(x_1494)) {
 x_1495 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1495 = x_1494;
}
lean_ctor_set(x_1495, 0, x_1492);
lean_ctor_set(x_1495, 1, x_1493);
return x_1495;
}
}
else
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
lean_dec(x_1484);
lean_dec(x_1476);
lean_dec_ref(x_1475);
lean_dec(x_1474);
lean_dec_ref(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1468);
lean_dec_ref(x_1);
x_1496 = lean_ctor_get(x_1485, 0);
lean_inc(x_1496);
x_1497 = lean_ctor_get(x_1485, 1);
lean_inc(x_1497);
if (lean_is_exclusive(x_1485)) {
 lean_ctor_release(x_1485, 0);
 lean_ctor_release(x_1485, 1);
 x_1498 = x_1485;
} else {
 lean_dec_ref(x_1485);
 x_1498 = lean_box(0);
}
if (lean_is_scalar(x_1498)) {
 x_1499 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1499 = x_1498;
}
lean_ctor_set(x_1499, 0, x_1496);
lean_ctor_set(x_1499, 1, x_1497);
return x_1499;
}
}
}
else
{
lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; 
lean_dec(x_1476);
lean_dec_ref(x_1475);
lean_dec(x_1474);
lean_dec_ref(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1468);
lean_dec_ref(x_1);
x_1500 = lean_ctor_get(x_1480, 0);
lean_inc(x_1500);
x_1501 = lean_ctor_get(x_1480, 1);
lean_inc(x_1501);
if (lean_is_exclusive(x_1480)) {
 lean_ctor_release(x_1480, 0);
 lean_ctor_release(x_1480, 1);
 x_1502 = x_1480;
} else {
 lean_dec_ref(x_1480);
 x_1502 = lean_box(0);
}
if (lean_is_scalar(x_1502)) {
 x_1503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1503 = x_1502;
}
lean_ctor_set(x_1503, 0, x_1500);
lean_ctor_set(x_1503, 1, x_1501);
return x_1503;
}
}
block_1511:
{
lean_object* x_1505; 
x_1505 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_1469);
if (lean_obj_tag(x_1505) == 0)
{
lean_object* x_1506; 
x_1506 = lean_ctor_get(x_1505, 1);
lean_inc(x_1506);
lean_dec_ref(x_1505);
x_1470 = x_2;
x_1471 = x_3;
x_1472 = x_4;
x_1473 = x_5;
x_1474 = x_6;
x_1475 = x_1286;
x_1476 = x_8;
x_1477 = x_1506;
goto block_1504;
}
else
{
lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; 
lean_dec(x_1468);
lean_dec_ref(x_1286);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1507 = lean_ctor_get(x_1505, 0);
lean_inc(x_1507);
x_1508 = lean_ctor_get(x_1505, 1);
lean_inc(x_1508);
if (lean_is_exclusive(x_1505)) {
 lean_ctor_release(x_1505, 0);
 lean_ctor_release(x_1505, 1);
 x_1509 = x_1505;
} else {
 lean_dec_ref(x_1505);
 x_1509 = lean_box(0);
}
if (lean_is_scalar(x_1509)) {
 x_1510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1510 = x_1509;
}
lean_ctor_set(x_1510, 0, x_1507);
lean_ctor_set(x_1510, 1, x_1508);
return x_1510;
}
}
}
else
{
lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; 
lean_dec_ref(x_1286);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1513 = lean_ctor_get(x_1467, 0);
lean_inc(x_1513);
x_1514 = lean_ctor_get(x_1467, 1);
lean_inc(x_1514);
if (lean_is_exclusive(x_1467)) {
 lean_ctor_release(x_1467, 0);
 lean_ctor_release(x_1467, 1);
 x_1515 = x_1467;
} else {
 lean_dec_ref(x_1467);
 x_1515 = lean_box(0);
}
if (lean_is_scalar(x_1515)) {
 x_1516 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1516 = x_1515;
}
lean_ctor_set(x_1516, 0, x_1513);
lean_ctor_set(x_1516, 1, x_1514);
return x_1516;
}
block_1451:
{
if (x_1298 == 0)
{
lean_object* x_1299; 
lean_inc(x_1289);
lean_inc_ref(x_1297);
lean_inc(x_1291);
lean_inc_ref(x_1293);
lean_inc_ref(x_1290);
x_1299 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_1290, x_1293, x_1291, x_1297, x_1289, x_1292);
if (lean_obj_tag(x_1299) == 0)
{
lean_object* x_1300; 
x_1300 = lean_ctor_get(x_1299, 0);
lean_inc(x_1300);
if (lean_obj_tag(x_1300) == 0)
{
lean_object* x_1301; lean_object* x_1302; 
x_1301 = lean_ctor_get(x_1299, 1);
lean_inc(x_1301);
lean_dec_ref(x_1299);
lean_inc(x_1289);
lean_inc_ref(x_1297);
lean_inc(x_1291);
lean_inc_ref(x_1293);
lean_inc_ref(x_1290);
x_1302 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1290, x_1296, x_1295, x_1293, x_1291, x_1297, x_1289, x_1301);
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; 
x_1303 = lean_ctor_get(x_1302, 0);
lean_inc(x_1303);
if (lean_obj_tag(x_1303) == 0)
{
lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; 
x_1304 = lean_ctor_get(x_1302, 1);
lean_inc(x_1304);
lean_dec_ref(x_1302);
x_1305 = lean_ctor_get(x_1290, 0);
x_1306 = lean_ctor_get(x_1290, 3);
lean_inc(x_1306);
x_1307 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1306, x_1304);
x_1308 = lean_ctor_get(x_1307, 0);
lean_inc(x_1308);
if (lean_obj_tag(x_1308) == 0)
{
lean_object* x_1309; lean_object* x_1310; 
x_1309 = lean_ctor_get(x_1307, 1);
lean_inc(x_1309);
lean_dec_ref(x_1307);
lean_inc(x_1289);
lean_inc_ref(x_1297);
lean_inc(x_1291);
lean_inc_ref(x_1293);
lean_inc_ref(x_1294);
lean_inc(x_1295);
lean_inc_ref(x_1296);
lean_inc_ref(x_1288);
lean_inc_ref(x_1290);
x_1310 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1290, x_1288, x_1296, x_1295, x_1294, x_1293, x_1291, x_1297, x_1289, x_1309);
if (lean_obj_tag(x_1310) == 0)
{
lean_object* x_1311; 
x_1311 = lean_ctor_get(x_1310, 0);
lean_inc(x_1311);
if (lean_obj_tag(x_1311) == 0)
{
lean_object* x_1312; lean_object* x_1313; 
x_1312 = lean_ctor_get(x_1310, 1);
lean_inc(x_1312);
lean_dec_ref(x_1310);
lean_inc(x_1289);
lean_inc_ref(x_1297);
lean_inc(x_1291);
lean_inc_ref(x_1293);
lean_inc_ref(x_1294);
lean_inc(x_1295);
lean_inc_ref(x_1296);
lean_inc(x_1306);
x_1313 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_1306, x_1296, x_1295, x_1294, x_1293, x_1291, x_1297, x_1289, x_1312);
if (lean_obj_tag(x_1313) == 0)
{
lean_object* x_1314; 
x_1314 = lean_ctor_get(x_1313, 0);
lean_inc(x_1314);
if (lean_obj_tag(x_1314) == 0)
{
lean_object* x_1315; lean_object* x_1316; 
x_1315 = lean_ctor_get(x_1313, 1);
lean_inc(x_1315);
lean_dec_ref(x_1313);
lean_inc(x_1289);
lean_inc_ref(x_1297);
lean_inc(x_1291);
lean_inc_ref(x_1293);
lean_inc_ref(x_1294);
lean_inc(x_1295);
lean_inc_ref(x_1296);
lean_inc_ref(x_1288);
x_1316 = l_Lean_Compiler_LCNF_Simp_simp(x_1288, x_1296, x_1295, x_1294, x_1293, x_1291, x_1297, x_1289, x_1315);
if (lean_obj_tag(x_1316) == 0)
{
lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; 
x_1317 = lean_ctor_get(x_1316, 0);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1316, 1);
lean_inc(x_1318);
lean_dec_ref(x_1316);
x_1319 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_1305, x_1295, x_1318);
if (lean_obj_tag(x_1319) == 0)
{
lean_object* x_1320; uint8_t x_1321; 
x_1320 = lean_ctor_get(x_1319, 0);
lean_inc(x_1320);
x_1321 = lean_unbox(x_1320);
lean_dec(x_1320);
if (x_1321 == 0)
{
lean_object* x_1322; lean_object* x_1323; 
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1289);
lean_dec_ref(x_1);
x_1322 = lean_ctor_get(x_1319, 1);
lean_inc(x_1322);
lean_dec_ref(x_1319);
x_1323 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1290, x_1295, x_1291, x_1322);
lean_dec(x_1291);
lean_dec(x_1295);
lean_dec_ref(x_1290);
if (lean_obj_tag(x_1323) == 0)
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
x_1324 = lean_ctor_get(x_1323, 1);
lean_inc(x_1324);
if (lean_is_exclusive(x_1323)) {
 lean_ctor_release(x_1323, 0);
 lean_ctor_release(x_1323, 1);
 x_1325 = x_1323;
} else {
 lean_dec_ref(x_1323);
 x_1325 = lean_box(0);
}
if (lean_is_scalar(x_1325)) {
 x_1326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1326 = x_1325;
}
lean_ctor_set(x_1326, 0, x_1317);
lean_ctor_set(x_1326, 1, x_1324);
return x_1326;
}
else
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; 
lean_dec(x_1317);
x_1327 = lean_ctor_get(x_1323, 0);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_1323, 1);
lean_inc(x_1328);
if (lean_is_exclusive(x_1323)) {
 lean_ctor_release(x_1323, 0);
 lean_ctor_release(x_1323, 1);
 x_1329 = x_1323;
} else {
 lean_dec_ref(x_1323);
 x_1329 = lean_box(0);
}
if (lean_is_scalar(x_1329)) {
 x_1330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1330 = x_1329;
}
lean_ctor_set(x_1330, 0, x_1327);
lean_ctor_set(x_1330, 1, x_1328);
return x_1330;
}
}
else
{
lean_object* x_1331; lean_object* x_1332; 
x_1331 = lean_ctor_get(x_1319, 1);
lean_inc(x_1331);
lean_dec_ref(x_1319);
lean_inc_ref(x_1290);
x_1332 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_1290, x_1296, x_1295, x_1294, x_1293, x_1291, x_1297, x_1289, x_1331);
lean_dec(x_1289);
lean_dec_ref(x_1297);
lean_dec(x_1291);
lean_dec_ref(x_1293);
lean_dec_ref(x_1294);
lean_dec(x_1295);
lean_dec_ref(x_1296);
if (lean_obj_tag(x_1332) == 0)
{
lean_object* x_1333; size_t x_1334; size_t x_1335; uint8_t x_1336; 
x_1333 = lean_ctor_get(x_1332, 1);
lean_inc(x_1333);
lean_dec_ref(x_1332);
x_1334 = lean_ptr_addr(x_1288);
x_1335 = lean_ptr_addr(x_1317);
x_1336 = lean_usize_dec_eq(x_1334, x_1335);
if (x_1336 == 0)
{
x_10 = x_1290;
x_11 = x_1333;
x_12 = x_1317;
x_13 = x_1336;
goto block_17;
}
else
{
size_t x_1337; size_t x_1338; uint8_t x_1339; 
x_1337 = lean_ptr_addr(x_1287);
x_1338 = lean_ptr_addr(x_1290);
x_1339 = lean_usize_dec_eq(x_1337, x_1338);
x_10 = x_1290;
x_11 = x_1333;
x_12 = x_1317;
x_13 = x_1339;
goto block_17;
}
}
else
{
lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; 
lean_dec(x_1317);
lean_dec_ref(x_1290);
lean_dec_ref(x_1);
x_1340 = lean_ctor_get(x_1332, 0);
lean_inc(x_1340);
x_1341 = lean_ctor_get(x_1332, 1);
lean_inc(x_1341);
if (lean_is_exclusive(x_1332)) {
 lean_ctor_release(x_1332, 0);
 lean_ctor_release(x_1332, 1);
 x_1342 = x_1332;
} else {
 lean_dec_ref(x_1332);
 x_1342 = lean_box(0);
}
if (lean_is_scalar(x_1342)) {
 x_1343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1343 = x_1342;
}
lean_ctor_set(x_1343, 0, x_1340);
lean_ctor_set(x_1343, 1, x_1341);
return x_1343;
}
}
}
else
{
lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; 
lean_dec(x_1317);
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec_ref(x_1290);
lean_dec(x_1289);
lean_dec_ref(x_1);
x_1344 = lean_ctor_get(x_1319, 0);
lean_inc(x_1344);
x_1345 = lean_ctor_get(x_1319, 1);
lean_inc(x_1345);
if (lean_is_exclusive(x_1319)) {
 lean_ctor_release(x_1319, 0);
 lean_ctor_release(x_1319, 1);
 x_1346 = x_1319;
} else {
 lean_dec_ref(x_1319);
 x_1346 = lean_box(0);
}
if (lean_is_scalar(x_1346)) {
 x_1347 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1347 = x_1346;
}
lean_ctor_set(x_1347, 0, x_1344);
lean_ctor_set(x_1347, 1, x_1345);
return x_1347;
}
}
else
{
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec_ref(x_1290);
lean_dec(x_1289);
lean_dec_ref(x_1);
return x_1316;
}
}
else
{
lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
lean_inc_ref(x_1288);
lean_dec_ref(x_1);
x_1348 = lean_ctor_get(x_1314, 0);
lean_inc(x_1348);
lean_dec_ref(x_1314);
x_1349 = lean_ctor_get(x_1313, 1);
lean_inc(x_1349);
lean_dec_ref(x_1313);
x_1350 = lean_ctor_get(x_1348, 0);
lean_inc(x_1350);
x_1351 = lean_ctor_get(x_1348, 1);
lean_inc(x_1351);
lean_dec(x_1348);
lean_inc(x_1305);
x_1352 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1305, x_1351, x_1295, x_1291, x_1297, x_1289, x_1349);
if (lean_obj_tag(x_1352) == 0)
{
lean_object* x_1353; lean_object* x_1354; 
x_1353 = lean_ctor_get(x_1352, 1);
lean_inc(x_1353);
lean_dec_ref(x_1352);
x_1354 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1290, x_1295, x_1291, x_1353);
lean_dec_ref(x_1290);
if (lean_obj_tag(x_1354) == 0)
{
lean_object* x_1355; lean_object* x_1356; 
x_1355 = lean_ctor_get(x_1354, 1);
lean_inc(x_1355);
lean_dec_ref(x_1354);
lean_inc(x_1289);
lean_inc_ref(x_1297);
lean_inc(x_1291);
lean_inc_ref(x_1293);
lean_inc_ref(x_1294);
lean_inc(x_1295);
lean_inc_ref(x_1296);
x_1356 = l_Lean_Compiler_LCNF_Simp_simp(x_1288, x_1296, x_1295, x_1294, x_1293, x_1291, x_1297, x_1289, x_1355);
if (lean_obj_tag(x_1356) == 0)
{
lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; 
x_1357 = lean_ctor_get(x_1356, 0);
lean_inc(x_1357);
x_1358 = lean_ctor_get(x_1356, 1);
lean_inc(x_1358);
lean_dec_ref(x_1356);
x_1359 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1350, x_1357, x_1296, x_1295, x_1294, x_1293, x_1291, x_1297, x_1289, x_1358);
lean_dec(x_1289);
lean_dec_ref(x_1297);
lean_dec(x_1291);
lean_dec_ref(x_1293);
lean_dec_ref(x_1294);
lean_dec(x_1295);
lean_dec_ref(x_1296);
lean_dec(x_1350);
return x_1359;
}
else
{
lean_dec(x_1350);
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec(x_1289);
return x_1356;
}
}
else
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
lean_dec(x_1350);
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec(x_1289);
lean_dec_ref(x_1288);
x_1360 = lean_ctor_get(x_1354, 0);
lean_inc(x_1360);
x_1361 = lean_ctor_get(x_1354, 1);
lean_inc(x_1361);
if (lean_is_exclusive(x_1354)) {
 lean_ctor_release(x_1354, 0);
 lean_ctor_release(x_1354, 1);
 x_1362 = x_1354;
} else {
 lean_dec_ref(x_1354);
 x_1362 = lean_box(0);
}
if (lean_is_scalar(x_1362)) {
 x_1363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1363 = x_1362;
}
lean_ctor_set(x_1363, 0, x_1360);
lean_ctor_set(x_1363, 1, x_1361);
return x_1363;
}
}
else
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; 
lean_dec(x_1350);
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec_ref(x_1290);
lean_dec(x_1289);
lean_dec_ref(x_1288);
x_1364 = lean_ctor_get(x_1352, 0);
lean_inc(x_1364);
x_1365 = lean_ctor_get(x_1352, 1);
lean_inc(x_1365);
if (lean_is_exclusive(x_1352)) {
 lean_ctor_release(x_1352, 0);
 lean_ctor_release(x_1352, 1);
 x_1366 = x_1352;
} else {
 lean_dec_ref(x_1352);
 x_1366 = lean_box(0);
}
if (lean_is_scalar(x_1366)) {
 x_1367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1367 = x_1366;
}
lean_ctor_set(x_1367, 0, x_1364);
lean_ctor_set(x_1367, 1, x_1365);
return x_1367;
}
}
}
else
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec_ref(x_1290);
lean_dec(x_1289);
lean_dec_ref(x_1);
x_1368 = lean_ctor_get(x_1313, 0);
lean_inc(x_1368);
x_1369 = lean_ctor_get(x_1313, 1);
lean_inc(x_1369);
if (lean_is_exclusive(x_1313)) {
 lean_ctor_release(x_1313, 0);
 lean_ctor_release(x_1313, 1);
 x_1370 = x_1313;
} else {
 lean_dec_ref(x_1313);
 x_1370 = lean_box(0);
}
if (lean_is_scalar(x_1370)) {
 x_1371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1371 = x_1370;
}
lean_ctor_set(x_1371, 0, x_1368);
lean_ctor_set(x_1371, 1, x_1369);
return x_1371;
}
}
else
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1289);
lean_dec_ref(x_1);
x_1372 = lean_ctor_get(x_1310, 1);
lean_inc(x_1372);
lean_dec_ref(x_1310);
x_1373 = lean_ctor_get(x_1311, 0);
lean_inc(x_1373);
lean_dec_ref(x_1311);
x_1374 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1290, x_1295, x_1291, x_1372);
lean_dec(x_1291);
lean_dec(x_1295);
lean_dec_ref(x_1290);
if (lean_obj_tag(x_1374) == 0)
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1375 = lean_ctor_get(x_1374, 1);
lean_inc(x_1375);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 lean_ctor_release(x_1374, 1);
 x_1376 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1376 = lean_box(0);
}
if (lean_is_scalar(x_1376)) {
 x_1377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1377 = x_1376;
}
lean_ctor_set(x_1377, 0, x_1373);
lean_ctor_set(x_1377, 1, x_1375);
return x_1377;
}
else
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
lean_dec(x_1373);
x_1378 = lean_ctor_get(x_1374, 0);
lean_inc(x_1378);
x_1379 = lean_ctor_get(x_1374, 1);
lean_inc(x_1379);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 lean_ctor_release(x_1374, 1);
 x_1380 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1380 = lean_box(0);
}
if (lean_is_scalar(x_1380)) {
 x_1381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1381 = x_1380;
}
lean_ctor_set(x_1381, 0, x_1378);
lean_ctor_set(x_1381, 1, x_1379);
return x_1381;
}
}
}
else
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; 
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec_ref(x_1290);
lean_dec(x_1289);
lean_dec_ref(x_1);
x_1382 = lean_ctor_get(x_1310, 0);
lean_inc(x_1382);
x_1383 = lean_ctor_get(x_1310, 1);
lean_inc(x_1383);
if (lean_is_exclusive(x_1310)) {
 lean_ctor_release(x_1310, 0);
 lean_ctor_release(x_1310, 1);
 x_1384 = x_1310;
} else {
 lean_dec_ref(x_1310);
 x_1384 = lean_box(0);
}
if (lean_is_scalar(x_1384)) {
 x_1385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1385 = x_1384;
}
lean_ctor_set(x_1385, 0, x_1382);
lean_ctor_set(x_1385, 1, x_1383);
return x_1385;
}
}
else
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; 
lean_inc_ref(x_1288);
lean_dec_ref(x_1);
x_1386 = lean_ctor_get(x_1307, 1);
lean_inc(x_1386);
lean_dec_ref(x_1307);
x_1387 = lean_ctor_get(x_1308, 0);
lean_inc(x_1387);
lean_dec_ref(x_1308);
lean_inc(x_1305);
x_1388 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1305, x_1387, x_1295, x_1291, x_1297, x_1289, x_1386);
if (lean_obj_tag(x_1388) == 0)
{
lean_object* x_1389; lean_object* x_1390; 
x_1389 = lean_ctor_get(x_1388, 1);
lean_inc(x_1389);
lean_dec_ref(x_1388);
x_1390 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1290, x_1295, x_1291, x_1389);
lean_dec_ref(x_1290);
if (lean_obj_tag(x_1390) == 0)
{
lean_object* x_1391; 
x_1391 = lean_ctor_get(x_1390, 1);
lean_inc(x_1391);
lean_dec_ref(x_1390);
x_1 = x_1288;
x_2 = x_1296;
x_3 = x_1295;
x_4 = x_1294;
x_5 = x_1293;
x_6 = x_1291;
x_7 = x_1297;
x_8 = x_1289;
x_9 = x_1391;
goto _start;
}
else
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; 
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec(x_1289);
lean_dec_ref(x_1288);
x_1393 = lean_ctor_get(x_1390, 0);
lean_inc(x_1393);
x_1394 = lean_ctor_get(x_1390, 1);
lean_inc(x_1394);
if (lean_is_exclusive(x_1390)) {
 lean_ctor_release(x_1390, 0);
 lean_ctor_release(x_1390, 1);
 x_1395 = x_1390;
} else {
 lean_dec_ref(x_1390);
 x_1395 = lean_box(0);
}
if (lean_is_scalar(x_1395)) {
 x_1396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1396 = x_1395;
}
lean_ctor_set(x_1396, 0, x_1393);
lean_ctor_set(x_1396, 1, x_1394);
return x_1396;
}
}
else
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec_ref(x_1290);
lean_dec(x_1289);
lean_dec_ref(x_1288);
x_1397 = lean_ctor_get(x_1388, 0);
lean_inc(x_1397);
x_1398 = lean_ctor_get(x_1388, 1);
lean_inc(x_1398);
if (lean_is_exclusive(x_1388)) {
 lean_ctor_release(x_1388, 0);
 lean_ctor_release(x_1388, 1);
 x_1399 = x_1388;
} else {
 lean_dec_ref(x_1388);
 x_1399 = lean_box(0);
}
if (lean_is_scalar(x_1399)) {
 x_1400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1400 = x_1399;
}
lean_ctor_set(x_1400, 0, x_1397);
lean_ctor_set(x_1400, 1, x_1398);
return x_1400;
}
}
}
else
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; 
lean_dec_ref(x_1290);
lean_inc_ref(x_1288);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1401 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1401 = lean_box(0);
}
x_1402 = lean_ctor_get(x_1302, 1);
lean_inc(x_1402);
lean_dec_ref(x_1302);
x_1403 = lean_ctor_get(x_1303, 0);
lean_inc(x_1403);
lean_dec_ref(x_1303);
if (lean_is_scalar(x_1401)) {
 x_1404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1404 = x_1401;
 lean_ctor_set_tag(x_1404, 1);
}
lean_ctor_set(x_1404, 0, x_1403);
lean_ctor_set(x_1404, 1, x_1288);
x_1 = x_1404;
x_2 = x_1296;
x_3 = x_1295;
x_4 = x_1294;
x_5 = x_1293;
x_6 = x_1291;
x_7 = x_1297;
x_8 = x_1289;
x_9 = x_1402;
goto _start;
}
}
else
{
lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; 
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec_ref(x_1290);
lean_dec(x_1289);
lean_dec_ref(x_1);
x_1406 = lean_ctor_get(x_1302, 0);
lean_inc(x_1406);
x_1407 = lean_ctor_get(x_1302, 1);
lean_inc(x_1407);
if (lean_is_exclusive(x_1302)) {
 lean_ctor_release(x_1302, 0);
 lean_ctor_release(x_1302, 1);
 x_1408 = x_1302;
} else {
 lean_dec_ref(x_1302);
 x_1408 = lean_box(0);
}
if (lean_is_scalar(x_1408)) {
 x_1409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1409 = x_1408;
}
lean_ctor_set(x_1409, 0, x_1406);
lean_ctor_set(x_1409, 1, x_1407);
return x_1409;
}
}
else
{
lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; 
lean_dec_ref(x_1290);
lean_inc_ref(x_1288);
lean_dec_ref(x_1);
x_1410 = lean_ctor_get(x_1299, 1);
lean_inc(x_1410);
lean_dec_ref(x_1299);
x_1411 = lean_ctor_get(x_1300, 0);
lean_inc(x_1411);
lean_dec_ref(x_1300);
x_1412 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1295, x_1410);
if (lean_obj_tag(x_1412) == 0)
{
lean_object* x_1413; lean_object* x_1414; 
x_1413 = lean_ctor_get(x_1412, 1);
lean_inc(x_1413);
lean_dec_ref(x_1412);
lean_inc(x_1289);
lean_inc_ref(x_1297);
lean_inc(x_1291);
lean_inc_ref(x_1293);
lean_inc_ref(x_1294);
lean_inc(x_1295);
lean_inc_ref(x_1296);
x_1414 = l_Lean_Compiler_LCNF_Simp_simp(x_1288, x_1296, x_1295, x_1294, x_1293, x_1291, x_1297, x_1289, x_1413);
if (lean_obj_tag(x_1414) == 0)
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; 
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1414, 1);
lean_inc(x_1416);
lean_dec_ref(x_1414);
x_1417 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1411, x_1415, x_1296, x_1295, x_1294, x_1293, x_1291, x_1297, x_1289, x_1416);
lean_dec(x_1289);
lean_dec_ref(x_1297);
lean_dec(x_1291);
lean_dec_ref(x_1293);
lean_dec_ref(x_1294);
lean_dec(x_1295);
lean_dec_ref(x_1296);
lean_dec(x_1411);
return x_1417;
}
else
{
lean_dec(x_1411);
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec(x_1289);
return x_1414;
}
}
else
{
lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; 
lean_dec(x_1411);
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec(x_1289);
lean_dec_ref(x_1288);
x_1418 = lean_ctor_get(x_1412, 0);
lean_inc(x_1418);
x_1419 = lean_ctor_get(x_1412, 1);
lean_inc(x_1419);
if (lean_is_exclusive(x_1412)) {
 lean_ctor_release(x_1412, 0);
 lean_ctor_release(x_1412, 1);
 x_1420 = x_1412;
} else {
 lean_dec_ref(x_1412);
 x_1420 = lean_box(0);
}
if (lean_is_scalar(x_1420)) {
 x_1421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1421 = x_1420;
}
lean_ctor_set(x_1421, 0, x_1418);
lean_ctor_set(x_1421, 1, x_1419);
return x_1421;
}
}
}
else
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; 
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec_ref(x_1290);
lean_dec(x_1289);
lean_dec_ref(x_1);
x_1422 = lean_ctor_get(x_1299, 0);
lean_inc(x_1422);
x_1423 = lean_ctor_get(x_1299, 1);
lean_inc(x_1423);
if (lean_is_exclusive(x_1299)) {
 lean_ctor_release(x_1299, 0);
 lean_ctor_release(x_1299, 1);
 x_1424 = x_1299;
} else {
 lean_dec_ref(x_1299);
 x_1424 = lean_box(0);
}
if (lean_is_scalar(x_1424)) {
 x_1425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1425 = x_1424;
}
lean_ctor_set(x_1425, 0, x_1422);
lean_ctor_set(x_1425, 1, x_1423);
return x_1425;
}
}
else
{
lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; uint8_t x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; 
lean_inc_ref(x_1288);
lean_dec_ref(x_1);
x_1426 = lean_st_ref_take(x_1295, x_1292);
x_1427 = lean_ctor_get(x_1426, 0);
lean_inc(x_1427);
x_1428 = lean_ctor_get(x_1426, 1);
lean_inc(x_1428);
lean_dec_ref(x_1426);
x_1429 = lean_ctor_get(x_1290, 0);
x_1430 = lean_ctor_get(x_1427, 0);
lean_inc_ref(x_1430);
x_1431 = lean_ctor_get(x_1427, 1);
lean_inc_ref(x_1431);
x_1432 = lean_ctor_get(x_1427, 2);
lean_inc(x_1432);
x_1433 = lean_ctor_get(x_1427, 3);
lean_inc_ref(x_1433);
x_1434 = lean_ctor_get_uint8(x_1427, sizeof(void*)*7);
x_1435 = lean_ctor_get(x_1427, 4);
lean_inc(x_1435);
x_1436 = lean_ctor_get(x_1427, 5);
lean_inc(x_1436);
x_1437 = lean_ctor_get(x_1427, 6);
lean_inc(x_1437);
if (lean_is_exclusive(x_1427)) {
 lean_ctor_release(x_1427, 0);
 lean_ctor_release(x_1427, 1);
 lean_ctor_release(x_1427, 2);
 lean_ctor_release(x_1427, 3);
 lean_ctor_release(x_1427, 4);
 lean_ctor_release(x_1427, 5);
 lean_ctor_release(x_1427, 6);
 x_1438 = x_1427;
} else {
 lean_dec_ref(x_1427);
 x_1438 = lean_box(0);
}
x_1439 = lean_box(0);
lean_inc(x_1429);
x_1440 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1430, x_1429, x_1439);
if (lean_is_scalar(x_1438)) {
 x_1441 = lean_alloc_ctor(0, 7, 1);
} else {
 x_1441 = x_1438;
}
lean_ctor_set(x_1441, 0, x_1440);
lean_ctor_set(x_1441, 1, x_1431);
lean_ctor_set(x_1441, 2, x_1432);
lean_ctor_set(x_1441, 3, x_1433);
lean_ctor_set(x_1441, 4, x_1435);
lean_ctor_set(x_1441, 5, x_1436);
lean_ctor_set(x_1441, 6, x_1437);
lean_ctor_set_uint8(x_1441, sizeof(void*)*7, x_1434);
x_1442 = lean_st_ref_set(x_1295, x_1441, x_1428);
x_1443 = lean_ctor_get(x_1442, 1);
lean_inc(x_1443);
lean_dec_ref(x_1442);
x_1444 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1290, x_1295, x_1291, x_1443);
lean_dec_ref(x_1290);
if (lean_obj_tag(x_1444) == 0)
{
lean_object* x_1445; 
x_1445 = lean_ctor_get(x_1444, 1);
lean_inc(x_1445);
lean_dec_ref(x_1444);
x_1 = x_1288;
x_2 = x_1296;
x_3 = x_1295;
x_4 = x_1294;
x_5 = x_1293;
x_6 = x_1291;
x_7 = x_1297;
x_8 = x_1289;
x_9 = x_1445;
goto _start;
}
else
{
lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; 
lean_dec_ref(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1291);
lean_dec(x_1289);
lean_dec_ref(x_1288);
x_1447 = lean_ctor_get(x_1444, 0);
lean_inc(x_1447);
x_1448 = lean_ctor_get(x_1444, 1);
lean_inc(x_1448);
if (lean_is_exclusive(x_1444)) {
 lean_ctor_release(x_1444, 0);
 lean_ctor_release(x_1444, 1);
 x_1449 = x_1444;
} else {
 lean_dec_ref(x_1444);
 x_1449 = lean_box(0);
}
if (lean_is_scalar(x_1449)) {
 x_1450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1450 = x_1449;
}
lean_ctor_set(x_1450, 0, x_1447);
lean_ctor_set(x_1450, 1, x_1448);
return x_1450;
}
}
}
block_1466:
{
uint8_t x_1463; 
x_1463 = l_Lean_Expr_isErased(x_1453);
lean_dec_ref(x_1453);
if (x_1463 == 0)
{
lean_dec(x_1454);
x_1289 = x_1461;
x_1290 = x_1452;
x_1291 = x_1459;
x_1292 = x_1462;
x_1293 = x_1458;
x_1294 = x_1457;
x_1295 = x_1456;
x_1296 = x_1455;
x_1297 = x_1460;
x_1298 = x_54;
goto block_1451;
}
else
{
lean_object* x_1464; uint8_t x_1465; 
x_1464 = lean_box(1);
x_1465 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_1454, x_1464);
lean_dec(x_1454);
if (x_1465 == 0)
{
x_1289 = x_1461;
x_1290 = x_1452;
x_1291 = x_1459;
x_1292 = x_1462;
x_1293 = x_1458;
x_1294 = x_1457;
x_1295 = x_1456;
x_1296 = x_1455;
x_1297 = x_1460;
x_1298 = x_1463;
goto block_1451;
}
else
{
x_1289 = x_1461;
x_1290 = x_1452;
x_1291 = x_1459;
x_1292 = x_1462;
x_1293 = x_1458;
x_1294 = x_1457;
x_1295 = x_1456;
x_1296 = x_1455;
x_1297 = x_1460;
x_1298 = x_54;
goto block_1451;
}
}
}
}
case 3:
{
lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; 
lean_dec(x_1221);
x_1517 = lean_ctor_get(x_1, 0);
x_1518 = lean_ctor_get(x_1, 1);
x_1519 = lean_st_ref_get(x_3, x_1220);
x_1520 = lean_ctor_get(x_1519, 0);
lean_inc(x_1520);
x_1521 = lean_ctor_get(x_1519, 1);
lean_inc(x_1521);
lean_dec_ref(x_1519);
x_1522 = lean_ctor_get(x_1520, 0);
lean_inc_ref(x_1522);
lean_dec(x_1520);
lean_inc(x_1517);
x_1523 = l_Lean_Compiler_LCNF_normFVarImp(x_1522, x_1517, x_54);
lean_dec_ref(x_1522);
if (lean_obj_tag(x_1523) == 0)
{
lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; uint8_t x_1530; lean_object* x_1536; lean_object* x_1542; 
x_1524 = lean_ctor_get(x_1523, 0);
lean_inc(x_1524);
lean_dec_ref(x_1523);
lean_inc_ref(x_1518);
x_1525 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_54, x_1518, x_3, x_1521);
x_1526 = lean_ctor_get(x_1525, 0);
lean_inc(x_1526);
x_1527 = lean_ctor_get(x_1525, 1);
lean_inc(x_1527);
if (lean_is_exclusive(x_1525)) {
 lean_ctor_release(x_1525, 0);
 lean_ctor_release(x_1525, 1);
 x_1528 = x_1525;
} else {
 lean_dec_ref(x_1525);
 x_1528 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_1286);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1526);
x_1542 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1524, x_1526, x_2, x_3, x_4, x_5, x_6, x_1286, x_8, x_1527);
if (lean_obj_tag(x_1542) == 0)
{
lean_object* x_1543; 
x_1543 = lean_ctor_get(x_1542, 0);
lean_inc(x_1543);
if (lean_obj_tag(x_1543) == 0)
{
lean_object* x_1544; lean_object* x_1545; 
lean_dec_ref(x_1286);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1544 = lean_ctor_get(x_1542, 1);
lean_inc(x_1544);
lean_dec_ref(x_1542);
lean_inc(x_1524);
x_1545 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1524, x_3, x_1544);
if (lean_obj_tag(x_1545) == 0)
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; uint8_t x_1549; 
x_1546 = lean_ctor_get(x_1545, 1);
lean_inc(x_1546);
lean_dec_ref(x_1545);
x_1547 = lean_unsigned_to_nat(0u);
x_1548 = lean_array_get_size(x_1526);
x_1549 = lean_nat_dec_lt(x_1547, x_1548);
if (x_1549 == 0)
{
lean_dec(x_1548);
lean_dec(x_3);
x_1536 = x_1546;
goto block_1541;
}
else
{
uint8_t x_1550; 
x_1550 = lean_nat_dec_le(x_1548, x_1548);
if (x_1550 == 0)
{
lean_dec(x_1548);
lean_dec(x_3);
x_1536 = x_1546;
goto block_1541;
}
else
{
lean_object* x_1551; size_t x_1552; size_t x_1553; lean_object* x_1554; 
x_1551 = lean_box(0);
x_1552 = 0;
x_1553 = lean_usize_of_nat(x_1548);
lean_dec(x_1548);
x_1554 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1526, x_1552, x_1553, x_1551, x_3, x_1546);
lean_dec(x_3);
if (lean_obj_tag(x_1554) == 0)
{
lean_object* x_1555; 
x_1555 = lean_ctor_get(x_1554, 1);
lean_inc(x_1555);
lean_dec_ref(x_1554);
x_1536 = x_1555;
goto block_1541;
}
else
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; 
lean_dec(x_1528);
lean_dec(x_1526);
lean_dec(x_1524);
lean_dec_ref(x_1);
x_1556 = lean_ctor_get(x_1554, 0);
lean_inc(x_1556);
x_1557 = lean_ctor_get(x_1554, 1);
lean_inc(x_1557);
if (lean_is_exclusive(x_1554)) {
 lean_ctor_release(x_1554, 0);
 lean_ctor_release(x_1554, 1);
 x_1558 = x_1554;
} else {
 lean_dec_ref(x_1554);
 x_1558 = lean_box(0);
}
if (lean_is_scalar(x_1558)) {
 x_1559 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1559 = x_1558;
}
lean_ctor_set(x_1559, 0, x_1556);
lean_ctor_set(x_1559, 1, x_1557);
return x_1559;
}
}
}
}
else
{
lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; 
lean_dec(x_1528);
lean_dec(x_1526);
lean_dec(x_1524);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1560 = lean_ctor_get(x_1545, 0);
lean_inc(x_1560);
x_1561 = lean_ctor_get(x_1545, 1);
lean_inc(x_1561);
if (lean_is_exclusive(x_1545)) {
 lean_ctor_release(x_1545, 0);
 lean_ctor_release(x_1545, 1);
 x_1562 = x_1545;
} else {
 lean_dec_ref(x_1545);
 x_1562 = lean_box(0);
}
if (lean_is_scalar(x_1562)) {
 x_1563 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1563 = x_1562;
}
lean_ctor_set(x_1563, 0, x_1560);
lean_ctor_set(x_1563, 1, x_1561);
return x_1563;
}
}
else
{
lean_object* x_1564; lean_object* x_1565; 
lean_dec(x_1528);
lean_dec(x_1526);
lean_dec(x_1524);
lean_dec_ref(x_1);
x_1564 = lean_ctor_get(x_1542, 1);
lean_inc(x_1564);
lean_dec_ref(x_1542);
x_1565 = lean_ctor_get(x_1543, 0);
lean_inc(x_1565);
lean_dec_ref(x_1543);
x_1 = x_1565;
x_7 = x_1286;
x_9 = x_1564;
goto _start;
}
}
else
{
lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
lean_dec(x_1528);
lean_dec(x_1526);
lean_dec(x_1524);
lean_dec_ref(x_1286);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1567 = lean_ctor_get(x_1542, 0);
lean_inc(x_1567);
x_1568 = lean_ctor_get(x_1542, 1);
lean_inc(x_1568);
if (lean_is_exclusive(x_1542)) {
 lean_ctor_release(x_1542, 0);
 lean_ctor_release(x_1542, 1);
 x_1569 = x_1542;
} else {
 lean_dec_ref(x_1542);
 x_1569 = lean_box(0);
}
if (lean_is_scalar(x_1569)) {
 x_1570 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1570 = x_1569;
}
lean_ctor_set(x_1570, 0, x_1567);
lean_ctor_set(x_1570, 1, x_1568);
return x_1570;
}
block_1535:
{
if (x_1530 == 0)
{
lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1531 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1531 = lean_box(0);
}
if (lean_is_scalar(x_1531)) {
 x_1532 = lean_alloc_ctor(3, 2, 0);
} else {
 x_1532 = x_1531;
}
lean_ctor_set(x_1532, 0, x_1524);
lean_ctor_set(x_1532, 1, x_1526);
if (lean_is_scalar(x_1528)) {
 x_1533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1533 = x_1528;
}
lean_ctor_set(x_1533, 0, x_1532);
lean_ctor_set(x_1533, 1, x_1529);
return x_1533;
}
else
{
lean_object* x_1534; 
lean_dec(x_1526);
lean_dec(x_1524);
if (lean_is_scalar(x_1528)) {
 x_1534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1534 = x_1528;
}
lean_ctor_set(x_1534, 0, x_1);
lean_ctor_set(x_1534, 1, x_1529);
return x_1534;
}
}
block_1541:
{
uint8_t x_1537; 
x_1537 = l_Lean_instBEqFVarId_beq(x_1517, x_1524);
if (x_1537 == 0)
{
x_1529 = x_1536;
x_1530 = x_1537;
goto block_1535;
}
else
{
size_t x_1538; size_t x_1539; uint8_t x_1540; 
x_1538 = lean_ptr_addr(x_1518);
x_1539 = lean_ptr_addr(x_1526);
x_1540 = lean_usize_dec_eq(x_1538, x_1539);
x_1529 = x_1536;
x_1530 = x_1540;
goto block_1535;
}
}
}
else
{
lean_object* x_1571; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1571 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1286, x_8, x_1521);
lean_dec(x_8);
lean_dec_ref(x_1286);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1571;
}
}
case 4:
{
lean_object* x_1572; lean_object* x_1573; 
lean_dec(x_1221);
x_1572 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1572);
lean_inc(x_8);
lean_inc_ref(x_1286);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1572);
x_1573 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1572, x_2, x_3, x_4, x_5, x_6, x_1286, x_8, x_1220);
if (lean_obj_tag(x_1573) == 0)
{
lean_object* x_1574; 
x_1574 = lean_ctor_get(x_1573, 0);
lean_inc(x_1574);
if (lean_obj_tag(x_1574) == 0)
{
lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; 
x_1575 = lean_ctor_get(x_1573, 1);
lean_inc(x_1575);
if (lean_is_exclusive(x_1573)) {
 lean_ctor_release(x_1573, 0);
 lean_ctor_release(x_1573, 1);
 x_1576 = x_1573;
} else {
 lean_dec_ref(x_1573);
 x_1576 = lean_box(0);
}
x_1577 = lean_st_ref_get(x_3, x_1575);
x_1578 = lean_ctor_get(x_1577, 0);
lean_inc(x_1578);
x_1579 = lean_ctor_get(x_1577, 1);
lean_inc(x_1579);
lean_dec_ref(x_1577);
x_1580 = lean_ctor_get(x_1572, 0);
lean_inc(x_1580);
x_1581 = lean_ctor_get(x_1572, 1);
lean_inc_ref(x_1581);
x_1582 = lean_ctor_get(x_1572, 2);
lean_inc(x_1582);
x_1583 = lean_ctor_get(x_1572, 3);
lean_inc_ref(x_1583);
if (lean_is_exclusive(x_1572)) {
 lean_ctor_release(x_1572, 0);
 lean_ctor_release(x_1572, 1);
 lean_ctor_release(x_1572, 2);
 lean_ctor_release(x_1572, 3);
 x_1584 = x_1572;
} else {
 lean_dec_ref(x_1572);
 x_1584 = lean_box(0);
}
x_1585 = lean_ctor_get(x_1578, 0);
lean_inc_ref(x_1585);
lean_dec(x_1578);
lean_inc(x_1582);
x_1586 = l_Lean_Compiler_LCNF_normFVarImp(x_1585, x_1582, x_54);
lean_dec_ref(x_1585);
if (lean_obj_tag(x_1586) == 0)
{
lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; 
x_1587 = lean_ctor_get(x_1586, 0);
lean_inc(x_1587);
if (lean_is_exclusive(x_1586)) {
 lean_ctor_release(x_1586, 0);
 x_1588 = x_1586;
} else {
 lean_dec_ref(x_1586);
 x_1588 = lean_box(0);
}
x_1589 = lean_st_ref_get(x_3, x_1579);
x_1590 = lean_ctor_get(x_1589, 0);
lean_inc(x_1590);
x_1591 = lean_ctor_get(x_1589, 1);
lean_inc(x_1591);
lean_dec_ref(x_1589);
x_1592 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_1286);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1583);
lean_inc(x_1587);
x_1593 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_1587, x_54, x_1592, x_1583, x_2, x_3, x_4, x_5, x_6, x_1286, x_8, x_1591);
if (lean_obj_tag(x_1593) == 0)
{
lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; 
x_1594 = lean_ctor_get(x_1593, 0);
lean_inc(x_1594);
x_1595 = lean_ctor_get(x_1593, 1);
lean_inc(x_1595);
if (lean_is_exclusive(x_1593)) {
 lean_ctor_release(x_1593, 0);
 lean_ctor_release(x_1593, 1);
 x_1596 = x_1593;
} else {
 lean_dec_ref(x_1593);
 x_1596 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_1597 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1594, x_2, x_3, x_4, x_5, x_6, x_1286, x_8, x_1595);
if (lean_obj_tag(x_1597) == 0)
{
lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1608; uint8_t x_1609; lean_object* x_1613; lean_object* x_1614; lean_object* x_1628; uint8_t x_1629; 
x_1598 = lean_ctor_get(x_1597, 0);
lean_inc(x_1598);
x_1599 = lean_ctor_get(x_1597, 1);
lean_inc(x_1599);
if (lean_is_exclusive(x_1597)) {
 lean_ctor_release(x_1597, 0);
 lean_ctor_release(x_1597, 1);
 x_1600 = x_1597;
} else {
 lean_dec_ref(x_1597);
 x_1600 = lean_box(0);
}
x_1601 = lean_ctor_get(x_1590, 0);
lean_inc_ref(x_1601);
lean_dec(x_1590);
lean_inc_ref(x_1581);
x_1602 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1601, x_54, x_1581);
lean_dec_ref(x_1601);
x_1628 = lean_array_get_size(x_1598);
x_1629 = lean_nat_dec_eq(x_1628, x_1284);
lean_dec(x_1628);
if (x_1629 == 0)
{
lean_dec(x_1576);
lean_dec(x_6);
x_1613 = x_3;
x_1614 = x_1599;
goto block_1627;
}
else
{
lean_object* x_1630; 
x_1630 = lean_array_fget_borrowed(x_1598, x_1592);
if (lean_obj_tag(x_1630) == 0)
{
lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1643; lean_object* x_1644; uint8_t x_1657; lean_object* x_1658; uint8_t x_1660; 
lean_dec(x_1576);
x_1631 = lean_ctor_get(x_1630, 1);
x_1632 = lean_ctor_get(x_1630, 2);
x_1643 = lean_array_get_size(x_1631);
x_1660 = lean_nat_dec_lt(x_1592, x_1643);
if (x_1660 == 0)
{
x_1657 = x_54;
x_1658 = x_1599;
goto block_1659;
}
else
{
if (x_1660 == 0)
{
x_1657 = x_54;
x_1658 = x_1599;
goto block_1659;
}
else
{
size_t x_1661; size_t x_1662; lean_object* x_1663; 
x_1661 = 0;
x_1662 = lean_usize_of_nat(x_1643);
x_1663 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1631, x_1661, x_1662, x_3, x_1599);
if (lean_obj_tag(x_1663) == 0)
{
lean_object* x_1664; lean_object* x_1665; uint8_t x_1666; 
x_1664 = lean_ctor_get(x_1663, 0);
lean_inc(x_1664);
x_1665 = lean_ctor_get(x_1663, 1);
lean_inc(x_1665);
lean_dec_ref(x_1663);
x_1666 = lean_unbox(x_1664);
lean_dec(x_1664);
x_1657 = x_1666;
x_1658 = x_1665;
goto block_1659;
}
else
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; 
lean_dec(x_1643);
lean_dec_ref(x_1602);
lean_dec(x_1600);
lean_dec(x_1598);
lean_dec(x_1596);
lean_dec(x_1588);
lean_dec(x_1587);
lean_dec(x_1584);
lean_dec_ref(x_1583);
lean_dec(x_1582);
lean_dec_ref(x_1581);
lean_dec(x_1580);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1667 = lean_ctor_get(x_1663, 0);
lean_inc(x_1667);
x_1668 = lean_ctor_get(x_1663, 1);
lean_inc(x_1668);
if (lean_is_exclusive(x_1663)) {
 lean_ctor_release(x_1663, 0);
 lean_ctor_release(x_1663, 1);
 x_1669 = x_1663;
} else {
 lean_dec_ref(x_1663);
 x_1669 = lean_box(0);
}
if (lean_is_scalar(x_1669)) {
 x_1670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1670 = x_1669;
}
lean_ctor_set(x_1670, 0, x_1667);
lean_ctor_set(x_1670, 1, x_1668);
return x_1670;
}
}
}
block_1642:
{
lean_object* x_1634; 
x_1634 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_1633);
lean_dec(x_3);
if (lean_obj_tag(x_1634) == 0)
{
lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; 
x_1635 = lean_ctor_get(x_1634, 1);
lean_inc(x_1635);
if (lean_is_exclusive(x_1634)) {
 lean_ctor_release(x_1634, 0);
 lean_ctor_release(x_1634, 1);
 x_1636 = x_1634;
} else {
 lean_dec_ref(x_1634);
 x_1636 = lean_box(0);
}
if (lean_is_scalar(x_1636)) {
 x_1637 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1637 = x_1636;
}
lean_ctor_set(x_1637, 0, x_1632);
lean_ctor_set(x_1637, 1, x_1635);
return x_1637;
}
else
{
lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; 
lean_dec_ref(x_1632);
x_1638 = lean_ctor_get(x_1634, 0);
lean_inc(x_1638);
x_1639 = lean_ctor_get(x_1634, 1);
lean_inc(x_1639);
if (lean_is_exclusive(x_1634)) {
 lean_ctor_release(x_1634, 0);
 lean_ctor_release(x_1634, 1);
 x_1640 = x_1634;
} else {
 lean_dec_ref(x_1634);
 x_1640 = lean_box(0);
}
if (lean_is_scalar(x_1640)) {
 x_1641 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1641 = x_1640;
}
lean_ctor_set(x_1641, 0, x_1638);
lean_ctor_set(x_1641, 1, x_1639);
return x_1641;
}
}
block_1656:
{
uint8_t x_1645; 
x_1645 = lean_nat_dec_lt(x_1592, x_1643);
if (x_1645 == 0)
{
lean_dec(x_1643);
lean_dec_ref(x_1631);
lean_dec(x_6);
x_1633 = x_1644;
goto block_1642;
}
else
{
uint8_t x_1646; 
x_1646 = lean_nat_dec_le(x_1643, x_1643);
if (x_1646 == 0)
{
lean_dec(x_1643);
lean_dec_ref(x_1631);
lean_dec(x_6);
x_1633 = x_1644;
goto block_1642;
}
else
{
lean_object* x_1647; size_t x_1648; size_t x_1649; lean_object* x_1650; 
x_1647 = lean_box(0);
x_1648 = 0;
x_1649 = lean_usize_of_nat(x_1643);
lean_dec(x_1643);
x_1650 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1631, x_1648, x_1649, x_1647, x_6, x_1644);
lean_dec(x_6);
lean_dec_ref(x_1631);
if (lean_obj_tag(x_1650) == 0)
{
lean_object* x_1651; 
x_1651 = lean_ctor_get(x_1650, 1);
lean_inc(x_1651);
lean_dec_ref(x_1650);
x_1633 = x_1651;
goto block_1642;
}
else
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; 
lean_dec_ref(x_1632);
lean_dec(x_3);
x_1652 = lean_ctor_get(x_1650, 0);
lean_inc(x_1652);
x_1653 = lean_ctor_get(x_1650, 1);
lean_inc(x_1653);
if (lean_is_exclusive(x_1650)) {
 lean_ctor_release(x_1650, 0);
 lean_ctor_release(x_1650, 1);
 x_1654 = x_1650;
} else {
 lean_dec_ref(x_1650);
 x_1654 = lean_box(0);
}
if (lean_is_scalar(x_1654)) {
 x_1655 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1655 = x_1654;
}
lean_ctor_set(x_1655, 0, x_1652);
lean_ctor_set(x_1655, 1, x_1653);
return x_1655;
}
}
}
}
block_1659:
{
if (x_1657 == 0)
{
lean_inc_ref(x_1632);
lean_inc_ref(x_1631);
lean_dec_ref(x_1602);
lean_dec(x_1600);
lean_dec(x_1598);
lean_dec(x_1596);
lean_dec(x_1588);
lean_dec(x_1587);
lean_dec(x_1584);
lean_dec_ref(x_1583);
lean_dec(x_1582);
lean_dec_ref(x_1581);
lean_dec(x_1580);
lean_dec_ref(x_1);
x_1644 = x_1658;
goto block_1656;
}
else
{
if (x_54 == 0)
{
lean_dec(x_1643);
lean_dec(x_6);
x_1613 = x_3;
x_1614 = x_1658;
goto block_1627;
}
else
{
lean_inc_ref(x_1632);
lean_inc_ref(x_1631);
lean_dec_ref(x_1602);
lean_dec(x_1600);
lean_dec(x_1598);
lean_dec(x_1596);
lean_dec(x_1588);
lean_dec(x_1587);
lean_dec(x_1584);
lean_dec_ref(x_1583);
lean_dec(x_1582);
lean_dec_ref(x_1581);
lean_dec(x_1580);
lean_dec_ref(x_1);
x_1644 = x_1658;
goto block_1656;
}
}
}
}
else
{
lean_object* x_1671; lean_object* x_1672; 
lean_inc_ref(x_1630);
lean_dec_ref(x_1602);
lean_dec(x_1600);
lean_dec(x_1598);
lean_dec(x_1596);
lean_dec(x_1588);
lean_dec(x_1587);
lean_dec(x_1584);
lean_dec_ref(x_1583);
lean_dec(x_1582);
lean_dec_ref(x_1581);
lean_dec(x_1580);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1671 = lean_ctor_get(x_1630, 0);
lean_inc_ref(x_1671);
lean_dec_ref(x_1630);
if (lean_is_scalar(x_1576)) {
 x_1672 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1672 = x_1576;
}
lean_ctor_set(x_1672, 0, x_1671);
lean_ctor_set(x_1672, 1, x_1599);
return x_1672;
}
}
block_1607:
{
lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; 
if (lean_is_scalar(x_1584)) {
 x_1604 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1604 = x_1584;
}
lean_ctor_set(x_1604, 0, x_1580);
lean_ctor_set(x_1604, 1, x_1602);
lean_ctor_set(x_1604, 2, x_1587);
lean_ctor_set(x_1604, 3, x_1598);
if (lean_is_scalar(x_1588)) {
 x_1605 = lean_alloc_ctor(4, 1, 0);
} else {
 x_1605 = x_1588;
 lean_ctor_set_tag(x_1605, 4);
}
lean_ctor_set(x_1605, 0, x_1604);
if (lean_is_scalar(x_1600)) {
 x_1606 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1606 = x_1600;
}
lean_ctor_set(x_1606, 0, x_1605);
lean_ctor_set(x_1606, 1, x_1603);
return x_1606;
}
block_1612:
{
if (x_1609 == 0)
{
lean_dec(x_1596);
lean_dec(x_1582);
lean_dec_ref(x_1);
x_1603 = x_1608;
goto block_1607;
}
else
{
uint8_t x_1610; 
x_1610 = l_Lean_instBEqFVarId_beq(x_1582, x_1587);
lean_dec(x_1582);
if (x_1610 == 0)
{
lean_dec(x_1596);
lean_dec_ref(x_1);
x_1603 = x_1608;
goto block_1607;
}
else
{
lean_object* x_1611; 
lean_dec_ref(x_1602);
lean_dec(x_1600);
lean_dec(x_1598);
lean_dec(x_1588);
lean_dec(x_1587);
lean_dec(x_1584);
lean_dec(x_1580);
if (lean_is_scalar(x_1596)) {
 x_1611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1611 = x_1596;
}
lean_ctor_set(x_1611, 0, x_1);
lean_ctor_set(x_1611, 1, x_1608);
return x_1611;
}
}
}
block_1627:
{
lean_object* x_1615; 
lean_inc(x_1587);
x_1615 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1587, x_1613, x_1614);
lean_dec(x_1613);
if (lean_obj_tag(x_1615) == 0)
{
lean_object* x_1616; size_t x_1617; size_t x_1618; uint8_t x_1619; 
x_1616 = lean_ctor_get(x_1615, 1);
lean_inc(x_1616);
lean_dec_ref(x_1615);
x_1617 = lean_ptr_addr(x_1583);
lean_dec_ref(x_1583);
x_1618 = lean_ptr_addr(x_1598);
x_1619 = lean_usize_dec_eq(x_1617, x_1618);
if (x_1619 == 0)
{
lean_dec_ref(x_1581);
x_1608 = x_1616;
x_1609 = x_1619;
goto block_1612;
}
else
{
size_t x_1620; size_t x_1621; uint8_t x_1622; 
x_1620 = lean_ptr_addr(x_1581);
lean_dec_ref(x_1581);
x_1621 = lean_ptr_addr(x_1602);
x_1622 = lean_usize_dec_eq(x_1620, x_1621);
x_1608 = x_1616;
x_1609 = x_1622;
goto block_1612;
}
}
else
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; 
lean_dec_ref(x_1602);
lean_dec(x_1600);
lean_dec(x_1598);
lean_dec(x_1596);
lean_dec(x_1588);
lean_dec(x_1587);
lean_dec(x_1584);
lean_dec_ref(x_1583);
lean_dec(x_1582);
lean_dec_ref(x_1581);
lean_dec(x_1580);
lean_dec_ref(x_1);
x_1623 = lean_ctor_get(x_1615, 0);
lean_inc(x_1623);
x_1624 = lean_ctor_get(x_1615, 1);
lean_inc(x_1624);
if (lean_is_exclusive(x_1615)) {
 lean_ctor_release(x_1615, 0);
 lean_ctor_release(x_1615, 1);
 x_1625 = x_1615;
} else {
 lean_dec_ref(x_1615);
 x_1625 = lean_box(0);
}
if (lean_is_scalar(x_1625)) {
 x_1626 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1626 = x_1625;
}
lean_ctor_set(x_1626, 0, x_1623);
lean_ctor_set(x_1626, 1, x_1624);
return x_1626;
}
}
}
else
{
lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; 
lean_dec(x_1596);
lean_dec(x_1590);
lean_dec(x_1588);
lean_dec(x_1587);
lean_dec(x_1584);
lean_dec_ref(x_1583);
lean_dec(x_1582);
lean_dec_ref(x_1581);
lean_dec(x_1580);
lean_dec(x_1576);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1673 = lean_ctor_get(x_1597, 0);
lean_inc(x_1673);
x_1674 = lean_ctor_get(x_1597, 1);
lean_inc(x_1674);
if (lean_is_exclusive(x_1597)) {
 lean_ctor_release(x_1597, 0);
 lean_ctor_release(x_1597, 1);
 x_1675 = x_1597;
} else {
 lean_dec_ref(x_1597);
 x_1675 = lean_box(0);
}
if (lean_is_scalar(x_1675)) {
 x_1676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1676 = x_1675;
}
lean_ctor_set(x_1676, 0, x_1673);
lean_ctor_set(x_1676, 1, x_1674);
return x_1676;
}
}
else
{
lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; 
lean_dec(x_1590);
lean_dec(x_1588);
lean_dec(x_1587);
lean_dec(x_1584);
lean_dec_ref(x_1583);
lean_dec(x_1582);
lean_dec_ref(x_1581);
lean_dec(x_1580);
lean_dec(x_1576);
lean_dec_ref(x_1286);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1677 = lean_ctor_get(x_1593, 0);
lean_inc(x_1677);
x_1678 = lean_ctor_get(x_1593, 1);
lean_inc(x_1678);
if (lean_is_exclusive(x_1593)) {
 lean_ctor_release(x_1593, 0);
 lean_ctor_release(x_1593, 1);
 x_1679 = x_1593;
} else {
 lean_dec_ref(x_1593);
 x_1679 = lean_box(0);
}
if (lean_is_scalar(x_1679)) {
 x_1680 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1680 = x_1679;
}
lean_ctor_set(x_1680, 0, x_1677);
lean_ctor_set(x_1680, 1, x_1678);
return x_1680;
}
}
else
{
lean_object* x_1681; 
lean_dec(x_1584);
lean_dec_ref(x_1583);
lean_dec(x_1582);
lean_dec_ref(x_1581);
lean_dec(x_1580);
lean_dec(x_1576);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1681 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1286, x_8, x_1579);
lean_dec(x_8);
lean_dec_ref(x_1286);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1681;
}
}
else
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
lean_dec_ref(x_1572);
lean_dec_ref(x_1286);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1682 = lean_ctor_get(x_1573, 1);
lean_inc(x_1682);
if (lean_is_exclusive(x_1573)) {
 lean_ctor_release(x_1573, 0);
 lean_ctor_release(x_1573, 1);
 x_1683 = x_1573;
} else {
 lean_dec_ref(x_1573);
 x_1683 = lean_box(0);
}
x_1684 = lean_ctor_get(x_1574, 0);
lean_inc(x_1684);
lean_dec_ref(x_1574);
if (lean_is_scalar(x_1683)) {
 x_1685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1685 = x_1683;
}
lean_ctor_set(x_1685, 0, x_1684);
lean_ctor_set(x_1685, 1, x_1682);
return x_1685;
}
}
else
{
lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
lean_dec_ref(x_1572);
lean_dec_ref(x_1286);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1686 = lean_ctor_get(x_1573, 0);
lean_inc(x_1686);
x_1687 = lean_ctor_get(x_1573, 1);
lean_inc(x_1687);
if (lean_is_exclusive(x_1573)) {
 lean_ctor_release(x_1573, 0);
 lean_ctor_release(x_1573, 1);
 x_1688 = x_1573;
} else {
 lean_dec_ref(x_1573);
 x_1688 = lean_box(0);
}
if (lean_is_scalar(x_1688)) {
 x_1689 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1689 = x_1688;
}
lean_ctor_set(x_1689, 0, x_1686);
lean_ctor_set(x_1689, 1, x_1687);
return x_1689;
}
}
case 5:
{
lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; 
lean_dec(x_1221);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1690 = lean_ctor_get(x_1, 0);
x_1691 = lean_st_ref_get(x_3, x_1220);
x_1692 = lean_ctor_get(x_1691, 0);
lean_inc(x_1692);
x_1693 = lean_ctor_get(x_1691, 1);
lean_inc(x_1693);
lean_dec_ref(x_1691);
x_1694 = lean_ctor_get(x_1692, 0);
lean_inc_ref(x_1694);
lean_dec(x_1692);
lean_inc(x_1690);
x_1695 = l_Lean_Compiler_LCNF_normFVarImp(x_1694, x_1690, x_54);
lean_dec_ref(x_1694);
if (lean_obj_tag(x_1695) == 0)
{
lean_object* x_1696; lean_object* x_1697; 
lean_dec_ref(x_1286);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1696 = lean_ctor_get(x_1695, 0);
lean_inc(x_1696);
lean_dec_ref(x_1695);
lean_inc(x_1696);
x_1697 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1696, x_3, x_1693);
lean_dec(x_3);
if (lean_obj_tag(x_1697) == 0)
{
lean_object* x_1698; lean_object* x_1699; uint8_t x_1700; 
x_1698 = lean_ctor_get(x_1697, 1);
lean_inc(x_1698);
if (lean_is_exclusive(x_1697)) {
 lean_ctor_release(x_1697, 0);
 lean_ctor_release(x_1697, 1);
 x_1699 = x_1697;
} else {
 lean_dec_ref(x_1697);
 x_1699 = lean_box(0);
}
x_1700 = l_Lean_instBEqFVarId_beq(x_1690, x_1696);
if (x_1700 == 0)
{
lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1701 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1701 = lean_box(0);
}
if (lean_is_scalar(x_1701)) {
 x_1702 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1702 = x_1701;
}
lean_ctor_set(x_1702, 0, x_1696);
if (lean_is_scalar(x_1699)) {
 x_1703 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1703 = x_1699;
}
lean_ctor_set(x_1703, 0, x_1702);
lean_ctor_set(x_1703, 1, x_1698);
return x_1703;
}
else
{
lean_object* x_1704; 
lean_dec(x_1696);
if (lean_is_scalar(x_1699)) {
 x_1704 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1704 = x_1699;
}
lean_ctor_set(x_1704, 0, x_1);
lean_ctor_set(x_1704, 1, x_1698);
return x_1704;
}
}
else
{
lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; 
lean_dec(x_1696);
lean_dec_ref(x_1);
x_1705 = lean_ctor_get(x_1697, 0);
lean_inc(x_1705);
x_1706 = lean_ctor_get(x_1697, 1);
lean_inc(x_1706);
if (lean_is_exclusive(x_1697)) {
 lean_ctor_release(x_1697, 0);
 lean_ctor_release(x_1697, 1);
 x_1707 = x_1697;
} else {
 lean_dec_ref(x_1697);
 x_1707 = lean_box(0);
}
if (lean_is_scalar(x_1707)) {
 x_1708 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1708 = x_1707;
}
lean_ctor_set(x_1708, 0, x_1705);
lean_ctor_set(x_1708, 1, x_1706);
return x_1708;
}
}
else
{
lean_object* x_1709; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1709 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1286, x_8, x_1693);
lean_dec(x_8);
lean_dec_ref(x_1286);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1709;
}
}
case 6:
{
lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; size_t x_1716; size_t x_1717; uint8_t x_1718; 
lean_dec_ref(x_1286);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1710 = lean_ctor_get(x_1, 0);
x_1711 = lean_st_ref_get(x_3, x_1220);
lean_dec(x_3);
x_1712 = lean_ctor_get(x_1711, 0);
lean_inc(x_1712);
x_1713 = lean_ctor_get(x_1711, 1);
lean_inc(x_1713);
lean_dec_ref(x_1711);
x_1714 = lean_ctor_get(x_1712, 0);
lean_inc_ref(x_1714);
lean_dec(x_1712);
lean_inc_ref(x_1710);
x_1715 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1714, x_54, x_1710);
lean_dec_ref(x_1714);
x_1716 = lean_ptr_addr(x_1710);
x_1717 = lean_ptr_addr(x_1715);
x_1718 = lean_usize_dec_eq(x_1716, x_1717);
if (x_1718 == 0)
{
lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1719 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1719 = lean_box(0);
}
if (lean_is_scalar(x_1719)) {
 x_1720 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1720 = x_1719;
}
lean_ctor_set(x_1720, 0, x_1715);
if (lean_is_scalar(x_1221)) {
 x_1721 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1721 = x_1221;
}
lean_ctor_set(x_1721, 0, x_1720);
lean_ctor_set(x_1721, 1, x_1713);
return x_1721;
}
else
{
lean_object* x_1722; 
lean_dec_ref(x_1715);
if (lean_is_scalar(x_1221)) {
 x_1722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1722 = x_1221;
}
lean_ctor_set(x_1722, 0, x_1);
lean_ctor_set(x_1722, 1, x_1713);
return x_1722;
}
}
default: 
{
lean_object* x_1723; lean_object* x_1724; 
lean_dec(x_1221);
x_1723 = lean_ctor_get(x_1, 0);
x_1724 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1724);
lean_inc_ref(x_1723);
x_1222 = x_1723;
x_1223 = x_1724;
x_1224 = x_2;
x_1225 = x_3;
x_1226 = x_4;
x_1227 = x_5;
x_1228 = x_6;
x_1229 = x_1286;
x_1230 = x_8;
goto block_1283;
}
}
block_1283:
{
lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; 
x_1231 = lean_ctor_get(x_1222, 0);
x_1232 = lean_ctor_get(x_1222, 2);
x_1233 = lean_ctor_get(x_1222, 3);
x_1234 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_1231, x_1225, x_1220);
if (lean_obj_tag(x_1234) == 0)
{
lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; uint8_t x_1238; 
x_1235 = lean_ctor_get(x_1234, 0);
lean_inc(x_1235);
x_1236 = lean_ctor_get(x_1234, 1);
lean_inc(x_1236);
lean_dec_ref(x_1234);
lean_inc(x_1235);
lean_inc_ref(x_1);
lean_inc_ref(x_1223);
x_1237 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_1237, 0, x_1223);
lean_closure_set(x_1237, 1, x_1);
lean_closure_set(x_1237, 2, x_1235);
x_1238 = lean_unbox(x_1235);
if (x_1238 == 0)
{
uint8_t x_1239; 
lean_dec(x_1235);
lean_dec_ref(x_1223);
x_1239 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_1239 == 0)
{
x_18 = x_1237;
x_19 = x_1222;
x_20 = x_1224;
x_21 = x_1225;
x_22 = x_1226;
x_23 = x_1227;
x_24 = x_1228;
x_25 = x_1229;
x_26 = x_1230;
x_27 = x_1236;
goto block_37;
}
else
{
uint8_t x_1240; 
lean_inc_ref(x_1233);
x_1240 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_1233, x_1232);
if (x_1240 == 0)
{
x_18 = x_1237;
x_19 = x_1222;
x_20 = x_1224;
x_21 = x_1225;
x_22 = x_1226;
x_23 = x_1227;
x_24 = x_1228;
x_25 = x_1229;
x_26 = x_1230;
x_27 = x_1236;
goto block_37;
}
else
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; 
x_1241 = lean_st_ref_get(x_1225, x_1236);
x_1242 = lean_ctor_get(x_1241, 0);
lean_inc(x_1242);
x_1243 = lean_ctor_get(x_1241, 1);
lean_inc(x_1243);
lean_dec_ref(x_1241);
x_1244 = lean_ctor_get(x_1242, 0);
lean_inc_ref(x_1244);
lean_dec(x_1242);
x_1245 = l_Lean_Compiler_LCNF_normFunDeclImp(x_54, x_1222, x_1244, x_1227, x_1228, x_1229, x_1230, x_1243);
lean_dec_ref(x_1244);
if (lean_obj_tag(x_1245) == 0)
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
x_1246 = lean_ctor_get(x_1245, 0);
lean_inc(x_1246);
x_1247 = lean_ctor_get(x_1245, 1);
lean_inc(x_1247);
lean_dec_ref(x_1245);
lean_inc(x_1230);
lean_inc_ref(x_1229);
lean_inc(x_1228);
lean_inc_ref(x_1227);
x_1248 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_1246, x_1227, x_1228, x_1229, x_1230, x_1247);
if (lean_obj_tag(x_1248) == 0)
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
x_1249 = lean_ctor_get(x_1248, 0);
lean_inc(x_1249);
x_1250 = lean_ctor_get(x_1248, 1);
lean_inc(x_1250);
lean_dec_ref(x_1248);
x_1251 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1225, x_1250);
if (lean_obj_tag(x_1251) == 0)
{
lean_object* x_1252; 
x_1252 = lean_ctor_get(x_1251, 1);
lean_inc(x_1252);
lean_dec_ref(x_1251);
x_18 = x_1237;
x_19 = x_1249;
x_20 = x_1224;
x_21 = x_1225;
x_22 = x_1226;
x_23 = x_1227;
x_24 = x_1228;
x_25 = x_1229;
x_26 = x_1230;
x_27 = x_1252;
goto block_37;
}
else
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
lean_dec(x_1249);
lean_dec_ref(x_1237);
lean_dec(x_1230);
lean_dec_ref(x_1229);
lean_dec(x_1228);
lean_dec_ref(x_1227);
lean_dec_ref(x_1226);
lean_dec(x_1225);
lean_dec_ref(x_1224);
x_1253 = lean_ctor_get(x_1251, 0);
lean_inc(x_1253);
x_1254 = lean_ctor_get(x_1251, 1);
lean_inc(x_1254);
if (lean_is_exclusive(x_1251)) {
 lean_ctor_release(x_1251, 0);
 lean_ctor_release(x_1251, 1);
 x_1255 = x_1251;
} else {
 lean_dec_ref(x_1251);
 x_1255 = lean_box(0);
}
if (lean_is_scalar(x_1255)) {
 x_1256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1256 = x_1255;
}
lean_ctor_set(x_1256, 0, x_1253);
lean_ctor_set(x_1256, 1, x_1254);
return x_1256;
}
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
lean_dec_ref(x_1237);
lean_dec(x_1230);
lean_dec_ref(x_1229);
lean_dec(x_1228);
lean_dec_ref(x_1227);
lean_dec_ref(x_1226);
lean_dec(x_1225);
lean_dec_ref(x_1224);
x_1257 = lean_ctor_get(x_1248, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1248, 1);
lean_inc(x_1258);
if (lean_is_exclusive(x_1248)) {
 lean_ctor_release(x_1248, 0);
 lean_ctor_release(x_1248, 1);
 x_1259 = x_1248;
} else {
 lean_dec_ref(x_1248);
 x_1259 = lean_box(0);
}
if (lean_is_scalar(x_1259)) {
 x_1260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1260 = x_1259;
}
lean_ctor_set(x_1260, 0, x_1257);
lean_ctor_set(x_1260, 1, x_1258);
return x_1260;
}
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
lean_dec_ref(x_1237);
lean_dec(x_1230);
lean_dec_ref(x_1229);
lean_dec(x_1228);
lean_dec_ref(x_1227);
lean_dec_ref(x_1226);
lean_dec(x_1225);
lean_dec_ref(x_1224);
x_1261 = lean_ctor_get(x_1245, 0);
lean_inc(x_1261);
x_1262 = lean_ctor_get(x_1245, 1);
lean_inc(x_1262);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1263 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1263 = lean_box(0);
}
if (lean_is_scalar(x_1263)) {
 x_1264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1264 = x_1263;
}
lean_ctor_set(x_1264, 0, x_1261);
lean_ctor_set(x_1264, 1, x_1262);
return x_1264;
}
}
}
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
lean_dec_ref(x_1237);
x_1265 = lean_st_ref_get(x_1225, x_1236);
x_1266 = lean_ctor_get(x_1265, 0);
lean_inc(x_1266);
x_1267 = lean_ctor_get(x_1265, 1);
lean_inc(x_1267);
lean_dec_ref(x_1265);
x_1268 = lean_ctor_get(x_1266, 0);
lean_inc_ref(x_1268);
lean_dec(x_1266);
x_1269 = l_Lean_Compiler_LCNF_normFunDeclImp(x_54, x_1222, x_1268, x_1227, x_1228, x_1229, x_1230, x_1267);
lean_dec_ref(x_1268);
if (lean_obj_tag(x_1269) == 0)
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; uint8_t x_1273; lean_object* x_1274; 
x_1270 = lean_ctor_get(x_1269, 0);
lean_inc(x_1270);
x_1271 = lean_ctor_get(x_1269, 1);
lean_inc(x_1271);
lean_dec_ref(x_1269);
x_1272 = lean_box(0);
x_1273 = lean_unbox(x_1235);
lean_dec(x_1235);
x_1274 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_1223, x_1, x_1273, x_1270, x_1272, x_1224, x_1225, x_1226, x_1227, x_1228, x_1229, x_1230, x_1271);
return x_1274;
}
else
{
lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
lean_dec(x_1235);
lean_dec(x_1230);
lean_dec_ref(x_1229);
lean_dec(x_1228);
lean_dec_ref(x_1227);
lean_dec_ref(x_1226);
lean_dec(x_1225);
lean_dec_ref(x_1224);
lean_dec_ref(x_1223);
lean_dec_ref(x_1);
x_1275 = lean_ctor_get(x_1269, 0);
lean_inc(x_1275);
x_1276 = lean_ctor_get(x_1269, 1);
lean_inc(x_1276);
if (lean_is_exclusive(x_1269)) {
 lean_ctor_release(x_1269, 0);
 lean_ctor_release(x_1269, 1);
 x_1277 = x_1269;
} else {
 lean_dec_ref(x_1269);
 x_1277 = lean_box(0);
}
if (lean_is_scalar(x_1277)) {
 x_1278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1278 = x_1277;
}
lean_ctor_set(x_1278, 0, x_1275);
lean_ctor_set(x_1278, 1, x_1276);
return x_1278;
}
}
}
else
{
lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
lean_dec(x_1230);
lean_dec_ref(x_1229);
lean_dec(x_1228);
lean_dec_ref(x_1227);
lean_dec_ref(x_1226);
lean_dec(x_1225);
lean_dec_ref(x_1224);
lean_dec_ref(x_1223);
lean_dec_ref(x_1222);
lean_dec_ref(x_1);
x_1279 = lean_ctor_get(x_1234, 0);
lean_inc(x_1279);
x_1280 = lean_ctor_get(x_1234, 1);
lean_inc(x_1280);
if (lean_is_exclusive(x_1234)) {
 lean_ctor_release(x_1234, 0);
 lean_ctor_release(x_1234, 1);
 x_1281 = x_1234;
} else {
 lean_dec_ref(x_1234);
 x_1281 = lean_box(0);
}
if (lean_is_scalar(x_1281)) {
 x_1282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1282 = x_1281;
}
lean_ctor_set(x_1282, 0, x_1279);
lean_ctor_set(x_1282, 1, x_1280);
return x_1282;
}
}
}
else
{
lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; 
lean_dec_ref(x_53);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1725 = lean_ctor_get(x_1219, 0);
lean_inc(x_1725);
x_1726 = lean_ctor_get(x_1219, 1);
lean_inc(x_1726);
if (lean_is_exclusive(x_1219)) {
 lean_ctor_release(x_1219, 0);
 lean_ctor_release(x_1219, 1);
 x_1727 = x_1219;
} else {
 lean_dec_ref(x_1219);
 x_1727 = lean_box(0);
}
if (lean_is_scalar(x_1727)) {
 x_1728 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1728 = x_1727;
}
lean_ctor_set(x_1728, 0, x_1725);
lean_ctor_set(x_1728, 1, x_1726);
return x_1728;
}
}
}
else
{
lean_object* x_1729; 
lean_dec_ref(x_1);
x_1729 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1729;
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_12);
lean_dec_ref(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
block_37:
{
lean_object* x_28; 
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
x_28 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_box(0);
x_32 = lean_apply_10(x_18, x_29, x_31, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_6);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_4, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = lean_st_ref_take(x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_array_uget(x_1, x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_25);
x_26 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_24, x_22, x_25);
lean_ctor_set(x_19, 0, x_26);
x_27 = lean_st_ref_set(x_5, x_19, x_20);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_10, x_29);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_30);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_6 = x_28;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
x_36 = lean_ctor_get(x_19, 2);
x_37 = lean_ctor_get(x_19, 3);
x_38 = lean_ctor_get_uint8(x_19, sizeof(void*)*7);
x_39 = lean_ctor_get(x_19, 4);
x_40 = lean_ctor_get(x_19, 5);
x_41 = lean_ctor_get(x_19, 6);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_42 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_42);
x_43 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_34, x_22, x_42);
x_44 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_35);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_39);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set(x_44, 6, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*7, x_38);
x_45 = lean_st_ref_set(x_5, x_44, x_20);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_10, x_47);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_48);
x_49 = 1;
x_50 = lean_usize_add(x_3, x_49);
x_3 = x_50;
x_6 = x_46;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; 
lean_dec(x_4);
x_52 = lean_st_ref_take(x_5, x_6);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_array_uget(x_1, x_3);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_53, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 3);
lean_inc_ref(x_60);
x_61 = lean_ctor_get_uint8(x_53, sizeof(void*)*7);
x_62 = lean_ctor_get(x_53, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_53, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_53, 6);
lean_inc(x_64);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 lean_ctor_release(x_53, 4);
 lean_ctor_release(x_53, 5);
 lean_ctor_release(x_53, 6);
 x_65 = x_53;
} else {
 lean_dec_ref(x_53);
 x_65 = lean_box(0);
}
x_66 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_66);
x_67 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_57, x_56, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 7, 1);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_58);
lean_ctor_set(x_68, 2, x_59);
lean_ctor_set(x_68, 3, x_60);
lean_ctor_set(x_68, 4, x_62);
lean_ctor_set(x_68, 5, x_63);
lean_ctor_set(x_68, 6, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*7, x_61);
x_69 = lean_st_ref_set(x_5, x_68, x_54);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_10, x_71);
lean_dec(x_10);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_9);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_11);
x_74 = 1;
x_75 = lean_usize_add(x_3, x_74);
x_3 = x_75;
x_4 = x_73;
x_6 = x_70;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
x_15 = 0;
lean_inc(x_13);
x_16 = l_Lean_Compiler_LCNF_normFVarImp(x_14, x_13, x_15);
lean_dec_ref(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_18, x_4, x_6, x_8, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_free_object(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec_ref(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_29 = x_20;
} else {
 lean_dec_ref(x_20);
 x_29 = lean_box(0);
}
x_30 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_28);
x_31 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_ctor_set_tag(x_16, 4);
lean_ctor_set(x_16, 0, x_34);
x_35 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_16, x_6, x_27);
lean_dec_ref(x_16);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_36);
if (lean_obj_tag(x_37) == 0)
{
if (lean_obj_tag(x_33) == 0)
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_free_object(x_31);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_40);
lean_dec_ref(x_33);
x_41 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_42);
lean_dec_ref(x_28);
x_69 = lean_ctor_get(x_41, 3);
lean_inc(x_69);
lean_dec_ref(x_41);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_array_get_size(x_42);
x_72 = lean_nat_dec_le(x_69, x_70);
if (x_72 == 0)
{
x_43 = x_69;
x_44 = x_71;
goto block_68;
}
else
{
lean_dec(x_69);
x_43 = x_70;
x_44 = x_71;
goto block_68;
}
block_68:
{
lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = l_Array_toSubarray___redArg(x_42, x_43, x_44);
x_46 = lean_array_size(x_39);
x_47 = 0;
x_48 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_39, x_46, x_47, x_45, x_3, x_38);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
lean_inc(x_6);
x_50 = l_Lean_Compiler_LCNF_Simp_simp(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_39, x_6, x_52);
lean_dec(x_6);
lean_dec_ref(x_39);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
if (lean_is_scalar(x_29)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_29;
}
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
if (lean_is_scalar(x_29)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_29;
}
lean_ctor_set(x_58, 0, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_51);
lean_dec(x_29);
x_60 = !lean_is_exclusive(x_53);
if (x_60 == 0)
{
return x_53;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_53, 0);
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_53);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_39);
lean_dec(x_29);
lean_dec(x_6);
x_64 = !lean_is_exclusive(x_50);
if (x_64 == 0)
{
return x_50;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_50, 0);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_50);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_37, 1);
lean_inc(x_73);
lean_dec_ref(x_37);
x_74 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_75);
lean_dec_ref(x_33);
x_76 = !lean_is_exclusive(x_28);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_28, 0);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_77, x_78);
if (x_79 == 1)
{
lean_object* x_80; 
lean_free_object(x_28);
lean_dec(x_77);
lean_dec_ref(x_74);
lean_free_object(x_31);
x_80 = l_Lean_Compiler_LCNF_Simp_simp(x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 0);
if (lean_is_scalar(x_29)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_29;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_80, 0, x_83);
return x_80;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_80, 0);
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_80);
if (lean_is_scalar(x_29)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_29;
}
lean_ctor_set(x_86, 0, x_84);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_29);
x_88 = !lean_is_exclusive(x_80);
if (x_88 == 0)
{
return x_80;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_80, 0);
x_90 = lean_ctor_get(x_80, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_80);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_sub(x_77, x_92);
lean_dec(x_77);
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_93);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_28);
x_95 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_96 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_94, x_95, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec_ref(x_96);
x_99 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_100 = lean_array_get_borrowed(x_99, x_74, x_78);
x_101 = lean_ctor_get(x_100, 0);
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
lean_inc(x_101);
x_103 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_101, x_102, x_3, x_6, x_7, x_8, x_98);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec_ref(x_103);
lean_inc(x_6);
x_105 = l_Lean_Compiler_LCNF_Simp_simp(x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_74, x_6, x_107);
lean_dec(x_6);
lean_dec_ref(x_74);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 0);
lean_dec(x_110);
lean_ctor_set(x_31, 1, x_106);
lean_ctor_set(x_31, 0, x_97);
if (lean_is_scalar(x_29)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_29;
}
lean_ctor_set(x_111, 0, x_31);
lean_ctor_set(x_108, 0, x_111);
return x_108;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
lean_ctor_set(x_31, 1, x_106);
lean_ctor_set(x_31, 0, x_97);
if (lean_is_scalar(x_29)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_29;
}
lean_ctor_set(x_113, 0, x_31);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_106);
lean_dec(x_97);
lean_free_object(x_31);
lean_dec(x_29);
x_115 = !lean_is_exclusive(x_108);
if (x_115 == 0)
{
return x_108;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_108, 0);
x_117 = lean_ctor_get(x_108, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_108);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_97);
lean_dec_ref(x_74);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_6);
x_119 = !lean_is_exclusive(x_105);
if (x_119 == 0)
{
return x_105;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_105, 0);
x_121 = lean_ctor_get(x_105, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_105);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_97);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_123 = !lean_is_exclusive(x_103);
if (x_123 == 0)
{
return x_103;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_103, 0);
x_125 = lean_ctor_get(x_103, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_103);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_127 = !lean_is_exclusive(x_96);
if (x_127 == 0)
{
return x_96;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_96, 0);
x_129 = lean_ctor_get(x_96, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_96);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_28, 0);
lean_inc(x_131);
lean_dec(x_28);
x_132 = lean_unsigned_to_nat(0u);
x_133 = lean_nat_dec_eq(x_131, x_132);
if (x_133 == 1)
{
lean_object* x_134; 
lean_dec(x_131);
lean_dec_ref(x_74);
lean_free_object(x_31);
x_134 = l_Lean_Compiler_LCNF_Simp_simp(x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_29;
}
lean_ctor_set(x_138, 0, x_135);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_29);
x_140 = lean_ctor_get(x_134, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_134, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_142 = x_134;
} else {
 lean_dec_ref(x_134);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_sub(x_131, x_144);
lean_dec(x_131);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_148 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_149 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_147, x_148, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec_ref(x_149);
x_152 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_153 = lean_array_get_borrowed(x_152, x_74, x_132);
x_154 = lean_ctor_get(x_153, 0);
x_155 = lean_ctor_get(x_150, 0);
lean_inc(x_155);
lean_inc(x_154);
x_156 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_154, x_155, x_3, x_6, x_7, x_8, x_151);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec_ref(x_156);
lean_inc(x_6);
x_158 = l_Lean_Compiler_LCNF_Simp_simp(x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec_ref(x_158);
x_161 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_74, x_6, x_160);
lean_dec(x_6);
lean_dec_ref(x_74);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
lean_ctor_set(x_31, 1, x_159);
lean_ctor_set(x_31, 0, x_150);
if (lean_is_scalar(x_29)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_29;
}
lean_ctor_set(x_164, 0, x_31);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_159);
lean_dec(x_150);
lean_free_object(x_31);
lean_dec(x_29);
x_166 = lean_ctor_get(x_161, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_161, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_168 = x_161;
} else {
 lean_dec_ref(x_161);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_150);
lean_dec_ref(x_74);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_6);
x_170 = lean_ctor_get(x_158, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_158, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_172 = x_158;
} else {
 lean_dec_ref(x_158);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_150);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_174 = lean_ctor_get(x_156, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_156, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_176 = x_156;
} else {
 lean_dec_ref(x_156);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_178 = lean_ctor_get(x_149, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_149, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_180 = x_149;
} else {
 lean_dec_ref(x_149);
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
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_free_object(x_31);
lean_dec(x_28);
x_182 = lean_ctor_get(x_37, 1);
lean_inc(x_182);
lean_dec_ref(x_37);
x_183 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_183);
lean_dec_ref(x_33);
x_184 = l_Lean_Compiler_LCNF_Simp_simp(x_183, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_182);
if (lean_obj_tag(x_184) == 0)
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_184, 0);
if (lean_is_scalar(x_29)) {
 x_187 = lean_alloc_ctor(1, 1, 0);
} else {
 x_187 = x_29;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_184, 0, x_187);
return x_184;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_184, 0);
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_184);
if (lean_is_scalar(x_29)) {
 x_190 = lean_alloc_ctor(1, 1, 0);
} else {
 x_190 = x_29;
}
lean_ctor_set(x_190, 0, x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
uint8_t x_192; 
lean_dec(x_29);
x_192 = !lean_is_exclusive(x_184);
if (x_192 == 0)
{
return x_184;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_184, 0);
x_194 = lean_ctor_get(x_184, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_184);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
else
{
uint8_t x_196; 
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_196 = !lean_is_exclusive(x_37);
if (x_196 == 0)
{
return x_37;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_37, 0);
x_198 = lean_ctor_get(x_37, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_37);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
uint8_t x_200; 
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_200 = !lean_is_exclusive(x_35);
if (x_200 == 0)
{
return x_35;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_35, 0);
x_202 = lean_ctor_get(x_35, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_35);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_31, 0);
x_205 = lean_ctor_get(x_31, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_31);
lean_ctor_set_tag(x_16, 4);
lean_ctor_set(x_16, 0, x_205);
x_206 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_16, x_6, x_27);
lean_dec_ref(x_16);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec_ref(x_206);
x_208 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_207);
if (lean_obj_tag(x_208) == 0)
{
if (lean_obj_tag(x_204) == 0)
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec_ref(x_208);
x_210 = lean_ctor_get(x_204, 1);
lean_inc_ref(x_210);
x_211 = lean_ctor_get(x_204, 2);
lean_inc_ref(x_211);
lean_dec_ref(x_204);
x_212 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_212);
x_213 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_213);
lean_dec_ref(x_28);
x_238 = lean_ctor_get(x_212, 3);
lean_inc(x_238);
lean_dec_ref(x_212);
x_239 = lean_unsigned_to_nat(0u);
x_240 = lean_array_get_size(x_213);
x_241 = lean_nat_dec_le(x_238, x_239);
if (x_241 == 0)
{
x_214 = x_238;
x_215 = x_240;
goto block_237;
}
else
{
lean_dec(x_238);
x_214 = x_239;
x_215 = x_240;
goto block_237;
}
block_237:
{
lean_object* x_216; size_t x_217; size_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = l_Array_toSubarray___redArg(x_213, x_214, x_215);
x_217 = lean_array_size(x_210);
x_218 = 0;
x_219 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_210, x_217, x_218, x_216, x_3, x_209);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec_ref(x_219);
lean_inc(x_6);
x_221 = l_Lean_Compiler_LCNF_Simp_simp(x_211, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec_ref(x_221);
x_224 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_210, x_6, x_223);
lean_dec(x_6);
lean_dec_ref(x_210);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_29;
}
lean_ctor_set(x_227, 0, x_222);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_222);
lean_dec(x_29);
x_229 = lean_ctor_get(x_224, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_224, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_231 = x_224;
} else {
 lean_dec_ref(x_224);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec_ref(x_210);
lean_dec(x_29);
lean_dec(x_6);
x_233 = lean_ctor_get(x_221, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_221, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_235 = x_221;
} else {
 lean_dec_ref(x_221);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
lean_dec_ref(x_208);
x_243 = lean_ctor_get(x_204, 1);
lean_inc_ref(x_243);
x_244 = lean_ctor_get(x_204, 2);
lean_inc_ref(x_244);
lean_dec_ref(x_204);
x_245 = lean_ctor_get(x_28, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_246 = x_28;
} else {
 lean_dec_ref(x_28);
 x_246 = lean_box(0);
}
x_247 = lean_unsigned_to_nat(0u);
x_248 = lean_nat_dec_eq(x_245, x_247);
if (x_248 == 1)
{
lean_object* x_249; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec_ref(x_243);
x_249 = l_Lean_Compiler_LCNF_Simp_simp(x_244, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_242);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_252 = x_249;
} else {
 lean_dec_ref(x_249);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_253 = lean_alloc_ctor(1, 1, 0);
} else {
 x_253 = x_29;
}
lean_ctor_set(x_253, 0, x_250);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_252;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_251);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_29);
x_255 = lean_ctor_get(x_249, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_249, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_257 = x_249;
} else {
 lean_dec_ref(x_249);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_259 = lean_unsigned_to_nat(1u);
x_260 = lean_nat_sub(x_245, x_259);
lean_dec(x_245);
if (lean_is_scalar(x_246)) {
 x_261 = lean_alloc_ctor(0, 1, 0);
} else {
 x_261 = x_246;
 lean_ctor_set_tag(x_261, 0);
}
lean_ctor_set(x_261, 0, x_260);
x_262 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_262, 0, x_261);
x_263 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_264 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_262, x_263, x_5, x_6, x_7, x_8, x_242);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec_ref(x_264);
x_267 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_268 = lean_array_get_borrowed(x_267, x_243, x_247);
x_269 = lean_ctor_get(x_268, 0);
x_270 = lean_ctor_get(x_265, 0);
lean_inc(x_270);
lean_inc(x_269);
x_271 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_269, x_270, x_3, x_6, x_7, x_8, x_266);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec_ref(x_271);
lean_inc(x_6);
x_273 = l_Lean_Compiler_LCNF_Simp_simp(x_244, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_272);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec_ref(x_273);
x_276 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_243, x_6, x_275);
lean_dec(x_6);
lean_dec_ref(x_243);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_278 = x_276;
} else {
 lean_dec_ref(x_276);
 x_278 = lean_box(0);
}
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_265);
lean_ctor_set(x_279, 1, x_274);
if (lean_is_scalar(x_29)) {
 x_280 = lean_alloc_ctor(1, 1, 0);
} else {
 x_280 = x_29;
}
lean_ctor_set(x_280, 0, x_279);
if (lean_is_scalar(x_278)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_278;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_277);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_274);
lean_dec(x_265);
lean_dec(x_29);
x_282 = lean_ctor_get(x_276, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_276, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_284 = x_276;
} else {
 lean_dec_ref(x_276);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_265);
lean_dec_ref(x_243);
lean_dec(x_29);
lean_dec(x_6);
x_286 = lean_ctor_get(x_273, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_273, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_288 = x_273;
} else {
 lean_dec_ref(x_273);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_265);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_290 = lean_ctor_get(x_271, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_271, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_292 = x_271;
} else {
 lean_dec_ref(x_271);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_294 = lean_ctor_get(x_264, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_264, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_296 = x_264;
} else {
 lean_dec_ref(x_264);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_28);
x_298 = lean_ctor_get(x_208, 1);
lean_inc(x_298);
lean_dec_ref(x_208);
x_299 = lean_ctor_get(x_204, 0);
lean_inc_ref(x_299);
lean_dec_ref(x_204);
x_300 = l_Lean_Compiler_LCNF_Simp_simp(x_299, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_298);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_303 = x_300;
} else {
 lean_dec_ref(x_300);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_304 = lean_alloc_ctor(1, 1, 0);
} else {
 x_304 = x_29;
}
lean_ctor_set(x_304, 0, x_301);
if (lean_is_scalar(x_303)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_303;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_302);
return x_305;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_29);
x_306 = lean_ctor_get(x_300, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_300, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_308 = x_300;
} else {
 lean_dec_ref(x_300);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_204);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_310 = lean_ctor_get(x_208, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_208, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_312 = x_208;
} else {
 lean_dec_ref(x_208);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_204);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_314 = lean_ctor_get(x_206, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_206, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_316 = x_206;
} else {
 lean_dec_ref(x_206);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
}
}
else
{
uint8_t x_318; 
lean_free_object(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_318 = !lean_is_exclusive(x_19);
if (x_318 == 0)
{
return x_19;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_19, 0);
x_320 = lean_ctor_get(x_19, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_19);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_16, 0);
lean_inc(x_322);
lean_dec(x_16);
x_323 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_322, x_4, x_6, x_8, x_12);
lean_dec(x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_326 = x_323;
} else {
 lean_dec_ref(x_323);
 x_326 = lean_box(0);
}
x_327 = lean_box(0);
if (lean_is_scalar(x_326)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_326;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_325);
return x_328;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_329 = lean_ctor_get(x_323, 1);
lean_inc(x_329);
lean_dec_ref(x_323);
x_330 = lean_ctor_get(x_324, 0);
lean_inc(x_330);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 x_331 = x_324;
} else {
 lean_dec_ref(x_324);
 x_331 = lean_box(0);
}
x_332 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_330);
x_333 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_332);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_336 = x_333;
} else {
 lean_dec_ref(x_333);
 x_336 = lean_box(0);
}
x_337 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_337, 0, x_335);
x_338 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_337, x_6, x_329);
lean_dec_ref(x_337);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_339);
if (lean_obj_tag(x_340) == 0)
{
if (lean_obj_tag(x_334) == 0)
{
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
lean_dec(x_336);
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
lean_dec_ref(x_340);
x_342 = lean_ctor_get(x_334, 1);
lean_inc_ref(x_342);
x_343 = lean_ctor_get(x_334, 2);
lean_inc_ref(x_343);
lean_dec_ref(x_334);
x_344 = lean_ctor_get(x_330, 0);
lean_inc_ref(x_344);
x_345 = lean_ctor_get(x_330, 1);
lean_inc_ref(x_345);
lean_dec_ref(x_330);
x_370 = lean_ctor_get(x_344, 3);
lean_inc(x_370);
lean_dec_ref(x_344);
x_371 = lean_unsigned_to_nat(0u);
x_372 = lean_array_get_size(x_345);
x_373 = lean_nat_dec_le(x_370, x_371);
if (x_373 == 0)
{
x_346 = x_370;
x_347 = x_372;
goto block_369;
}
else
{
lean_dec(x_370);
x_346 = x_371;
x_347 = x_372;
goto block_369;
}
block_369:
{
lean_object* x_348; size_t x_349; size_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_348 = l_Array_toSubarray___redArg(x_345, x_346, x_347);
x_349 = lean_array_size(x_342);
x_350 = 0;
x_351 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_342, x_349, x_350, x_348, x_3, x_341);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec_ref(x_351);
lean_inc(x_6);
x_353 = l_Lean_Compiler_LCNF_Simp_simp(x_343, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_352);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec_ref(x_353);
x_356 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_342, x_6, x_355);
lean_dec(x_6);
lean_dec_ref(x_342);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_358 = x_356;
} else {
 lean_dec_ref(x_356);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_359 = lean_alloc_ctor(1, 1, 0);
} else {
 x_359 = x_331;
}
lean_ctor_set(x_359, 0, x_354);
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_357);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_354);
lean_dec(x_331);
x_361 = lean_ctor_get(x_356, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_356, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_363 = x_356;
} else {
 lean_dec_ref(x_356);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_361);
lean_ctor_set(x_364, 1, x_362);
return x_364;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec_ref(x_342);
lean_dec(x_331);
lean_dec(x_6);
x_365 = lean_ctor_get(x_353, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_353, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_367 = x_353;
} else {
 lean_dec_ref(x_353);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; 
x_374 = lean_ctor_get(x_340, 1);
lean_inc(x_374);
lean_dec_ref(x_340);
x_375 = lean_ctor_get(x_334, 1);
lean_inc_ref(x_375);
x_376 = lean_ctor_get(x_334, 2);
lean_inc_ref(x_376);
lean_dec_ref(x_334);
x_377 = lean_ctor_get(x_330, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 x_378 = x_330;
} else {
 lean_dec_ref(x_330);
 x_378 = lean_box(0);
}
x_379 = lean_unsigned_to_nat(0u);
x_380 = lean_nat_dec_eq(x_377, x_379);
if (x_380 == 1)
{
lean_object* x_381; 
lean_dec(x_378);
lean_dec(x_377);
lean_dec_ref(x_375);
lean_dec(x_336);
x_381 = l_Lean_Compiler_LCNF_Simp_simp(x_376, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_374);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_384 = x_381;
} else {
 lean_dec_ref(x_381);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_385 = lean_alloc_ctor(1, 1, 0);
} else {
 x_385 = x_331;
}
lean_ctor_set(x_385, 0, x_382);
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_383);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_331);
x_387 = lean_ctor_get(x_381, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_381, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_389 = x_381;
} else {
 lean_dec_ref(x_381);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_388);
return x_390;
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_391 = lean_unsigned_to_nat(1u);
x_392 = lean_nat_sub(x_377, x_391);
lean_dec(x_377);
if (lean_is_scalar(x_378)) {
 x_393 = lean_alloc_ctor(0, 1, 0);
} else {
 x_393 = x_378;
 lean_ctor_set_tag(x_393, 0);
}
lean_ctor_set(x_393, 0, x_392);
x_394 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_394, 0, x_393);
x_395 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_396 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_394, x_395, x_5, x_6, x_7, x_8, x_374);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec_ref(x_396);
x_399 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_400 = lean_array_get_borrowed(x_399, x_375, x_379);
x_401 = lean_ctor_get(x_400, 0);
x_402 = lean_ctor_get(x_397, 0);
lean_inc(x_402);
lean_inc(x_401);
x_403 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_401, x_402, x_3, x_6, x_7, x_8, x_398);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec_ref(x_403);
lean_inc(x_6);
x_405 = l_Lean_Compiler_LCNF_Simp_simp(x_376, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_404);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec_ref(x_405);
x_408 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_375, x_6, x_407);
lean_dec(x_6);
lean_dec_ref(x_375);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_410 = x_408;
} else {
 lean_dec_ref(x_408);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_411 = x_336;
}
lean_ctor_set(x_411, 0, x_397);
lean_ctor_set(x_411, 1, x_406);
if (lean_is_scalar(x_331)) {
 x_412 = lean_alloc_ctor(1, 1, 0);
} else {
 x_412 = x_331;
}
lean_ctor_set(x_412, 0, x_411);
if (lean_is_scalar(x_410)) {
 x_413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_413 = x_410;
}
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_409);
return x_413;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_406);
lean_dec(x_397);
lean_dec(x_336);
lean_dec(x_331);
x_414 = lean_ctor_get(x_408, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_408, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_416 = x_408;
} else {
 lean_dec_ref(x_408);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_397);
lean_dec_ref(x_375);
lean_dec(x_336);
lean_dec(x_331);
lean_dec(x_6);
x_418 = lean_ctor_get(x_405, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_405, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_420 = x_405;
} else {
 lean_dec_ref(x_405);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_397);
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec(x_336);
lean_dec(x_331);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_422 = lean_ctor_get(x_403, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_403, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_424 = x_403;
} else {
 lean_dec_ref(x_403);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec(x_336);
lean_dec(x_331);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_426 = lean_ctor_get(x_396, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_396, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_428 = x_396;
} else {
 lean_dec_ref(x_396);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_426);
lean_ctor_set(x_429, 1, x_427);
return x_429;
}
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_336);
lean_dec(x_330);
x_430 = lean_ctor_get(x_340, 1);
lean_inc(x_430);
lean_dec_ref(x_340);
x_431 = lean_ctor_get(x_334, 0);
lean_inc_ref(x_431);
lean_dec_ref(x_334);
x_432 = l_Lean_Compiler_LCNF_Simp_simp(x_431, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_430);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_435 = x_432;
} else {
 lean_dec_ref(x_432);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_436 = lean_alloc_ctor(1, 1, 0);
} else {
 x_436 = x_331;
}
lean_ctor_set(x_436, 0, x_433);
if (lean_is_scalar(x_435)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_435;
}
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_434);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_331);
x_438 = lean_ctor_get(x_432, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_432, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_440 = x_432;
} else {
 lean_dec_ref(x_432);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_336);
lean_dec(x_334);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_442 = lean_ctor_get(x_340, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_340, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_444 = x_340;
} else {
 lean_dec_ref(x_340);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_336);
lean_dec(x_334);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_446 = lean_ctor_get(x_338, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_338, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_448 = x_338;
} else {
 lean_dec_ref(x_338);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_450 = lean_ctor_get(x_323, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_323, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_452 = x_323;
} else {
 lean_dec_ref(x_323);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 2, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_450);
lean_ctor_set(x_453, 1, x_451);
return x_453;
}
}
}
else
{
lean_object* x_454; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_454 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_454) == 0)
{
uint8_t x_455; 
x_455 = !lean_is_exclusive(x_454);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_ctor_get(x_454, 0);
x_457 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_454, 0, x_457);
return x_454;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_458 = lean_ctor_get(x_454, 0);
x_459 = lean_ctor_get(x_454, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_454);
x_460 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_460, 0, x_458);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_459);
return x_461;
}
}
else
{
uint8_t x_462; 
x_462 = !lean_is_exclusive(x_454);
if (x_462 == 0)
{
return x_454;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_454, 0);
x_464 = lean_ctor_get(x_454, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_454);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
return x_465;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_array_fget_borrowed(x_3, x_2);
x_11 = lean_ctor_get(x_10, 2);
x_12 = lean_st_ref_get(x_4, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
lean_inc_ref(x_11);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_15, x_1, x_11);
lean_dec_ref(x_15);
lean_inc_ref(x_10);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(x_10, x_16, x_5, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ptr_addr(x_10);
x_21 = lean_ptr_addr(x_18);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
x_25 = lean_array_fset(x_3, x_2, x_18);
lean_dec(x_2);
x_2 = x_24;
x_3 = x_25;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_18);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_2, x_27);
lean_dec(x_2);
x_2 = x_28;
x_6 = x_19;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_1, x_2, x_3, x_5, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_1, x_11, x_2, x_4, x_7, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = 0;
lean_inc_ref(x_13);
x_17 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_16, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_inc(x_6);
lean_inc_ref(x_15);
x_20 = l_Lean_Compiler_LCNF_Simp_simp(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_23);
lean_dec(x_11);
lean_inc_ref(x_14);
x_24 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_23, x_16, x_14);
lean_dec_ref(x_23);
x_25 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_24, x_18, x_21, x_6, x_22);
lean_dec(x_6);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_ConstantFold(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_ConstantFold(builtin, lean_io_mk_world());
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
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3);
l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0 = _init_l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0);
l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__0);
l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__1);
l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__2);
l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3);
l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
