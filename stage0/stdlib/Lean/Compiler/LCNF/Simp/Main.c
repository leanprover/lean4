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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object*, size_t, size_t, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_hasLocalInst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___boxed(lean_object**);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__0;
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__2;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3;
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqLetValue_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getCode(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0;
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__1;
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_3, x_4, x_5, x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_35 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_21, x_23, x_34);
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
x_59 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_45, x_47, x_58);
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
x_89 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_73, x_76, x_88);
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
x_122 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_105, x_108, x_121);
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
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_1, x_6, x_7, x_13, x_14, x_15, x_16);
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
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_10, x_18, x_19, x_17);
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
x_34 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_28, x_33, x_31, x_5, x_6, x_7, x_8);
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
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_1, x_6, x_7, x_4);
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
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_9 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
x_52 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_50, x_51, x_49);
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
x_92 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_90, x_91, x_89);
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
x_137 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_135, x_136, x_134);
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
x_190 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_188, x_189, x_187);
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
x_253 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_251, x_252, x_250);
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
x_323 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_321, x_322, x_320);
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
x_406 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_404, x_405, x_403);
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
x_210 = l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_208, x_203, x_205);
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
x_216 = l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_214, x_203, x_205);
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
x_408 = l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_405, x_399, x_401);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_1, x_2, x_4, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1, x_2, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1, x_2, x_3, x_4, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_2, x_3, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_75 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_31, x_73, x_74, x_11);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_75 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_31, x_73, x_74, x_11);
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
x_25 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(x_1, x_2, x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(x_1, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1, x_2, x_3, x_4, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_2, x_3, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_14 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_23; uint8_t x_24; lean_object* x_29; lean_object* x_50; lean_object* x_51; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_50 = lean_ctor_get(x_4, 0);
x_51 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_50, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_54 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(x_4, x_7, x_10);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_15);
return x_54;
}
else
{
lean_object* x_57; 
lean_dec(x_54);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_15);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_15);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
if (x_3 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_29 = lean_box(0);
goto block_49;
}
else
{
lean_object* x_61; 
lean_inc_ref(x_4);
x_61 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_29 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_62; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
return x_61;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_16);
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
x_65 = !lean_is_exclusive(x_51);
if (x_65 == 0)
{
return x_51;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_51, 0);
lean_inc(x_66);
lean_dec(x_51);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
block_22:
{
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_2);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_15);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_15);
lean_dec_ref(x_4);
if (lean_is_scalar(x_16)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_16;
}
lean_ctor_set(x_21, 0, x_2);
return x_21;
}
}
block_28:
{
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_2);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_15);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_15);
lean_dec_ref(x_4);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_2);
return x_27;
}
}
block_49:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ptr_addr(x_31);
x_33 = lean_ptr_addr(x_15);
x_34 = lean_usize_dec_eq(x_32, x_33);
if (x_34 == 0)
{
x_17 = lean_box(0);
x_18 = x_34;
goto block_22;
}
else
{
size_t x_35; size_t x_36; uint8_t x_37; 
x_35 = lean_ptr_addr(x_30);
x_36 = lean_ptr_addr(x_4);
x_37 = lean_usize_dec_eq(x_35, x_36);
x_17 = lean_box(0);
x_18 = x_37;
goto block_22;
}
}
case 2:
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; uint8_t x_42; 
lean_dec(x_16);
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
x_40 = lean_ptr_addr(x_39);
x_41 = lean_ptr_addr(x_15);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
x_23 = lean_box(0);
x_24 = x_42;
goto block_28;
}
else
{
size_t x_43; size_t x_44; uint8_t x_45; 
x_43 = lean_ptr_addr(x_38);
x_44 = lean_ptr_addr(x_4);
x_45 = lean_usize_dec_eq(x_43, x_44);
x_23 = lean_box(0);
x_24 = x_45;
goto block_28;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_46 = l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3;
x_47 = l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
x_38 = lean_ctor_get(x_7, 2);
x_39 = lean_ctor_get(x_7, 3);
x_40 = lean_ctor_get(x_7, 4);
x_41 = lean_ctor_get(x_7, 5);
x_42 = lean_ctor_get(x_7, 6);
x_43 = lean_ctor_get(x_7, 7);
x_44 = lean_ctor_get(x_7, 8);
x_45 = lean_ctor_get(x_7, 9);
x_46 = lean_ctor_get(x_7, 10);
x_47 = lean_ctor_get(x_7, 11);
x_48 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_49 = lean_ctor_get(x_7, 12);
x_50 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_51 = lean_ctor_get(x_7, 13);
x_52 = lean_nat_dec_eq(x_39, x_40);
if (x_52 == 0)
{
uint8_t x_53; 
lean_inc_ref(x_51);
lean_inc(x_49);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_36);
x_53 = !lean_is_exclusive(x_7);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_54 = lean_ctor_get(x_7, 13);
lean_dec(x_54);
x_55 = lean_ctor_get(x_7, 12);
lean_dec(x_55);
x_56 = lean_ctor_get(x_7, 11);
lean_dec(x_56);
x_57 = lean_ctor_get(x_7, 10);
lean_dec(x_57);
x_58 = lean_ctor_get(x_7, 9);
lean_dec(x_58);
x_59 = lean_ctor_get(x_7, 8);
lean_dec(x_59);
x_60 = lean_ctor_get(x_7, 7);
lean_dec(x_60);
x_61 = lean_ctor_get(x_7, 6);
lean_dec(x_61);
x_62 = lean_ctor_get(x_7, 5);
lean_dec(x_62);
x_63 = lean_ctor_get(x_7, 4);
lean_dec(x_63);
x_64 = lean_ctor_get(x_7, 3);
lean_dec(x_64);
x_65 = lean_ctor_get(x_7, 2);
lean_dec(x_65);
x_66 = lean_ctor_get(x_7, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_7, 0);
lean_dec(x_67);
x_68 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_119; lean_object* x_120; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_add(x_39, x_119);
lean_dec(x_39);
lean_ctor_set(x_7, 3, x_120);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_276; 
lean_free_object(x_68);
x_121 = lean_ctor_get(x_1, 0);
x_122 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_121);
x_276 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_52, x_121, x_3, x_6);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_311; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
lean_dec_ref(x_276);
x_311 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_121, x_277);
if (x_311 == 0)
{
goto block_310;
}
else
{
if (x_52 == 0)
{
x_278 = x_2;
x_279 = x_3;
x_280 = x_4;
x_281 = x_5;
x_282 = x_6;
x_283 = x_7;
x_284 = x_8;
x_285 = lean_box(0);
goto block_305;
}
else
{
goto block_310;
}
}
block_305:
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_277, 2);
x_287 = lean_ctor_get(x_277, 3);
lean_inc(x_284);
lean_inc_ref(x_283);
lean_inc(x_282);
lean_inc_ref(x_281);
lean_inc_ref(x_280);
lean_inc(x_287);
x_288 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_287, x_278, x_280, x_281, x_282, x_283, x_284);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec_ref(x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_inc(x_287);
lean_inc_ref(x_286);
x_261 = x_277;
x_262 = x_286;
x_263 = x_287;
x_264 = x_278;
x_265 = x_279;
x_266 = x_280;
x_267 = x_281;
x_268 = x_282;
x_269 = x_283;
x_270 = x_284;
x_271 = lean_box(0);
goto block_275;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
x_291 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_279);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; 
lean_dec_ref(x_291);
x_292 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_277, x_290, x_282);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec_ref(x_292);
x_294 = lean_ctor_get(x_293, 2);
lean_inc_ref(x_294);
x_295 = lean_ctor_get(x_293, 3);
lean_inc(x_295);
x_261 = x_293;
x_262 = x_294;
x_263 = x_295;
x_264 = x_278;
x_265 = x_279;
x_266 = x_280;
x_267 = x_281;
x_268 = x_282;
x_269 = x_283;
x_270 = x_284;
x_271 = lean_box(0);
goto block_275;
}
else
{
uint8_t x_296; 
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec_ref(x_1);
x_296 = !lean_is_exclusive(x_292);
if (x_296 == 0)
{
return x_292;
}
else
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_292, 0);
lean_inc(x_297);
lean_dec(x_292);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_297);
return x_298;
}
}
}
else
{
uint8_t x_299; 
lean_dec(x_290);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec_ref(x_1);
x_299 = !lean_is_exclusive(x_291);
if (x_299 == 0)
{
return x_291;
}
else
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_291, 0);
lean_inc(x_300);
lean_dec(x_291);
x_301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_301, 0, x_300);
return x_301;
}
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec_ref(x_1);
x_302 = !lean_is_exclusive(x_288);
if (x_302 == 0)
{
return x_288;
}
else
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_288, 0);
lean_inc(x_303);
lean_dec(x_288);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
}
}
block_310:
{
lean_object* x_306; 
x_306 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_306) == 0)
{
lean_dec_ref(x_306);
x_278 = x_2;
x_279 = x_3;
x_280 = x_4;
x_281 = x_5;
x_282 = x_6;
x_283 = x_7;
x_284 = x_8;
x_285 = lean_box(0);
goto block_305;
}
else
{
uint8_t x_307; 
lean_dec(x_277);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_307 = !lean_is_exclusive(x_306);
if (x_307 == 0)
{
return x_306;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_306, 0);
lean_inc(x_308);
lean_dec(x_306);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
return x_309;
}
}
}
}
else
{
uint8_t x_312; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_312 = !lean_is_exclusive(x_276);
if (x_312 == 0)
{
return x_276;
}
else
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_276, 0);
lean_inc(x_313);
lean_dec(x_276);
x_314 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_314, 0, x_313);
return x_314;
}
}
block_260:
{
if (x_132 == 0)
{
lean_object* x_133; 
lean_inc(x_123);
lean_inc_ref(x_131);
lean_inc(x_125);
lean_inc_ref(x_127);
lean_inc_ref(x_124);
x_133 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_124, x_127, x_125, x_131, x_123);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
lean_inc(x_123);
lean_inc_ref(x_131);
lean_inc(x_125);
lean_inc_ref(x_127);
lean_inc_ref(x_124);
x_135 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_124, x_130, x_129, x_127, x_125, x_131, x_123);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_124, 0);
x_138 = lean_ctor_get(x_124, 3);
x_139 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
lean_inc(x_123);
lean_inc_ref(x_131);
lean_inc(x_125);
lean_inc_ref(x_127);
lean_inc_ref(x_128);
lean_inc(x_129);
lean_inc_ref(x_130);
lean_inc_ref(x_122);
lean_inc_ref(x_124);
x_141 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_124, x_122, x_130, x_129, x_128, x_127, x_125, x_131, x_123);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
lean_inc(x_123);
lean_inc_ref(x_131);
lean_inc(x_125);
lean_inc_ref(x_127);
lean_inc_ref(x_128);
lean_inc(x_129);
lean_inc_ref(x_130);
lean_inc(x_138);
x_143 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_138, x_130, x_129, x_128, x_127, x_125, x_131, x_123);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
lean_inc(x_123);
lean_inc_ref(x_131);
lean_inc(x_125);
lean_inc_ref(x_127);
lean_inc_ref(x_128);
lean_inc(x_129);
lean_inc_ref(x_130);
lean_inc_ref(x_122);
x_145 = l_Lean_Compiler_LCNF_Simp_simp(x_122, x_130, x_129, x_128, x_127, x_125, x_131, x_123);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_137, x_129);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_123);
lean_dec_ref(x_1);
x_150 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_124, x_129, x_125);
lean_dec(x_125);
lean_dec(x_129);
lean_dec_ref(x_124);
if (lean_obj_tag(x_150) == 0)
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_150, 0);
lean_dec(x_152);
lean_ctor_set(x_150, 0, x_146);
return x_150;
}
else
{
lean_object* x_153; 
lean_dec(x_150);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_146);
return x_153;
}
}
else
{
uint8_t x_154; 
lean_dec(x_146);
x_154 = !lean_is_exclusive(x_150);
if (x_154 == 0)
{
return x_150;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_150, 0);
lean_inc(x_155);
lean_dec(x_150);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
}
else
{
lean_object* x_157; 
lean_inc_ref(x_124);
x_157 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_124, x_130, x_129, x_128, x_127, x_125, x_131, x_123);
lean_dec(x_123);
lean_dec_ref(x_131);
lean_dec(x_125);
lean_dec_ref(x_127);
lean_dec_ref(x_128);
lean_dec(x_129);
lean_dec_ref(x_130);
if (lean_obj_tag(x_157) == 0)
{
size_t x_158; size_t x_159; uint8_t x_160; 
lean_dec_ref(x_157);
x_158 = lean_ptr_addr(x_122);
x_159 = lean_ptr_addr(x_146);
x_160 = lean_usize_dec_eq(x_158, x_159);
if (x_160 == 0)
{
x_10 = x_124;
x_11 = lean_box(0);
x_12 = x_146;
x_13 = x_160;
goto block_17;
}
else
{
size_t x_161; size_t x_162; uint8_t x_163; 
x_161 = lean_ptr_addr(x_121);
x_162 = lean_ptr_addr(x_124);
x_163 = lean_usize_dec_eq(x_161, x_162);
x_10 = x_124;
x_11 = lean_box(0);
x_12 = x_146;
x_13 = x_163;
goto block_17;
}
}
else
{
uint8_t x_164; 
lean_dec(x_146);
lean_dec_ref(x_124);
lean_dec_ref(x_1);
x_164 = !lean_is_exclusive(x_157);
if (x_164 == 0)
{
return x_157;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_157, 0);
lean_inc(x_165);
lean_dec(x_157);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_146);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_1);
x_167 = !lean_is_exclusive(x_147);
if (x_167 == 0)
{
return x_147;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_147, 0);
lean_inc(x_168);
lean_dec(x_147);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
}
}
else
{
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_1);
return x_145;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_inc_ref(x_122);
lean_dec_ref(x_1);
x_170 = lean_ctor_get(x_144, 0);
lean_inc(x_170);
lean_dec_ref(x_144);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
lean_inc(x_137);
x_173 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_137, x_172, x_129, x_125, x_131, x_123);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
lean_dec_ref(x_173);
x_174 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_124, x_129, x_125);
lean_dec_ref(x_124);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
lean_dec_ref(x_174);
lean_inc(x_123);
lean_inc_ref(x_131);
lean_inc(x_125);
lean_inc_ref(x_127);
lean_inc_ref(x_128);
lean_inc(x_129);
lean_inc_ref(x_130);
x_175 = l_Lean_Compiler_LCNF_Simp_simp(x_122, x_130, x_129, x_128, x_127, x_125, x_131, x_123);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_171, x_176, x_130, x_129, x_128, x_127, x_125, x_131, x_123);
lean_dec(x_123);
lean_dec_ref(x_131);
lean_dec(x_125);
lean_dec_ref(x_127);
lean_dec_ref(x_128);
lean_dec(x_129);
lean_dec_ref(x_130);
lean_dec(x_171);
return x_177;
}
else
{
lean_dec(x_171);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec(x_123);
return x_175;
}
}
else
{
uint8_t x_178; 
lean_dec(x_171);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec(x_123);
lean_dec_ref(x_122);
x_178 = !lean_is_exclusive(x_174);
if (x_178 == 0)
{
return x_174;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_174, 0);
lean_inc(x_179);
lean_dec(x_174);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_171);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
x_181 = !lean_is_exclusive(x_173);
if (x_181 == 0)
{
return x_173;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_173, 0);
lean_inc(x_182);
lean_dec(x_173);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
}
}
}
else
{
uint8_t x_184; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_1);
x_184 = !lean_is_exclusive(x_143);
if (x_184 == 0)
{
return x_143;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_143, 0);
lean_inc(x_185);
lean_dec(x_143);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_123);
lean_dec_ref(x_1);
x_187 = lean_ctor_get(x_142, 0);
lean_inc(x_187);
lean_dec_ref(x_142);
x_188 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_124, x_129, x_125);
lean_dec(x_125);
lean_dec(x_129);
lean_dec_ref(x_124);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_188, 0);
lean_dec(x_190);
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
else
{
lean_object* x_191; 
lean_dec(x_188);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_187);
return x_191;
}
}
else
{
uint8_t x_192; 
lean_dec(x_187);
x_192 = !lean_is_exclusive(x_188);
if (x_192 == 0)
{
return x_188;
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_188, 0);
lean_inc(x_193);
lean_dec(x_188);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
return x_194;
}
}
}
}
else
{
uint8_t x_195; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_1);
x_195 = !lean_is_exclusive(x_141);
if (x_195 == 0)
{
return x_141;
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_141, 0);
lean_inc(x_196);
lean_dec(x_141);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_inc_ref(x_122);
lean_dec_ref(x_1);
x_198 = lean_ctor_get(x_140, 0);
lean_inc(x_198);
lean_dec_ref(x_140);
lean_inc(x_137);
x_199 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_137, x_198, x_129, x_125, x_131, x_123);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; 
lean_dec_ref(x_199);
x_200 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_124, x_129, x_125);
lean_dec_ref(x_124);
if (lean_obj_tag(x_200) == 0)
{
lean_dec_ref(x_200);
x_1 = x_122;
x_2 = x_130;
x_3 = x_129;
x_4 = x_128;
x_5 = x_127;
x_6 = x_125;
x_7 = x_131;
x_8 = x_123;
goto _start;
}
else
{
uint8_t x_202; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec(x_123);
lean_dec_ref(x_122);
x_202 = !lean_is_exclusive(x_200);
if (x_202 == 0)
{
return x_200;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_200, 0);
lean_inc(x_203);
lean_dec(x_200);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
x_205 = !lean_is_exclusive(x_199);
if (x_205 == 0)
{
return x_199;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_199, 0);
lean_inc(x_206);
lean_dec(x_199);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
}
}
}
else
{
uint8_t x_208; 
lean_dec_ref(x_124);
lean_inc_ref(x_122);
x_208 = !lean_is_exclusive(x_1);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_1, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_1, 0);
lean_dec(x_210);
x_211 = lean_ctor_get(x_136, 0);
lean_inc(x_211);
lean_dec_ref(x_136);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_211);
x_2 = x_130;
x_3 = x_129;
x_4 = x_128;
x_5 = x_127;
x_6 = x_125;
x_7 = x_131;
x_8 = x_123;
goto _start;
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_1);
x_213 = lean_ctor_get(x_136, 0);
lean_inc(x_213);
lean_dec_ref(x_136);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_122);
x_1 = x_214;
x_2 = x_130;
x_3 = x_129;
x_4 = x_128;
x_5 = x_127;
x_6 = x_125;
x_7 = x_131;
x_8 = x_123;
goto _start;
}
}
}
else
{
uint8_t x_216; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_1);
x_216 = !lean_is_exclusive(x_135);
if (x_216 == 0)
{
return x_135;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_135, 0);
lean_inc(x_217);
lean_dec(x_135);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec_ref(x_124);
lean_inc_ref(x_122);
lean_dec_ref(x_1);
x_219 = lean_ctor_get(x_134, 0);
lean_inc(x_219);
lean_dec_ref(x_134);
x_220 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_129);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
lean_dec_ref(x_220);
lean_inc(x_123);
lean_inc_ref(x_131);
lean_inc(x_125);
lean_inc_ref(x_127);
lean_inc_ref(x_128);
lean_inc(x_129);
lean_inc_ref(x_130);
x_221 = l_Lean_Compiler_LCNF_Simp_simp(x_122, x_130, x_129, x_128, x_127, x_125, x_131, x_123);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
x_223 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_219, x_222, x_130, x_129, x_128, x_127, x_125, x_131, x_123);
lean_dec(x_123);
lean_dec_ref(x_131);
lean_dec(x_125);
lean_dec_ref(x_127);
lean_dec_ref(x_128);
lean_dec(x_129);
lean_dec_ref(x_130);
lean_dec(x_219);
return x_223;
}
else
{
lean_dec(x_219);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec(x_123);
return x_221;
}
}
else
{
uint8_t x_224; 
lean_dec(x_219);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec(x_123);
lean_dec_ref(x_122);
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
}
else
{
uint8_t x_227; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_1);
x_227 = !lean_is_exclusive(x_133);
if (x_227 == 0)
{
return x_133;
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_133, 0);
lean_inc(x_228);
lean_dec(x_133);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_228);
return x_229;
}
}
}
else
{
lean_object* x_230; uint8_t x_231; 
lean_inc_ref(x_122);
lean_dec_ref(x_1);
x_230 = lean_st_ref_take(x_129);
x_231 = !lean_is_exclusive(x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_232 = lean_ctor_get(x_124, 0);
x_233 = lean_ctor_get(x_230, 0);
x_234 = lean_box(0);
lean_inc(x_232);
x_235 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_233, x_232, x_234);
lean_ctor_set(x_230, 0, x_235);
x_236 = lean_st_ref_set(x_129, x_230);
x_237 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_124, x_129, x_125);
lean_dec_ref(x_124);
if (lean_obj_tag(x_237) == 0)
{
lean_dec_ref(x_237);
x_1 = x_122;
x_2 = x_130;
x_3 = x_129;
x_4 = x_128;
x_5 = x_127;
x_6 = x_125;
x_7 = x_131;
x_8 = x_123;
goto _start;
}
else
{
uint8_t x_239; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec(x_123);
lean_dec_ref(x_122);
x_239 = !lean_is_exclusive(x_237);
if (x_239 == 0)
{
return x_237;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_237, 0);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_240);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_242 = lean_ctor_get(x_124, 0);
x_243 = lean_ctor_get(x_230, 0);
x_244 = lean_ctor_get(x_230, 1);
x_245 = lean_ctor_get(x_230, 2);
x_246 = lean_ctor_get(x_230, 3);
x_247 = lean_ctor_get_uint8(x_230, sizeof(void*)*7);
x_248 = lean_ctor_get(x_230, 4);
x_249 = lean_ctor_get(x_230, 5);
x_250 = lean_ctor_get(x_230, 6);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_230);
x_251 = lean_box(0);
lean_inc(x_242);
x_252 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_243, x_242, x_251);
x_253 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_244);
lean_ctor_set(x_253, 2, x_245);
lean_ctor_set(x_253, 3, x_246);
lean_ctor_set(x_253, 4, x_248);
lean_ctor_set(x_253, 5, x_249);
lean_ctor_set(x_253, 6, x_250);
lean_ctor_set_uint8(x_253, sizeof(void*)*7, x_247);
x_254 = lean_st_ref_set(x_129, x_253);
x_255 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_124, x_129, x_125);
lean_dec_ref(x_124);
if (lean_obj_tag(x_255) == 0)
{
lean_dec_ref(x_255);
x_1 = x_122;
x_2 = x_130;
x_3 = x_129;
x_4 = x_128;
x_5 = x_127;
x_6 = x_125;
x_7 = x_131;
x_8 = x_123;
goto _start;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
lean_dec(x_125);
lean_dec(x_123);
lean_dec_ref(x_122);
x_257 = lean_ctor_get(x_255, 0);
lean_inc(x_257);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_258 = x_255;
} else {
 lean_dec_ref(x_255);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 1, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_257);
return x_259;
}
}
}
}
block_275:
{
uint8_t x_272; 
x_272 = l_Lean_Expr_isErased(x_262);
lean_dec_ref(x_262);
if (x_272 == 0)
{
lean_dec(x_263);
x_123 = x_270;
x_124 = x_261;
x_125 = x_268;
x_126 = lean_box(0);
x_127 = x_267;
x_128 = x_266;
x_129 = x_265;
x_130 = x_264;
x_131 = x_269;
x_132 = x_52;
goto block_260;
}
else
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_box(1);
x_274 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_263, x_273);
lean_dec(x_263);
if (x_274 == 0)
{
x_123 = x_270;
x_124 = x_261;
x_125 = x_268;
x_126 = lean_box(0);
x_127 = x_267;
x_128 = x_266;
x_129 = x_265;
x_130 = x_264;
x_131 = x_269;
x_132 = x_272;
goto block_260;
}
else
{
x_123 = x_270;
x_124 = x_261;
x_125 = x_268;
x_126 = lean_box(0);
x_127 = x_267;
x_128 = x_266;
x_129 = x_265;
x_130 = x_264;
x_131 = x_269;
x_132 = x_52;
goto block_260;
}
}
}
}
case 3:
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_free_object(x_68);
x_315 = lean_ctor_get(x_1, 0);
x_316 = lean_ctor_get(x_1, 1);
x_317 = lean_st_ref_get(x_3);
x_318 = lean_ctor_get(x_317, 0);
lean_inc_ref(x_318);
lean_dec_ref(x_317);
lean_inc(x_315);
x_319 = l_Lean_Compiler_LCNF_normFVarImp(x_318, x_315, x_52);
lean_dec_ref(x_318);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_334; lean_object* x_340; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
lean_dec_ref(x_319);
lean_inc_ref(x_316);
x_321 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_52, x_316, x_3);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 x_323 = x_321;
} else {
 lean_dec_ref(x_321);
 x_323 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_322);
x_340 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_320, x_322, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
lean_dec_ref(x_340);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_320);
x_342 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_320, x_3);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; uint8_t x_345; 
lean_dec_ref(x_342);
x_343 = lean_unsigned_to_nat(0u);
x_344 = lean_array_get_size(x_322);
x_345 = lean_nat_dec_lt(x_343, x_344);
if (x_345 == 0)
{
lean_dec(x_344);
lean_dec(x_3);
x_334 = lean_box(0);
goto block_339;
}
else
{
uint8_t x_346; 
x_346 = lean_nat_dec_le(x_344, x_344);
if (x_346 == 0)
{
lean_dec(x_344);
lean_dec(x_3);
x_334 = lean_box(0);
goto block_339;
}
else
{
lean_object* x_347; size_t x_348; size_t x_349; lean_object* x_350; 
x_347 = lean_box(0);
x_348 = 0;
x_349 = lean_usize_of_nat(x_344);
lean_dec(x_344);
x_350 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_322, x_348, x_349, x_347, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_350) == 0)
{
lean_dec_ref(x_350);
x_334 = lean_box(0);
goto block_339;
}
else
{
uint8_t x_351; 
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_320);
lean_dec_ref(x_1);
x_351 = !lean_is_exclusive(x_350);
if (x_351 == 0)
{
return x_350;
}
else
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_ctor_get(x_350, 0);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_353, 0, x_352);
return x_353;
}
}
}
}
}
else
{
uint8_t x_354; 
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_320);
lean_dec(x_3);
lean_dec_ref(x_1);
x_354 = !lean_is_exclusive(x_342);
if (x_354 == 0)
{
return x_342;
}
else
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_342, 0);
lean_inc(x_355);
lean_dec(x_342);
x_356 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_356, 0, x_355);
return x_356;
}
}
}
else
{
lean_object* x_357; 
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_320);
lean_dec_ref(x_1);
x_357 = lean_ctor_get(x_341, 0);
lean_inc(x_357);
lean_dec_ref(x_341);
x_1 = x_357;
goto _start;
}
}
else
{
uint8_t x_359; 
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_320);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_359 = !lean_is_exclusive(x_340);
if (x_359 == 0)
{
return x_340;
}
else
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_340, 0);
lean_inc(x_360);
lean_dec(x_340);
x_361 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_361, 0, x_360);
return x_361;
}
}
block_333:
{
if (x_325 == 0)
{
uint8_t x_326; 
x_326 = !lean_is_exclusive(x_1);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_1, 1);
lean_dec(x_327);
x_328 = lean_ctor_get(x_1, 0);
lean_dec(x_328);
lean_ctor_set(x_1, 1, x_322);
lean_ctor_set(x_1, 0, x_320);
if (lean_is_scalar(x_323)) {
 x_329 = lean_alloc_ctor(0, 1, 0);
} else {
 x_329 = x_323;
}
lean_ctor_set(x_329, 0, x_1);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_1);
x_330 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_330, 0, x_320);
lean_ctor_set(x_330, 1, x_322);
if (lean_is_scalar(x_323)) {
 x_331 = lean_alloc_ctor(0, 1, 0);
} else {
 x_331 = x_323;
}
lean_ctor_set(x_331, 0, x_330);
return x_331;
}
}
else
{
lean_object* x_332; 
lean_dec(x_322);
lean_dec(x_320);
if (lean_is_scalar(x_323)) {
 x_332 = lean_alloc_ctor(0, 1, 0);
} else {
 x_332 = x_323;
}
lean_ctor_set(x_332, 0, x_1);
return x_332;
}
}
block_339:
{
uint8_t x_335; 
x_335 = l_Lean_instBEqFVarId_beq(x_315, x_320);
if (x_335 == 0)
{
x_324 = lean_box(0);
x_325 = x_335;
goto block_333;
}
else
{
size_t x_336; size_t x_337; uint8_t x_338; 
x_336 = lean_ptr_addr(x_316);
x_337 = lean_ptr_addr(x_322);
x_338 = lean_usize_dec_eq(x_336, x_337);
x_324 = lean_box(0);
x_325 = x_338;
goto block_333;
}
}
}
else
{
lean_object* x_362; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_362 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_362;
}
}
case 4:
{
lean_object* x_363; lean_object* x_364; 
lean_free_object(x_68);
x_363 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_363);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_363);
x_364 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_363, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_364) == 0)
{
uint8_t x_365; 
x_365 = !lean_is_exclusive(x_364);
if (x_365 == 0)
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_364, 0);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_367 = lean_st_ref_get(x_3);
x_368 = lean_ctor_get(x_363, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_363, 1);
lean_inc_ref(x_369);
x_370 = lean_ctor_get(x_363, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_363, 3);
lean_inc_ref(x_371);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 lean_ctor_release(x_363, 2);
 lean_ctor_release(x_363, 3);
 x_372 = x_363;
} else {
 lean_dec_ref(x_363);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_367, 0);
lean_inc_ref(x_373);
lean_dec_ref(x_367);
lean_inc(x_370);
x_374 = l_Lean_Compiler_LCNF_normFVarImp(x_373, x_370, x_52);
lean_dec_ref(x_373);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_376 = x_374;
} else {
 lean_dec_ref(x_374);
 x_376 = lean_box(0);
}
x_377 = lean_st_ref_get(x_3);
x_378 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_371);
lean_inc(x_375);
x_379 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_375, x_52, x_378, x_371, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_381 = x_379;
} else {
 lean_dec_ref(x_379);
 x_381 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_382 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_380, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_392; uint8_t x_393; lean_object* x_397; lean_object* x_398; lean_object* x_410; uint8_t x_411; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 x_384 = x_382;
} else {
 lean_dec_ref(x_382);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_377, 0);
lean_inc_ref(x_385);
lean_dec_ref(x_377);
lean_inc_ref(x_369);
x_386 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_385, x_52, x_369);
lean_dec_ref(x_385);
x_410 = lean_array_get_size(x_383);
x_411 = lean_nat_dec_eq(x_410, x_119);
lean_dec(x_410);
if (x_411 == 0)
{
lean_free_object(x_364);
lean_dec(x_6);
x_397 = x_3;
x_398 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_412; 
x_412 = lean_array_fget_borrowed(x_383, x_378);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_424; lean_object* x_425; uint8_t x_436; lean_object* x_437; uint8_t x_439; 
lean_free_object(x_364);
x_413 = lean_ctor_get(x_412, 1);
x_414 = lean_ctor_get(x_412, 2);
x_424 = lean_array_get_size(x_413);
x_439 = lean_nat_dec_lt(x_378, x_424);
if (x_439 == 0)
{
x_436 = x_52;
x_437 = lean_box(0);
goto block_438;
}
else
{
if (x_439 == 0)
{
x_436 = x_52;
x_437 = lean_box(0);
goto block_438;
}
else
{
size_t x_440; size_t x_441; lean_object* x_442; 
x_440 = 0;
x_441 = lean_usize_of_nat(x_424);
x_442 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_413, x_440, x_441, x_3);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; uint8_t x_444; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
lean_dec_ref(x_442);
x_444 = lean_unbox(x_443);
lean_dec(x_443);
x_436 = x_444;
x_437 = lean_box(0);
goto block_438;
}
else
{
uint8_t x_445; 
lean_dec(x_424);
lean_dec_ref(x_386);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_445 = !lean_is_exclusive(x_442);
if (x_445 == 0)
{
return x_442;
}
else
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_ctor_get(x_442, 0);
lean_inc(x_446);
lean_dec(x_442);
x_447 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_447, 0, x_446);
return x_447;
}
}
}
}
block_423:
{
lean_object* x_416; 
x_416 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_416) == 0)
{
uint8_t x_417; 
x_417 = !lean_is_exclusive(x_416);
if (x_417 == 0)
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_416, 0);
lean_dec(x_418);
lean_ctor_set(x_416, 0, x_414);
return x_416;
}
else
{
lean_object* x_419; 
lean_dec(x_416);
x_419 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_419, 0, x_414);
return x_419;
}
}
else
{
uint8_t x_420; 
lean_dec_ref(x_414);
x_420 = !lean_is_exclusive(x_416);
if (x_420 == 0)
{
return x_416;
}
else
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_416, 0);
lean_inc(x_421);
lean_dec(x_416);
x_422 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_422, 0, x_421);
return x_422;
}
}
}
block_435:
{
uint8_t x_426; 
x_426 = lean_nat_dec_lt(x_378, x_424);
if (x_426 == 0)
{
lean_dec(x_424);
lean_dec_ref(x_413);
lean_dec(x_6);
x_415 = lean_box(0);
goto block_423;
}
else
{
uint8_t x_427; 
x_427 = lean_nat_dec_le(x_424, x_424);
if (x_427 == 0)
{
lean_dec(x_424);
lean_dec_ref(x_413);
lean_dec(x_6);
x_415 = lean_box(0);
goto block_423;
}
else
{
lean_object* x_428; size_t x_429; size_t x_430; lean_object* x_431; 
x_428 = lean_box(0);
x_429 = 0;
x_430 = lean_usize_of_nat(x_424);
lean_dec(x_424);
x_431 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_413, x_429, x_430, x_428, x_6);
lean_dec(x_6);
lean_dec_ref(x_413);
if (lean_obj_tag(x_431) == 0)
{
lean_dec_ref(x_431);
x_415 = lean_box(0);
goto block_423;
}
else
{
uint8_t x_432; 
lean_dec_ref(x_414);
lean_dec(x_3);
x_432 = !lean_is_exclusive(x_431);
if (x_432 == 0)
{
return x_431;
}
else
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_ctor_get(x_431, 0);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_434, 0, x_433);
return x_434;
}
}
}
}
}
block_438:
{
if (x_436 == 0)
{
lean_inc_ref(x_414);
lean_inc_ref(x_413);
lean_dec_ref(x_386);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_dec_ref(x_1);
x_425 = lean_box(0);
goto block_435;
}
else
{
if (x_52 == 0)
{
lean_dec(x_424);
lean_dec(x_6);
x_397 = x_3;
x_398 = lean_box(0);
goto block_409;
}
else
{
lean_inc_ref(x_414);
lean_inc_ref(x_413);
lean_dec_ref(x_386);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_dec_ref(x_1);
x_425 = lean_box(0);
goto block_435;
}
}
}
}
else
{
lean_object* x_448; 
lean_inc_ref(x_412);
lean_dec_ref(x_386);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_448 = lean_ctor_get(x_412, 0);
lean_inc_ref(x_448);
lean_dec_ref(x_412);
lean_ctor_set(x_364, 0, x_448);
return x_364;
}
}
block_391:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
if (lean_is_scalar(x_372)) {
 x_388 = lean_alloc_ctor(0, 4, 0);
} else {
 x_388 = x_372;
}
lean_ctor_set(x_388, 0, x_368);
lean_ctor_set(x_388, 1, x_386);
lean_ctor_set(x_388, 2, x_375);
lean_ctor_set(x_388, 3, x_383);
if (lean_is_scalar(x_376)) {
 x_389 = lean_alloc_ctor(4, 1, 0);
} else {
 x_389 = x_376;
 lean_ctor_set_tag(x_389, 4);
}
lean_ctor_set(x_389, 0, x_388);
if (lean_is_scalar(x_384)) {
 x_390 = lean_alloc_ctor(0, 1, 0);
} else {
 x_390 = x_384;
}
lean_ctor_set(x_390, 0, x_389);
return x_390;
}
block_396:
{
if (x_393 == 0)
{
lean_dec(x_381);
lean_dec(x_370);
lean_dec_ref(x_1);
x_387 = lean_box(0);
goto block_391;
}
else
{
uint8_t x_394; 
x_394 = l_Lean_instBEqFVarId_beq(x_370, x_375);
lean_dec(x_370);
if (x_394 == 0)
{
lean_dec(x_381);
lean_dec_ref(x_1);
x_387 = lean_box(0);
goto block_391;
}
else
{
lean_object* x_395; 
lean_dec_ref(x_386);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_372);
lean_dec(x_368);
if (lean_is_scalar(x_381)) {
 x_395 = lean_alloc_ctor(0, 1, 0);
} else {
 x_395 = x_381;
}
lean_ctor_set(x_395, 0, x_1);
return x_395;
}
}
}
block_409:
{
lean_object* x_399; 
lean_inc(x_375);
x_399 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_375, x_397);
lean_dec(x_397);
if (lean_obj_tag(x_399) == 0)
{
size_t x_400; size_t x_401; uint8_t x_402; 
lean_dec_ref(x_399);
x_400 = lean_ptr_addr(x_371);
lean_dec_ref(x_371);
x_401 = lean_ptr_addr(x_383);
x_402 = lean_usize_dec_eq(x_400, x_401);
if (x_402 == 0)
{
lean_dec_ref(x_369);
x_392 = lean_box(0);
x_393 = x_402;
goto block_396;
}
else
{
size_t x_403; size_t x_404; uint8_t x_405; 
x_403 = lean_ptr_addr(x_369);
lean_dec_ref(x_369);
x_404 = lean_ptr_addr(x_386);
x_405 = lean_usize_dec_eq(x_403, x_404);
x_392 = lean_box(0);
x_393 = x_405;
goto block_396;
}
}
else
{
uint8_t x_406; 
lean_dec_ref(x_386);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_dec_ref(x_1);
x_406 = !lean_is_exclusive(x_399);
if (x_406 == 0)
{
return x_399;
}
else
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_ctor_get(x_399, 0);
lean_inc(x_407);
lean_dec(x_399);
x_408 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_408, 0, x_407);
return x_408;
}
}
}
}
else
{
uint8_t x_449; 
lean_dec(x_381);
lean_dec_ref(x_377);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_free_object(x_364);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_449 = !lean_is_exclusive(x_382);
if (x_449 == 0)
{
return x_382;
}
else
{
lean_object* x_450; lean_object* x_451; 
x_450 = lean_ctor_get(x_382, 0);
lean_inc(x_450);
lean_dec(x_382);
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_450);
return x_451;
}
}
}
else
{
uint8_t x_452; 
lean_dec_ref(x_377);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_free_object(x_364);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_452 = !lean_is_exclusive(x_379);
if (x_452 == 0)
{
return x_379;
}
else
{
lean_object* x_453; lean_object* x_454; 
x_453 = lean_ctor_get(x_379, 0);
lean_inc(x_453);
lean_dec(x_379);
x_454 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_454, 0, x_453);
return x_454;
}
}
}
else
{
lean_object* x_455; 
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_free_object(x_364);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_455 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_455;
}
}
else
{
lean_object* x_456; 
lean_dec_ref(x_363);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_456 = lean_ctor_get(x_366, 0);
lean_inc(x_456);
lean_dec_ref(x_366);
lean_ctor_set(x_364, 0, x_456);
return x_364;
}
}
else
{
lean_object* x_457; 
x_457 = lean_ctor_get(x_364, 0);
lean_inc(x_457);
lean_dec(x_364);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_458 = lean_st_ref_get(x_3);
x_459 = lean_ctor_get(x_363, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_363, 1);
lean_inc_ref(x_460);
x_461 = lean_ctor_get(x_363, 2);
lean_inc(x_461);
x_462 = lean_ctor_get(x_363, 3);
lean_inc_ref(x_462);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 lean_ctor_release(x_363, 2);
 lean_ctor_release(x_363, 3);
 x_463 = x_363;
} else {
 lean_dec_ref(x_363);
 x_463 = lean_box(0);
}
x_464 = lean_ctor_get(x_458, 0);
lean_inc_ref(x_464);
lean_dec_ref(x_458);
lean_inc(x_461);
x_465 = l_Lean_Compiler_LCNF_normFVarImp(x_464, x_461, x_52);
lean_dec_ref(x_464);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 x_467 = x_465;
} else {
 lean_dec_ref(x_465);
 x_467 = lean_box(0);
}
x_468 = lean_st_ref_get(x_3);
x_469 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_462);
lean_inc(x_466);
x_470 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_466, x_52, x_469, x_462, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 x_472 = x_470;
} else {
 lean_dec_ref(x_470);
 x_472 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_473 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_471, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_483; uint8_t x_484; lean_object* x_488; lean_object* x_489; lean_object* x_501; uint8_t x_502; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 x_475 = x_473;
} else {
 lean_dec_ref(x_473);
 x_475 = lean_box(0);
}
x_476 = lean_ctor_get(x_468, 0);
lean_inc_ref(x_476);
lean_dec_ref(x_468);
lean_inc_ref(x_460);
x_477 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_476, x_52, x_460);
lean_dec_ref(x_476);
x_501 = lean_array_get_size(x_474);
x_502 = lean_nat_dec_eq(x_501, x_119);
lean_dec(x_501);
if (x_502 == 0)
{
lean_dec(x_6);
x_488 = x_3;
x_489 = lean_box(0);
goto block_500;
}
else
{
lean_object* x_503; 
x_503 = lean_array_fget_borrowed(x_474, x_469);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_514; lean_object* x_515; uint8_t x_526; lean_object* x_527; uint8_t x_529; 
x_504 = lean_ctor_get(x_503, 1);
x_505 = lean_ctor_get(x_503, 2);
x_514 = lean_array_get_size(x_504);
x_529 = lean_nat_dec_lt(x_469, x_514);
if (x_529 == 0)
{
x_526 = x_52;
x_527 = lean_box(0);
goto block_528;
}
else
{
if (x_529 == 0)
{
x_526 = x_52;
x_527 = lean_box(0);
goto block_528;
}
else
{
size_t x_530; size_t x_531; lean_object* x_532; 
x_530 = 0;
x_531 = lean_usize_of_nat(x_514);
x_532 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_504, x_530, x_531, x_3);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; uint8_t x_534; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
lean_dec_ref(x_532);
x_534 = lean_unbox(x_533);
lean_dec(x_533);
x_526 = x_534;
x_527 = lean_box(0);
goto block_528;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_514);
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_472);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_535 = lean_ctor_get(x_532, 0);
lean_inc(x_535);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 x_536 = x_532;
} else {
 lean_dec_ref(x_532);
 x_536 = lean_box(0);
}
if (lean_is_scalar(x_536)) {
 x_537 = lean_alloc_ctor(1, 1, 0);
} else {
 x_537 = x_536;
}
lean_ctor_set(x_537, 0, x_535);
return x_537;
}
}
}
block_513:
{
lean_object* x_507; 
x_507 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; 
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 x_508 = x_507;
} else {
 lean_dec_ref(x_507);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(0, 1, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_505);
return x_509;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec_ref(x_505);
x_510 = lean_ctor_get(x_507, 0);
lean_inc(x_510);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 x_511 = x_507;
} else {
 lean_dec_ref(x_507);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(1, 1, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_510);
return x_512;
}
}
block_525:
{
uint8_t x_516; 
x_516 = lean_nat_dec_lt(x_469, x_514);
if (x_516 == 0)
{
lean_dec(x_514);
lean_dec_ref(x_504);
lean_dec(x_6);
x_506 = lean_box(0);
goto block_513;
}
else
{
uint8_t x_517; 
x_517 = lean_nat_dec_le(x_514, x_514);
if (x_517 == 0)
{
lean_dec(x_514);
lean_dec_ref(x_504);
lean_dec(x_6);
x_506 = lean_box(0);
goto block_513;
}
else
{
lean_object* x_518; size_t x_519; size_t x_520; lean_object* x_521; 
x_518 = lean_box(0);
x_519 = 0;
x_520 = lean_usize_of_nat(x_514);
lean_dec(x_514);
x_521 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_504, x_519, x_520, x_518, x_6);
lean_dec(x_6);
lean_dec_ref(x_504);
if (lean_obj_tag(x_521) == 0)
{
lean_dec_ref(x_521);
x_506 = lean_box(0);
goto block_513;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec_ref(x_505);
lean_dec(x_3);
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_523 = x_521;
} else {
 lean_dec_ref(x_521);
 x_523 = lean_box(0);
}
if (lean_is_scalar(x_523)) {
 x_524 = lean_alloc_ctor(1, 1, 0);
} else {
 x_524 = x_523;
}
lean_ctor_set(x_524, 0, x_522);
return x_524;
}
}
}
}
block_528:
{
if (x_526 == 0)
{
lean_inc_ref(x_505);
lean_inc_ref(x_504);
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_472);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec_ref(x_1);
x_515 = lean_box(0);
goto block_525;
}
else
{
if (x_52 == 0)
{
lean_dec(x_514);
lean_dec(x_6);
x_488 = x_3;
x_489 = lean_box(0);
goto block_500;
}
else
{
lean_inc_ref(x_505);
lean_inc_ref(x_504);
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_472);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec_ref(x_1);
x_515 = lean_box(0);
goto block_525;
}
}
}
}
else
{
lean_object* x_538; lean_object* x_539; 
lean_inc_ref(x_503);
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_472);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_538 = lean_ctor_get(x_503, 0);
lean_inc_ref(x_538);
lean_dec_ref(x_503);
x_539 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_539, 0, x_538);
return x_539;
}
}
block_482:
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
if (lean_is_scalar(x_463)) {
 x_479 = lean_alloc_ctor(0, 4, 0);
} else {
 x_479 = x_463;
}
lean_ctor_set(x_479, 0, x_459);
lean_ctor_set(x_479, 1, x_477);
lean_ctor_set(x_479, 2, x_466);
lean_ctor_set(x_479, 3, x_474);
if (lean_is_scalar(x_467)) {
 x_480 = lean_alloc_ctor(4, 1, 0);
} else {
 x_480 = x_467;
 lean_ctor_set_tag(x_480, 4);
}
lean_ctor_set(x_480, 0, x_479);
if (lean_is_scalar(x_475)) {
 x_481 = lean_alloc_ctor(0, 1, 0);
} else {
 x_481 = x_475;
}
lean_ctor_set(x_481, 0, x_480);
return x_481;
}
block_487:
{
if (x_484 == 0)
{
lean_dec(x_472);
lean_dec(x_461);
lean_dec_ref(x_1);
x_478 = lean_box(0);
goto block_482;
}
else
{
uint8_t x_485; 
x_485 = l_Lean_instBEqFVarId_beq(x_461, x_466);
lean_dec(x_461);
if (x_485 == 0)
{
lean_dec(x_472);
lean_dec_ref(x_1);
x_478 = lean_box(0);
goto block_482;
}
else
{
lean_object* x_486; 
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_463);
lean_dec(x_459);
if (lean_is_scalar(x_472)) {
 x_486 = lean_alloc_ctor(0, 1, 0);
} else {
 x_486 = x_472;
}
lean_ctor_set(x_486, 0, x_1);
return x_486;
}
}
}
block_500:
{
lean_object* x_490; 
lean_inc(x_466);
x_490 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_466, x_488);
lean_dec(x_488);
if (lean_obj_tag(x_490) == 0)
{
size_t x_491; size_t x_492; uint8_t x_493; 
lean_dec_ref(x_490);
x_491 = lean_ptr_addr(x_462);
lean_dec_ref(x_462);
x_492 = lean_ptr_addr(x_474);
x_493 = lean_usize_dec_eq(x_491, x_492);
if (x_493 == 0)
{
lean_dec_ref(x_460);
x_483 = lean_box(0);
x_484 = x_493;
goto block_487;
}
else
{
size_t x_494; size_t x_495; uint8_t x_496; 
x_494 = lean_ptr_addr(x_460);
lean_dec_ref(x_460);
x_495 = lean_ptr_addr(x_477);
x_496 = lean_usize_dec_eq(x_494, x_495);
x_483 = lean_box(0);
x_484 = x_496;
goto block_487;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_472);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec_ref(x_1);
x_497 = lean_ctor_get(x_490, 0);
lean_inc(x_497);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 x_498 = x_490;
} else {
 lean_dec_ref(x_490);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(1, 1, 0);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_497);
return x_499;
}
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_472);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_540 = lean_ctor_get(x_473, 0);
lean_inc(x_540);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 x_541 = x_473;
} else {
 lean_dec_ref(x_473);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 1, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_540);
return x_542;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_543 = lean_ctor_get(x_470, 0);
lean_inc(x_543);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 x_544 = x_470;
} else {
 lean_dec_ref(x_470);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 1, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_543);
return x_545;
}
}
else
{
lean_object* x_546; 
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_546 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_546;
}
}
else
{
lean_object* x_547; lean_object* x_548; 
lean_dec_ref(x_363);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_547 = lean_ctor_get(x_457, 0);
lean_inc(x_547);
lean_dec_ref(x_457);
x_548 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_548, 0, x_547);
return x_548;
}
}
}
else
{
uint8_t x_549; 
lean_dec_ref(x_363);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_549 = !lean_is_exclusive(x_364);
if (x_549 == 0)
{
return x_364;
}
else
{
lean_object* x_550; lean_object* x_551; 
x_550 = lean_ctor_get(x_364, 0);
lean_inc(x_550);
lean_dec(x_364);
x_551 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_551, 0, x_550);
return x_551;
}
}
}
case 5:
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_free_object(x_68);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_552 = lean_ctor_get(x_1, 0);
x_553 = lean_st_ref_get(x_3);
x_554 = lean_ctor_get(x_553, 0);
lean_inc_ref(x_554);
lean_dec_ref(x_553);
lean_inc(x_552);
x_555 = l_Lean_Compiler_LCNF_normFVarImp(x_554, x_552, x_52);
lean_dec_ref(x_554);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
lean_dec_ref(x_555);
lean_inc(x_556);
x_557 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_556, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_557) == 0)
{
uint8_t x_558; 
x_558 = !lean_is_exclusive(x_557);
if (x_558 == 0)
{
lean_object* x_559; uint8_t x_560; 
x_559 = lean_ctor_get(x_557, 0);
lean_dec(x_559);
x_560 = l_Lean_instBEqFVarId_beq(x_552, x_556);
if (x_560 == 0)
{
uint8_t x_561; 
x_561 = !lean_is_exclusive(x_1);
if (x_561 == 0)
{
lean_object* x_562; 
x_562 = lean_ctor_get(x_1, 0);
lean_dec(x_562);
lean_ctor_set(x_1, 0, x_556);
lean_ctor_set(x_557, 0, x_1);
return x_557;
}
else
{
lean_object* x_563; 
lean_dec(x_1);
x_563 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_563, 0, x_556);
lean_ctor_set(x_557, 0, x_563);
return x_557;
}
}
else
{
lean_dec(x_556);
lean_ctor_set(x_557, 0, x_1);
return x_557;
}
}
else
{
uint8_t x_564; 
lean_dec(x_557);
x_564 = l_Lean_instBEqFVarId_beq(x_552, x_556);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_565 = x_1;
} else {
 lean_dec_ref(x_1);
 x_565 = lean_box(0);
}
if (lean_is_scalar(x_565)) {
 x_566 = lean_alloc_ctor(5, 1, 0);
} else {
 x_566 = x_565;
}
lean_ctor_set(x_566, 0, x_556);
x_567 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_567, 0, x_566);
return x_567;
}
else
{
lean_object* x_568; 
lean_dec(x_556);
x_568 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_568, 0, x_1);
return x_568;
}
}
}
else
{
uint8_t x_569; 
lean_dec(x_556);
lean_dec_ref(x_1);
x_569 = !lean_is_exclusive(x_557);
if (x_569 == 0)
{
return x_557;
}
else
{
lean_object* x_570; lean_object* x_571; 
x_570 = lean_ctor_get(x_557, 0);
lean_inc(x_570);
lean_dec(x_557);
x_571 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_571, 0, x_570);
return x_571;
}
}
}
else
{
lean_object* x_572; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_572 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_572;
}
}
case 6:
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; size_t x_577; size_t x_578; uint8_t x_579; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_573 = lean_ctor_get(x_1, 0);
x_574 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_575 = lean_ctor_get(x_574, 0);
lean_inc_ref(x_575);
lean_dec_ref(x_574);
lean_inc_ref(x_573);
x_576 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_575, x_52, x_573);
lean_dec_ref(x_575);
x_577 = lean_ptr_addr(x_573);
x_578 = lean_ptr_addr(x_576);
x_579 = lean_usize_dec_eq(x_577, x_578);
if (x_579 == 0)
{
uint8_t x_580; 
x_580 = !lean_is_exclusive(x_1);
if (x_580 == 0)
{
lean_object* x_581; 
x_581 = lean_ctor_get(x_1, 0);
lean_dec(x_581);
lean_ctor_set(x_1, 0, x_576);
lean_ctor_set(x_68, 0, x_1);
return x_68;
}
else
{
lean_object* x_582; 
lean_dec(x_1);
x_582 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_582, 0, x_576);
lean_ctor_set(x_68, 0, x_582);
return x_68;
}
}
else
{
lean_dec_ref(x_576);
lean_ctor_set(x_68, 0, x_1);
return x_68;
}
}
default: 
{
lean_object* x_583; lean_object* x_584; 
lean_free_object(x_68);
x_583 = lean_ctor_get(x_1, 0);
x_584 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_584);
lean_inc_ref(x_583);
x_71 = x_583;
x_72 = x_584;
x_73 = x_2;
x_74 = x_3;
x_75 = x_4;
x_76 = x_5;
x_77 = x_6;
x_78 = x_7;
x_79 = x_8;
goto block_118;
}
}
block_118:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_71, 0);
x_81 = lean_ctor_get(x_71, 2);
x_82 = lean_ctor_get(x_71, 3);
x_83 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_80, x_74);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
lean_inc(x_84);
lean_inc_ref(x_1);
lean_inc_ref(x_72);
x_85 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_85, 0, x_72);
lean_closure_set(x_85, 1, x_1);
lean_closure_set(x_85, 2, x_84);
x_86 = lean_unbox(x_84);
if (x_86 == 0)
{
uint8_t x_87; 
lean_dec(x_84);
lean_dec_ref(x_72);
x_87 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_87 == 0)
{
x_18 = x_85;
x_19 = x_71;
x_20 = x_73;
x_21 = x_74;
x_22 = x_75;
x_23 = x_76;
x_24 = x_77;
x_25 = x_78;
x_26 = x_79;
x_27 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_88; 
lean_inc_ref(x_82);
x_88 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_82, x_81);
if (x_88 == 0)
{
x_18 = x_85;
x_19 = x_71;
x_20 = x_73;
x_21 = x_74;
x_22 = x_75;
x_23 = x_76;
x_24 = x_77;
x_25 = x_78;
x_26 = x_79;
x_27 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_st_ref_get(x_74);
x_90 = lean_ctor_get(x_89, 0);
lean_inc_ref(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_Compiler_LCNF_normFunDeclImp(x_52, x_71, x_90, x_76, x_77, x_78, x_79);
lean_dec_ref(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
lean_inc(x_79);
lean_inc_ref(x_78);
lean_inc(x_77);
lean_inc_ref(x_76);
x_93 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_92, x_76, x_77, x_78, x_79);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_74);
if (lean_obj_tag(x_95) == 0)
{
lean_dec_ref(x_95);
x_18 = x_85;
x_19 = x_94;
x_20 = x_73;
x_21 = x_74;
x_22 = x_75;
x_23 = x_76;
x_24 = x_77;
x_25 = x_78;
x_26 = x_79;
x_27 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_96; 
lean_dec(x_94);
lean_dec_ref(x_85);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
return x_95;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec_ref(x_85);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
x_99 = !lean_is_exclusive(x_93);
if (x_99 == 0)
{
return x_93;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_100);
lean_dec(x_93);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec_ref(x_85);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
x_102 = !lean_is_exclusive(x_91);
if (x_102 == 0)
{
return x_91;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_91, 0);
lean_inc(x_103);
lean_dec(x_91);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_85);
x_105 = lean_st_ref_get(x_74);
x_106 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_106);
lean_dec_ref(x_105);
x_107 = l_Lean_Compiler_LCNF_normFunDeclImp(x_52, x_71, x_106, x_76, x_77, x_78, x_79);
lean_dec_ref(x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_box(0);
x_110 = lean_unbox(x_84);
lean_dec(x_84);
x_111 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_72, x_1, x_110, x_108, x_109, x_73, x_74, x_75, x_76, x_77, x_78, x_79);
return x_111;
}
else
{
uint8_t x_112; 
lean_dec(x_84);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_1);
x_112 = !lean_is_exclusive(x_107);
if (x_112 == 0)
{
return x_107;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_107, 0);
lean_inc(x_113);
lean_dec(x_107);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_1);
x_115 = !lean_is_exclusive(x_83);
if (x_115 == 0)
{
return x_83;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_83, 0);
lean_inc(x_116);
lean_dec(x_83);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_633; lean_object* x_634; 
lean_dec(x_68);
x_633 = lean_unsigned_to_nat(1u);
x_634 = lean_nat_add(x_39, x_633);
lean_dec(x_39);
lean_ctor_set(x_7, 3, x_634);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_774; 
x_635 = lean_ctor_get(x_1, 0);
x_636 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_635);
x_774 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_52, x_635, x_3, x_6);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; uint8_t x_809; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
lean_dec_ref(x_774);
x_809 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_635, x_775);
if (x_809 == 0)
{
goto block_808;
}
else
{
if (x_52 == 0)
{
x_776 = x_2;
x_777 = x_3;
x_778 = x_4;
x_779 = x_5;
x_780 = x_6;
x_781 = x_7;
x_782 = x_8;
x_783 = lean_box(0);
goto block_803;
}
else
{
goto block_808;
}
}
block_803:
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_784 = lean_ctor_get(x_775, 2);
x_785 = lean_ctor_get(x_775, 3);
lean_inc(x_782);
lean_inc_ref(x_781);
lean_inc(x_780);
lean_inc_ref(x_779);
lean_inc_ref(x_778);
lean_inc(x_785);
x_786 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_785, x_776, x_778, x_779, x_780, x_781, x_782);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; 
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
lean_dec_ref(x_786);
if (lean_obj_tag(x_787) == 0)
{
lean_inc(x_785);
lean_inc_ref(x_784);
x_759 = x_775;
x_760 = x_784;
x_761 = x_785;
x_762 = x_776;
x_763 = x_777;
x_764 = x_778;
x_765 = x_779;
x_766 = x_780;
x_767 = x_781;
x_768 = x_782;
x_769 = lean_box(0);
goto block_773;
}
else
{
lean_object* x_788; lean_object* x_789; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
lean_dec_ref(x_787);
x_789 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_777);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; 
lean_dec_ref(x_789);
x_790 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_775, x_788, x_780);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
lean_dec_ref(x_790);
x_792 = lean_ctor_get(x_791, 2);
lean_inc_ref(x_792);
x_793 = lean_ctor_get(x_791, 3);
lean_inc(x_793);
x_759 = x_791;
x_760 = x_792;
x_761 = x_793;
x_762 = x_776;
x_763 = x_777;
x_764 = x_778;
x_765 = x_779;
x_766 = x_780;
x_767 = x_781;
x_768 = x_782;
x_769 = lean_box(0);
goto block_773;
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec(x_780);
lean_dec_ref(x_779);
lean_dec_ref(x_778);
lean_dec(x_777);
lean_dec_ref(x_776);
lean_dec_ref(x_1);
x_794 = lean_ctor_get(x_790, 0);
lean_inc(x_794);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 x_795 = x_790;
} else {
 lean_dec_ref(x_790);
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
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
lean_dec(x_788);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec(x_780);
lean_dec_ref(x_779);
lean_dec_ref(x_778);
lean_dec(x_777);
lean_dec_ref(x_776);
lean_dec(x_775);
lean_dec_ref(x_1);
x_797 = lean_ctor_get(x_789, 0);
lean_inc(x_797);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 x_798 = x_789;
} else {
 lean_dec_ref(x_789);
 x_798 = lean_box(0);
}
if (lean_is_scalar(x_798)) {
 x_799 = lean_alloc_ctor(1, 1, 0);
} else {
 x_799 = x_798;
}
lean_ctor_set(x_799, 0, x_797);
return x_799;
}
}
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec(x_780);
lean_dec_ref(x_779);
lean_dec_ref(x_778);
lean_dec(x_777);
lean_dec_ref(x_776);
lean_dec(x_775);
lean_dec_ref(x_1);
x_800 = lean_ctor_get(x_786, 0);
lean_inc(x_800);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 x_801 = x_786;
} else {
 lean_dec_ref(x_786);
 x_801 = lean_box(0);
}
if (lean_is_scalar(x_801)) {
 x_802 = lean_alloc_ctor(1, 1, 0);
} else {
 x_802 = x_801;
}
lean_ctor_set(x_802, 0, x_800);
return x_802;
}
}
block_808:
{
lean_object* x_804; 
x_804 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_804) == 0)
{
lean_dec_ref(x_804);
x_776 = x_2;
x_777 = x_3;
x_778 = x_4;
x_779 = x_5;
x_780 = x_6;
x_781 = x_7;
x_782 = x_8;
x_783 = lean_box(0);
goto block_803;
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_775);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_805 = lean_ctor_get(x_804, 0);
lean_inc(x_805);
if (lean_is_exclusive(x_804)) {
 lean_ctor_release(x_804, 0);
 x_806 = x_804;
} else {
 lean_dec_ref(x_804);
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
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_810 = lean_ctor_get(x_774, 0);
lean_inc(x_810);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_811 = x_774;
} else {
 lean_dec_ref(x_774);
 x_811 = lean_box(0);
}
if (lean_is_scalar(x_811)) {
 x_812 = lean_alloc_ctor(1, 1, 0);
} else {
 x_812 = x_811;
}
lean_ctor_set(x_812, 0, x_810);
return x_812;
}
block_758:
{
if (x_646 == 0)
{
lean_object* x_647; 
lean_inc(x_637);
lean_inc_ref(x_645);
lean_inc(x_639);
lean_inc_ref(x_641);
lean_inc_ref(x_638);
x_647 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_638, x_641, x_639, x_645, x_637);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; 
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
lean_dec_ref(x_647);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; 
lean_inc(x_637);
lean_inc_ref(x_645);
lean_inc(x_639);
lean_inc_ref(x_641);
lean_inc_ref(x_638);
x_649 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_638, x_644, x_643, x_641, x_639, x_645, x_637);
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_650; 
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
lean_dec_ref(x_649);
if (lean_obj_tag(x_650) == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_651 = lean_ctor_get(x_638, 0);
x_652 = lean_ctor_get(x_638, 3);
x_653 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_652);
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
lean_dec_ref(x_653);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; 
lean_inc(x_637);
lean_inc_ref(x_645);
lean_inc(x_639);
lean_inc_ref(x_641);
lean_inc_ref(x_642);
lean_inc(x_643);
lean_inc_ref(x_644);
lean_inc_ref(x_636);
lean_inc_ref(x_638);
x_655 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_638, x_636, x_644, x_643, x_642, x_641, x_639, x_645, x_637);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
lean_dec_ref(x_655);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; 
lean_inc(x_637);
lean_inc_ref(x_645);
lean_inc(x_639);
lean_inc_ref(x_641);
lean_inc_ref(x_642);
lean_inc(x_643);
lean_inc_ref(x_644);
lean_inc(x_652);
x_657 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_652, x_644, x_643, x_642, x_641, x_639, x_645, x_637);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
lean_dec_ref(x_657);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; 
lean_inc(x_637);
lean_inc_ref(x_645);
lean_inc(x_639);
lean_inc_ref(x_641);
lean_inc_ref(x_642);
lean_inc(x_643);
lean_inc_ref(x_644);
lean_inc_ref(x_636);
x_659 = l_Lean_Compiler_LCNF_Simp_simp(x_636, x_644, x_643, x_642, x_641, x_639, x_645, x_637);
if (lean_obj_tag(x_659) == 0)
{
lean_object* x_660; lean_object* x_661; 
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
lean_dec_ref(x_659);
x_661 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_651, x_643);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; uint8_t x_663; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
lean_dec_ref(x_661);
x_663 = lean_unbox(x_662);
lean_dec(x_662);
if (x_663 == 0)
{
lean_object* x_664; 
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_637);
lean_dec_ref(x_1);
x_664 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_638, x_643, x_639);
lean_dec(x_639);
lean_dec(x_643);
lean_dec_ref(x_638);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; 
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 x_665 = x_664;
} else {
 lean_dec_ref(x_664);
 x_665 = lean_box(0);
}
if (lean_is_scalar(x_665)) {
 x_666 = lean_alloc_ctor(0, 1, 0);
} else {
 x_666 = x_665;
}
lean_ctor_set(x_666, 0, x_660);
return x_666;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_660);
x_667 = lean_ctor_get(x_664, 0);
lean_inc(x_667);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 x_668 = x_664;
} else {
 lean_dec_ref(x_664);
 x_668 = lean_box(0);
}
if (lean_is_scalar(x_668)) {
 x_669 = lean_alloc_ctor(1, 1, 0);
} else {
 x_669 = x_668;
}
lean_ctor_set(x_669, 0, x_667);
return x_669;
}
}
else
{
lean_object* x_670; 
lean_inc_ref(x_638);
x_670 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_638, x_644, x_643, x_642, x_641, x_639, x_645, x_637);
lean_dec(x_637);
lean_dec_ref(x_645);
lean_dec(x_639);
lean_dec_ref(x_641);
lean_dec_ref(x_642);
lean_dec(x_643);
lean_dec_ref(x_644);
if (lean_obj_tag(x_670) == 0)
{
size_t x_671; size_t x_672; uint8_t x_673; 
lean_dec_ref(x_670);
x_671 = lean_ptr_addr(x_636);
x_672 = lean_ptr_addr(x_660);
x_673 = lean_usize_dec_eq(x_671, x_672);
if (x_673 == 0)
{
x_10 = x_638;
x_11 = lean_box(0);
x_12 = x_660;
x_13 = x_673;
goto block_17;
}
else
{
size_t x_674; size_t x_675; uint8_t x_676; 
x_674 = lean_ptr_addr(x_635);
x_675 = lean_ptr_addr(x_638);
x_676 = lean_usize_dec_eq(x_674, x_675);
x_10 = x_638;
x_11 = lean_box(0);
x_12 = x_660;
x_13 = x_676;
goto block_17;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
lean_dec(x_660);
lean_dec_ref(x_638);
lean_dec_ref(x_1);
x_677 = lean_ctor_get(x_670, 0);
lean_inc(x_677);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 x_678 = x_670;
} else {
 lean_dec_ref(x_670);
 x_678 = lean_box(0);
}
if (lean_is_scalar(x_678)) {
 x_679 = lean_alloc_ctor(1, 1, 0);
} else {
 x_679 = x_678;
}
lean_ctor_set(x_679, 0, x_677);
return x_679;
}
}
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_660);
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_1);
x_680 = lean_ctor_get(x_661, 0);
lean_inc(x_680);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 x_681 = x_661;
} else {
 lean_dec_ref(x_661);
 x_681 = lean_box(0);
}
if (lean_is_scalar(x_681)) {
 x_682 = lean_alloc_ctor(1, 1, 0);
} else {
 x_682 = x_681;
}
lean_ctor_set(x_682, 0, x_680);
return x_682;
}
}
else
{
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_1);
return x_659;
}
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
lean_inc_ref(x_636);
lean_dec_ref(x_1);
x_683 = lean_ctor_get(x_658, 0);
lean_inc(x_683);
lean_dec_ref(x_658);
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
lean_dec(x_683);
lean_inc(x_651);
x_686 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_651, x_685, x_643, x_639, x_645, x_637);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; 
lean_dec_ref(x_686);
x_687 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_638, x_643, x_639);
lean_dec_ref(x_638);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; 
lean_dec_ref(x_687);
lean_inc(x_637);
lean_inc_ref(x_645);
lean_inc(x_639);
lean_inc_ref(x_641);
lean_inc_ref(x_642);
lean_inc(x_643);
lean_inc_ref(x_644);
x_688 = l_Lean_Compiler_LCNF_Simp_simp(x_636, x_644, x_643, x_642, x_641, x_639, x_645, x_637);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
lean_dec_ref(x_688);
x_690 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_684, x_689, x_644, x_643, x_642, x_641, x_639, x_645, x_637);
lean_dec(x_637);
lean_dec_ref(x_645);
lean_dec(x_639);
lean_dec_ref(x_641);
lean_dec_ref(x_642);
lean_dec(x_643);
lean_dec_ref(x_644);
lean_dec(x_684);
return x_690;
}
else
{
lean_dec(x_684);
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec(x_637);
return x_688;
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_684);
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec(x_637);
lean_dec_ref(x_636);
x_691 = lean_ctor_get(x_687, 0);
lean_inc(x_691);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 x_692 = x_687;
} else {
 lean_dec_ref(x_687);
 x_692 = lean_box(0);
}
if (lean_is_scalar(x_692)) {
 x_693 = lean_alloc_ctor(1, 1, 0);
} else {
 x_693 = x_692;
}
lean_ctor_set(x_693, 0, x_691);
return x_693;
}
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_684);
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
x_694 = lean_ctor_get(x_686, 0);
lean_inc(x_694);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 x_695 = x_686;
} else {
 lean_dec_ref(x_686);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(1, 1, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_694);
return x_696;
}
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_1);
x_697 = lean_ctor_get(x_657, 0);
lean_inc(x_697);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 x_698 = x_657;
} else {
 lean_dec_ref(x_657);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 1, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_697);
return x_699;
}
}
else
{
lean_object* x_700; lean_object* x_701; 
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_637);
lean_dec_ref(x_1);
x_700 = lean_ctor_get(x_656, 0);
lean_inc(x_700);
lean_dec_ref(x_656);
x_701 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_638, x_643, x_639);
lean_dec(x_639);
lean_dec(x_643);
lean_dec_ref(x_638);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; 
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 x_702 = x_701;
} else {
 lean_dec_ref(x_701);
 x_702 = lean_box(0);
}
if (lean_is_scalar(x_702)) {
 x_703 = lean_alloc_ctor(0, 1, 0);
} else {
 x_703 = x_702;
}
lean_ctor_set(x_703, 0, x_700);
return x_703;
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_700);
x_704 = lean_ctor_get(x_701, 0);
lean_inc(x_704);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 x_705 = x_701;
} else {
 lean_dec_ref(x_701);
 x_705 = lean_box(0);
}
if (lean_is_scalar(x_705)) {
 x_706 = lean_alloc_ctor(1, 1, 0);
} else {
 x_706 = x_705;
}
lean_ctor_set(x_706, 0, x_704);
return x_706;
}
}
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_1);
x_707 = lean_ctor_get(x_655, 0);
lean_inc(x_707);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 x_708 = x_655;
} else {
 lean_dec_ref(x_655);
 x_708 = lean_box(0);
}
if (lean_is_scalar(x_708)) {
 x_709 = lean_alloc_ctor(1, 1, 0);
} else {
 x_709 = x_708;
}
lean_ctor_set(x_709, 0, x_707);
return x_709;
}
}
else
{
lean_object* x_710; lean_object* x_711; 
lean_inc_ref(x_636);
lean_dec_ref(x_1);
x_710 = lean_ctor_get(x_654, 0);
lean_inc(x_710);
lean_dec_ref(x_654);
lean_inc(x_651);
x_711 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_651, x_710, x_643, x_639, x_645, x_637);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; 
lean_dec_ref(x_711);
x_712 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_638, x_643, x_639);
lean_dec_ref(x_638);
if (lean_obj_tag(x_712) == 0)
{
lean_dec_ref(x_712);
x_1 = x_636;
x_2 = x_644;
x_3 = x_643;
x_4 = x_642;
x_5 = x_641;
x_6 = x_639;
x_7 = x_645;
x_8 = x_637;
goto _start;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec(x_637);
lean_dec_ref(x_636);
x_714 = lean_ctor_get(x_712, 0);
lean_inc(x_714);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 x_715 = x_712;
} else {
 lean_dec_ref(x_712);
 x_715 = lean_box(0);
}
if (lean_is_scalar(x_715)) {
 x_716 = lean_alloc_ctor(1, 1, 0);
} else {
 x_716 = x_715;
}
lean_ctor_set(x_716, 0, x_714);
return x_716;
}
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
x_717 = lean_ctor_get(x_711, 0);
lean_inc(x_717);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 x_718 = x_711;
} else {
 lean_dec_ref(x_711);
 x_718 = lean_box(0);
}
if (lean_is_scalar(x_718)) {
 x_719 = lean_alloc_ctor(1, 1, 0);
} else {
 x_719 = x_718;
}
lean_ctor_set(x_719, 0, x_717);
return x_719;
}
}
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; 
lean_dec_ref(x_638);
lean_inc_ref(x_636);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_720 = x_1;
} else {
 lean_dec_ref(x_1);
 x_720 = lean_box(0);
}
x_721 = lean_ctor_get(x_650, 0);
lean_inc(x_721);
lean_dec_ref(x_650);
if (lean_is_scalar(x_720)) {
 x_722 = lean_alloc_ctor(1, 2, 0);
} else {
 x_722 = x_720;
 lean_ctor_set_tag(x_722, 1);
}
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_636);
x_1 = x_722;
x_2 = x_644;
x_3 = x_643;
x_4 = x_642;
x_5 = x_641;
x_6 = x_639;
x_7 = x_645;
x_8 = x_637;
goto _start;
}
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_1);
x_724 = lean_ctor_get(x_649, 0);
lean_inc(x_724);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 x_725 = x_649;
} else {
 lean_dec_ref(x_649);
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
lean_object* x_727; lean_object* x_728; 
lean_dec_ref(x_638);
lean_inc_ref(x_636);
lean_dec_ref(x_1);
x_727 = lean_ctor_get(x_648, 0);
lean_inc(x_727);
lean_dec_ref(x_648);
x_728 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_643);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; 
lean_dec_ref(x_728);
lean_inc(x_637);
lean_inc_ref(x_645);
lean_inc(x_639);
lean_inc_ref(x_641);
lean_inc_ref(x_642);
lean_inc(x_643);
lean_inc_ref(x_644);
x_729 = l_Lean_Compiler_LCNF_Simp_simp(x_636, x_644, x_643, x_642, x_641, x_639, x_645, x_637);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
lean_dec_ref(x_729);
x_731 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_727, x_730, x_644, x_643, x_642, x_641, x_639, x_645, x_637);
lean_dec(x_637);
lean_dec_ref(x_645);
lean_dec(x_639);
lean_dec_ref(x_641);
lean_dec_ref(x_642);
lean_dec(x_643);
lean_dec_ref(x_644);
lean_dec(x_727);
return x_731;
}
else
{
lean_dec(x_727);
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec(x_637);
return x_729;
}
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; 
lean_dec(x_727);
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec(x_637);
lean_dec_ref(x_636);
x_732 = lean_ctor_get(x_728, 0);
lean_inc(x_732);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 x_733 = x_728;
} else {
 lean_dec_ref(x_728);
 x_733 = lean_box(0);
}
if (lean_is_scalar(x_733)) {
 x_734 = lean_alloc_ctor(1, 1, 0);
} else {
 x_734 = x_733;
}
lean_ctor_set(x_734, 0, x_732);
return x_734;
}
}
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_1);
x_735 = lean_ctor_get(x_647, 0);
lean_inc(x_735);
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 x_736 = x_647;
} else {
 lean_dec_ref(x_647);
 x_736 = lean_box(0);
}
if (lean_is_scalar(x_736)) {
 x_737 = lean_alloc_ctor(1, 1, 0);
} else {
 x_737 = x_736;
}
lean_ctor_set(x_737, 0, x_735);
return x_737;
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; uint8_t x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_inc_ref(x_636);
lean_dec_ref(x_1);
x_738 = lean_st_ref_take(x_643);
x_739 = lean_ctor_get(x_638, 0);
x_740 = lean_ctor_get(x_738, 0);
lean_inc_ref(x_740);
x_741 = lean_ctor_get(x_738, 1);
lean_inc_ref(x_741);
x_742 = lean_ctor_get(x_738, 2);
lean_inc(x_742);
x_743 = lean_ctor_get(x_738, 3);
lean_inc_ref(x_743);
x_744 = lean_ctor_get_uint8(x_738, sizeof(void*)*7);
x_745 = lean_ctor_get(x_738, 4);
lean_inc(x_745);
x_746 = lean_ctor_get(x_738, 5);
lean_inc(x_746);
x_747 = lean_ctor_get(x_738, 6);
lean_inc(x_747);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 lean_ctor_release(x_738, 1);
 lean_ctor_release(x_738, 2);
 lean_ctor_release(x_738, 3);
 lean_ctor_release(x_738, 4);
 lean_ctor_release(x_738, 5);
 lean_ctor_release(x_738, 6);
 x_748 = x_738;
} else {
 lean_dec_ref(x_738);
 x_748 = lean_box(0);
}
x_749 = lean_box(0);
lean_inc(x_739);
x_750 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_740, x_739, x_749);
if (lean_is_scalar(x_748)) {
 x_751 = lean_alloc_ctor(0, 7, 1);
} else {
 x_751 = x_748;
}
lean_ctor_set(x_751, 0, x_750);
lean_ctor_set(x_751, 1, x_741);
lean_ctor_set(x_751, 2, x_742);
lean_ctor_set(x_751, 3, x_743);
lean_ctor_set(x_751, 4, x_745);
lean_ctor_set(x_751, 5, x_746);
lean_ctor_set(x_751, 6, x_747);
lean_ctor_set_uint8(x_751, sizeof(void*)*7, x_744);
x_752 = lean_st_ref_set(x_643, x_751);
x_753 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_638, x_643, x_639);
lean_dec_ref(x_638);
if (lean_obj_tag(x_753) == 0)
{
lean_dec_ref(x_753);
x_1 = x_636;
x_2 = x_644;
x_3 = x_643;
x_4 = x_642;
x_5 = x_641;
x_6 = x_639;
x_7 = x_645;
x_8 = x_637;
goto _start;
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; 
lean_dec_ref(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_641);
lean_dec(x_639);
lean_dec(x_637);
lean_dec_ref(x_636);
x_755 = lean_ctor_get(x_753, 0);
lean_inc(x_755);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 x_756 = x_753;
} else {
 lean_dec_ref(x_753);
 x_756 = lean_box(0);
}
if (lean_is_scalar(x_756)) {
 x_757 = lean_alloc_ctor(1, 1, 0);
} else {
 x_757 = x_756;
}
lean_ctor_set(x_757, 0, x_755);
return x_757;
}
}
}
block_773:
{
uint8_t x_770; 
x_770 = l_Lean_Expr_isErased(x_760);
lean_dec_ref(x_760);
if (x_770 == 0)
{
lean_dec(x_761);
x_637 = x_768;
x_638 = x_759;
x_639 = x_766;
x_640 = lean_box(0);
x_641 = x_765;
x_642 = x_764;
x_643 = x_763;
x_644 = x_762;
x_645 = x_767;
x_646 = x_52;
goto block_758;
}
else
{
lean_object* x_771; uint8_t x_772; 
x_771 = lean_box(1);
x_772 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_761, x_771);
lean_dec(x_761);
if (x_772 == 0)
{
x_637 = x_768;
x_638 = x_759;
x_639 = x_766;
x_640 = lean_box(0);
x_641 = x_765;
x_642 = x_764;
x_643 = x_763;
x_644 = x_762;
x_645 = x_767;
x_646 = x_770;
goto block_758;
}
else
{
x_637 = x_768;
x_638 = x_759;
x_639 = x_766;
x_640 = lean_box(0);
x_641 = x_765;
x_642 = x_764;
x_643 = x_763;
x_644 = x_762;
x_645 = x_767;
x_646 = x_52;
goto block_758;
}
}
}
}
case 3:
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_813 = lean_ctor_get(x_1, 0);
x_814 = lean_ctor_get(x_1, 1);
x_815 = lean_st_ref_get(x_3);
x_816 = lean_ctor_get(x_815, 0);
lean_inc_ref(x_816);
lean_dec_ref(x_815);
lean_inc(x_813);
x_817 = l_Lean_Compiler_LCNF_normFVarImp(x_816, x_813, x_52);
lean_dec_ref(x_816);
if (lean_obj_tag(x_817) == 0)
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_823; lean_object* x_829; lean_object* x_835; 
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
lean_dec_ref(x_817);
lean_inc_ref(x_814);
x_819 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_52, x_814, x_3);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 x_821 = x_819;
} else {
 lean_dec_ref(x_819);
 x_821 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_820);
x_835 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_818, x_820, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_835) == 0)
{
lean_object* x_836; 
x_836 = lean_ctor_get(x_835, 0);
lean_inc(x_836);
lean_dec_ref(x_835);
if (lean_obj_tag(x_836) == 0)
{
lean_object* x_837; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_818);
x_837 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_818, x_3);
if (lean_obj_tag(x_837) == 0)
{
lean_object* x_838; lean_object* x_839; uint8_t x_840; 
lean_dec_ref(x_837);
x_838 = lean_unsigned_to_nat(0u);
x_839 = lean_array_get_size(x_820);
x_840 = lean_nat_dec_lt(x_838, x_839);
if (x_840 == 0)
{
lean_dec(x_839);
lean_dec(x_3);
x_829 = lean_box(0);
goto block_834;
}
else
{
uint8_t x_841; 
x_841 = lean_nat_dec_le(x_839, x_839);
if (x_841 == 0)
{
lean_dec(x_839);
lean_dec(x_3);
x_829 = lean_box(0);
goto block_834;
}
else
{
lean_object* x_842; size_t x_843; size_t x_844; lean_object* x_845; 
x_842 = lean_box(0);
x_843 = 0;
x_844 = lean_usize_of_nat(x_839);
lean_dec(x_839);
x_845 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_820, x_843, x_844, x_842, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_845) == 0)
{
lean_dec_ref(x_845);
x_829 = lean_box(0);
goto block_834;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_818);
lean_dec_ref(x_1);
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 x_847 = x_845;
} else {
 lean_dec_ref(x_845);
 x_847 = lean_box(0);
}
if (lean_is_scalar(x_847)) {
 x_848 = lean_alloc_ctor(1, 1, 0);
} else {
 x_848 = x_847;
}
lean_ctor_set(x_848, 0, x_846);
return x_848;
}
}
}
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_818);
lean_dec(x_3);
lean_dec_ref(x_1);
x_849 = lean_ctor_get(x_837, 0);
lean_inc(x_849);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 x_850 = x_837;
} else {
 lean_dec_ref(x_837);
 x_850 = lean_box(0);
}
if (lean_is_scalar(x_850)) {
 x_851 = lean_alloc_ctor(1, 1, 0);
} else {
 x_851 = x_850;
}
lean_ctor_set(x_851, 0, x_849);
return x_851;
}
}
else
{
lean_object* x_852; 
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_818);
lean_dec_ref(x_1);
x_852 = lean_ctor_get(x_836, 0);
lean_inc(x_852);
lean_dec_ref(x_836);
x_1 = x_852;
goto _start;
}
}
else
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_818);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_854 = lean_ctor_get(x_835, 0);
lean_inc(x_854);
if (lean_is_exclusive(x_835)) {
 lean_ctor_release(x_835, 0);
 x_855 = x_835;
} else {
 lean_dec_ref(x_835);
 x_855 = lean_box(0);
}
if (lean_is_scalar(x_855)) {
 x_856 = lean_alloc_ctor(1, 1, 0);
} else {
 x_856 = x_855;
}
lean_ctor_set(x_856, 0, x_854);
return x_856;
}
block_828:
{
if (x_823 == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_824 = x_1;
} else {
 lean_dec_ref(x_1);
 x_824 = lean_box(0);
}
if (lean_is_scalar(x_824)) {
 x_825 = lean_alloc_ctor(3, 2, 0);
} else {
 x_825 = x_824;
}
lean_ctor_set(x_825, 0, x_818);
lean_ctor_set(x_825, 1, x_820);
if (lean_is_scalar(x_821)) {
 x_826 = lean_alloc_ctor(0, 1, 0);
} else {
 x_826 = x_821;
}
lean_ctor_set(x_826, 0, x_825);
return x_826;
}
else
{
lean_object* x_827; 
lean_dec(x_820);
lean_dec(x_818);
if (lean_is_scalar(x_821)) {
 x_827 = lean_alloc_ctor(0, 1, 0);
} else {
 x_827 = x_821;
}
lean_ctor_set(x_827, 0, x_1);
return x_827;
}
}
block_834:
{
uint8_t x_830; 
x_830 = l_Lean_instBEqFVarId_beq(x_813, x_818);
if (x_830 == 0)
{
x_822 = lean_box(0);
x_823 = x_830;
goto block_828;
}
else
{
size_t x_831; size_t x_832; uint8_t x_833; 
x_831 = lean_ptr_addr(x_814);
x_832 = lean_ptr_addr(x_820);
x_833 = lean_usize_dec_eq(x_831, x_832);
x_822 = lean_box(0);
x_823 = x_833;
goto block_828;
}
}
}
else
{
lean_object* x_857; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_857 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_857;
}
}
case 4:
{
lean_object* x_858; lean_object* x_859; 
x_858 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_858);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_858);
x_859 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_858, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_859) == 0)
{
lean_object* x_860; lean_object* x_861; 
x_860 = lean_ctor_get(x_859, 0);
lean_inc(x_860);
if (lean_is_exclusive(x_859)) {
 lean_ctor_release(x_859, 0);
 x_861 = x_859;
} else {
 lean_dec_ref(x_859);
 x_861 = lean_box(0);
}
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_862 = lean_st_ref_get(x_3);
x_863 = lean_ctor_get(x_858, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_858, 1);
lean_inc_ref(x_864);
x_865 = lean_ctor_get(x_858, 2);
lean_inc(x_865);
x_866 = lean_ctor_get(x_858, 3);
lean_inc_ref(x_866);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 lean_ctor_release(x_858, 2);
 lean_ctor_release(x_858, 3);
 x_867 = x_858;
} else {
 lean_dec_ref(x_858);
 x_867 = lean_box(0);
}
x_868 = lean_ctor_get(x_862, 0);
lean_inc_ref(x_868);
lean_dec_ref(x_862);
lean_inc(x_865);
x_869 = l_Lean_Compiler_LCNF_normFVarImp(x_868, x_865, x_52);
lean_dec_ref(x_868);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 x_871 = x_869;
} else {
 lean_dec_ref(x_869);
 x_871 = lean_box(0);
}
x_872 = lean_st_ref_get(x_3);
x_873 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_866);
lean_inc(x_870);
x_874 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_870, x_52, x_873, x_866, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_874) == 0)
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; 
x_875 = lean_ctor_get(x_874, 0);
lean_inc(x_875);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 x_876 = x_874;
} else {
 lean_dec_ref(x_874);
 x_876 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_877 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_875, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_887; uint8_t x_888; lean_object* x_892; lean_object* x_893; lean_object* x_905; uint8_t x_906; 
x_878 = lean_ctor_get(x_877, 0);
lean_inc(x_878);
if (lean_is_exclusive(x_877)) {
 lean_ctor_release(x_877, 0);
 x_879 = x_877;
} else {
 lean_dec_ref(x_877);
 x_879 = lean_box(0);
}
x_880 = lean_ctor_get(x_872, 0);
lean_inc_ref(x_880);
lean_dec_ref(x_872);
lean_inc_ref(x_864);
x_881 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_880, x_52, x_864);
lean_dec_ref(x_880);
x_905 = lean_array_get_size(x_878);
x_906 = lean_nat_dec_eq(x_905, x_633);
lean_dec(x_905);
if (x_906 == 0)
{
lean_dec(x_861);
lean_dec(x_6);
x_892 = x_3;
x_893 = lean_box(0);
goto block_904;
}
else
{
lean_object* x_907; 
x_907 = lean_array_fget_borrowed(x_878, x_873);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_918; lean_object* x_919; uint8_t x_930; lean_object* x_931; uint8_t x_933; 
lean_dec(x_861);
x_908 = lean_ctor_get(x_907, 1);
x_909 = lean_ctor_get(x_907, 2);
x_918 = lean_array_get_size(x_908);
x_933 = lean_nat_dec_lt(x_873, x_918);
if (x_933 == 0)
{
x_930 = x_52;
x_931 = lean_box(0);
goto block_932;
}
else
{
if (x_933 == 0)
{
x_930 = x_52;
x_931 = lean_box(0);
goto block_932;
}
else
{
size_t x_934; size_t x_935; lean_object* x_936; 
x_934 = 0;
x_935 = lean_usize_of_nat(x_918);
x_936 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_908, x_934, x_935, x_3);
if (lean_obj_tag(x_936) == 0)
{
lean_object* x_937; uint8_t x_938; 
x_937 = lean_ctor_get(x_936, 0);
lean_inc(x_937);
lean_dec_ref(x_936);
x_938 = lean_unbox(x_937);
lean_dec(x_937);
x_930 = x_938;
x_931 = lean_box(0);
goto block_932;
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec(x_918);
lean_dec_ref(x_881);
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_876);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_867);
lean_dec_ref(x_866);
lean_dec(x_865);
lean_dec_ref(x_864);
lean_dec(x_863);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_939 = lean_ctor_get(x_936, 0);
lean_inc(x_939);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 x_940 = x_936;
} else {
 lean_dec_ref(x_936);
 x_940 = lean_box(0);
}
if (lean_is_scalar(x_940)) {
 x_941 = lean_alloc_ctor(1, 1, 0);
} else {
 x_941 = x_940;
}
lean_ctor_set(x_941, 0, x_939);
return x_941;
}
}
}
block_917:
{
lean_object* x_911; 
x_911 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_911) == 0)
{
lean_object* x_912; lean_object* x_913; 
if (lean_is_exclusive(x_911)) {
 lean_ctor_release(x_911, 0);
 x_912 = x_911;
} else {
 lean_dec_ref(x_911);
 x_912 = lean_box(0);
}
if (lean_is_scalar(x_912)) {
 x_913 = lean_alloc_ctor(0, 1, 0);
} else {
 x_913 = x_912;
}
lean_ctor_set(x_913, 0, x_909);
return x_913;
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; 
lean_dec_ref(x_909);
x_914 = lean_ctor_get(x_911, 0);
lean_inc(x_914);
if (lean_is_exclusive(x_911)) {
 lean_ctor_release(x_911, 0);
 x_915 = x_911;
} else {
 lean_dec_ref(x_911);
 x_915 = lean_box(0);
}
if (lean_is_scalar(x_915)) {
 x_916 = lean_alloc_ctor(1, 1, 0);
} else {
 x_916 = x_915;
}
lean_ctor_set(x_916, 0, x_914);
return x_916;
}
}
block_929:
{
uint8_t x_920; 
x_920 = lean_nat_dec_lt(x_873, x_918);
if (x_920 == 0)
{
lean_dec(x_918);
lean_dec_ref(x_908);
lean_dec(x_6);
x_910 = lean_box(0);
goto block_917;
}
else
{
uint8_t x_921; 
x_921 = lean_nat_dec_le(x_918, x_918);
if (x_921 == 0)
{
lean_dec(x_918);
lean_dec_ref(x_908);
lean_dec(x_6);
x_910 = lean_box(0);
goto block_917;
}
else
{
lean_object* x_922; size_t x_923; size_t x_924; lean_object* x_925; 
x_922 = lean_box(0);
x_923 = 0;
x_924 = lean_usize_of_nat(x_918);
lean_dec(x_918);
x_925 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_908, x_923, x_924, x_922, x_6);
lean_dec(x_6);
lean_dec_ref(x_908);
if (lean_obj_tag(x_925) == 0)
{
lean_dec_ref(x_925);
x_910 = lean_box(0);
goto block_917;
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec_ref(x_909);
lean_dec(x_3);
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
if (lean_is_exclusive(x_925)) {
 lean_ctor_release(x_925, 0);
 x_927 = x_925;
} else {
 lean_dec_ref(x_925);
 x_927 = lean_box(0);
}
if (lean_is_scalar(x_927)) {
 x_928 = lean_alloc_ctor(1, 1, 0);
} else {
 x_928 = x_927;
}
lean_ctor_set(x_928, 0, x_926);
return x_928;
}
}
}
}
block_932:
{
if (x_930 == 0)
{
lean_inc_ref(x_909);
lean_inc_ref(x_908);
lean_dec_ref(x_881);
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_876);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_867);
lean_dec_ref(x_866);
lean_dec(x_865);
lean_dec_ref(x_864);
lean_dec(x_863);
lean_dec_ref(x_1);
x_919 = lean_box(0);
goto block_929;
}
else
{
if (x_52 == 0)
{
lean_dec(x_918);
lean_dec(x_6);
x_892 = x_3;
x_893 = lean_box(0);
goto block_904;
}
else
{
lean_inc_ref(x_909);
lean_inc_ref(x_908);
lean_dec_ref(x_881);
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_876);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_867);
lean_dec_ref(x_866);
lean_dec(x_865);
lean_dec_ref(x_864);
lean_dec(x_863);
lean_dec_ref(x_1);
x_919 = lean_box(0);
goto block_929;
}
}
}
}
else
{
lean_object* x_942; lean_object* x_943; 
lean_inc_ref(x_907);
lean_dec_ref(x_881);
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_876);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_867);
lean_dec_ref(x_866);
lean_dec(x_865);
lean_dec_ref(x_864);
lean_dec(x_863);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_942 = lean_ctor_get(x_907, 0);
lean_inc_ref(x_942);
lean_dec_ref(x_907);
if (lean_is_scalar(x_861)) {
 x_943 = lean_alloc_ctor(0, 1, 0);
} else {
 x_943 = x_861;
}
lean_ctor_set(x_943, 0, x_942);
return x_943;
}
}
block_886:
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; 
if (lean_is_scalar(x_867)) {
 x_883 = lean_alloc_ctor(0, 4, 0);
} else {
 x_883 = x_867;
}
lean_ctor_set(x_883, 0, x_863);
lean_ctor_set(x_883, 1, x_881);
lean_ctor_set(x_883, 2, x_870);
lean_ctor_set(x_883, 3, x_878);
if (lean_is_scalar(x_871)) {
 x_884 = lean_alloc_ctor(4, 1, 0);
} else {
 x_884 = x_871;
 lean_ctor_set_tag(x_884, 4);
}
lean_ctor_set(x_884, 0, x_883);
if (lean_is_scalar(x_879)) {
 x_885 = lean_alloc_ctor(0, 1, 0);
} else {
 x_885 = x_879;
}
lean_ctor_set(x_885, 0, x_884);
return x_885;
}
block_891:
{
if (x_888 == 0)
{
lean_dec(x_876);
lean_dec(x_865);
lean_dec_ref(x_1);
x_882 = lean_box(0);
goto block_886;
}
else
{
uint8_t x_889; 
x_889 = l_Lean_instBEqFVarId_beq(x_865, x_870);
lean_dec(x_865);
if (x_889 == 0)
{
lean_dec(x_876);
lean_dec_ref(x_1);
x_882 = lean_box(0);
goto block_886;
}
else
{
lean_object* x_890; 
lean_dec_ref(x_881);
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_867);
lean_dec(x_863);
if (lean_is_scalar(x_876)) {
 x_890 = lean_alloc_ctor(0, 1, 0);
} else {
 x_890 = x_876;
}
lean_ctor_set(x_890, 0, x_1);
return x_890;
}
}
}
block_904:
{
lean_object* x_894; 
lean_inc(x_870);
x_894 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_870, x_892);
lean_dec(x_892);
if (lean_obj_tag(x_894) == 0)
{
size_t x_895; size_t x_896; uint8_t x_897; 
lean_dec_ref(x_894);
x_895 = lean_ptr_addr(x_866);
lean_dec_ref(x_866);
x_896 = lean_ptr_addr(x_878);
x_897 = lean_usize_dec_eq(x_895, x_896);
if (x_897 == 0)
{
lean_dec_ref(x_864);
x_887 = lean_box(0);
x_888 = x_897;
goto block_891;
}
else
{
size_t x_898; size_t x_899; uint8_t x_900; 
x_898 = lean_ptr_addr(x_864);
lean_dec_ref(x_864);
x_899 = lean_ptr_addr(x_881);
x_900 = lean_usize_dec_eq(x_898, x_899);
x_887 = lean_box(0);
x_888 = x_900;
goto block_891;
}
}
else
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; 
lean_dec_ref(x_881);
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_876);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_867);
lean_dec_ref(x_866);
lean_dec(x_865);
lean_dec_ref(x_864);
lean_dec(x_863);
lean_dec_ref(x_1);
x_901 = lean_ctor_get(x_894, 0);
lean_inc(x_901);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 x_902 = x_894;
} else {
 lean_dec_ref(x_894);
 x_902 = lean_box(0);
}
if (lean_is_scalar(x_902)) {
 x_903 = lean_alloc_ctor(1, 1, 0);
} else {
 x_903 = x_902;
}
lean_ctor_set(x_903, 0, x_901);
return x_903;
}
}
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; 
lean_dec(x_876);
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_867);
lean_dec_ref(x_866);
lean_dec(x_865);
lean_dec_ref(x_864);
lean_dec(x_863);
lean_dec(x_861);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_944 = lean_ctor_get(x_877, 0);
lean_inc(x_944);
if (lean_is_exclusive(x_877)) {
 lean_ctor_release(x_877, 0);
 x_945 = x_877;
} else {
 lean_dec_ref(x_877);
 x_945 = lean_box(0);
}
if (lean_is_scalar(x_945)) {
 x_946 = lean_alloc_ctor(1, 1, 0);
} else {
 x_946 = x_945;
}
lean_ctor_set(x_946, 0, x_944);
return x_946;
}
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; 
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_867);
lean_dec_ref(x_866);
lean_dec(x_865);
lean_dec_ref(x_864);
lean_dec(x_863);
lean_dec(x_861);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_947 = lean_ctor_get(x_874, 0);
lean_inc(x_947);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 x_948 = x_874;
} else {
 lean_dec_ref(x_874);
 x_948 = lean_box(0);
}
if (lean_is_scalar(x_948)) {
 x_949 = lean_alloc_ctor(1, 1, 0);
} else {
 x_949 = x_948;
}
lean_ctor_set(x_949, 0, x_947);
return x_949;
}
}
else
{
lean_object* x_950; 
lean_dec(x_867);
lean_dec_ref(x_866);
lean_dec(x_865);
lean_dec_ref(x_864);
lean_dec(x_863);
lean_dec(x_861);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_950 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_950;
}
}
else
{
lean_object* x_951; lean_object* x_952; 
lean_dec_ref(x_858);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_951 = lean_ctor_get(x_860, 0);
lean_inc(x_951);
lean_dec_ref(x_860);
if (lean_is_scalar(x_861)) {
 x_952 = lean_alloc_ctor(0, 1, 0);
} else {
 x_952 = x_861;
}
lean_ctor_set(x_952, 0, x_951);
return x_952;
}
}
else
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; 
lean_dec_ref(x_858);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_953 = lean_ctor_get(x_859, 0);
lean_inc(x_953);
if (lean_is_exclusive(x_859)) {
 lean_ctor_release(x_859, 0);
 x_954 = x_859;
} else {
 lean_dec_ref(x_859);
 x_954 = lean_box(0);
}
if (lean_is_scalar(x_954)) {
 x_955 = lean_alloc_ctor(1, 1, 0);
} else {
 x_955 = x_954;
}
lean_ctor_set(x_955, 0, x_953);
return x_955;
}
}
case 5:
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_956 = lean_ctor_get(x_1, 0);
x_957 = lean_st_ref_get(x_3);
x_958 = lean_ctor_get(x_957, 0);
lean_inc_ref(x_958);
lean_dec_ref(x_957);
lean_inc(x_956);
x_959 = l_Lean_Compiler_LCNF_normFVarImp(x_958, x_956, x_52);
lean_dec_ref(x_958);
if (lean_obj_tag(x_959) == 0)
{
lean_object* x_960; lean_object* x_961; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_960 = lean_ctor_get(x_959, 0);
lean_inc(x_960);
lean_dec_ref(x_959);
lean_inc(x_960);
x_961 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_960, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; uint8_t x_963; 
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 x_962 = x_961;
} else {
 lean_dec_ref(x_961);
 x_962 = lean_box(0);
}
x_963 = l_Lean_instBEqFVarId_beq(x_956, x_960);
if (x_963 == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_964 = x_1;
} else {
 lean_dec_ref(x_1);
 x_964 = lean_box(0);
}
if (lean_is_scalar(x_964)) {
 x_965 = lean_alloc_ctor(5, 1, 0);
} else {
 x_965 = x_964;
}
lean_ctor_set(x_965, 0, x_960);
if (lean_is_scalar(x_962)) {
 x_966 = lean_alloc_ctor(0, 1, 0);
} else {
 x_966 = x_962;
}
lean_ctor_set(x_966, 0, x_965);
return x_966;
}
else
{
lean_object* x_967; 
lean_dec(x_960);
if (lean_is_scalar(x_962)) {
 x_967 = lean_alloc_ctor(0, 1, 0);
} else {
 x_967 = x_962;
}
lean_ctor_set(x_967, 0, x_1);
return x_967;
}
}
else
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; 
lean_dec(x_960);
lean_dec_ref(x_1);
x_968 = lean_ctor_get(x_961, 0);
lean_inc(x_968);
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 x_969 = x_961;
} else {
 lean_dec_ref(x_961);
 x_969 = lean_box(0);
}
if (lean_is_scalar(x_969)) {
 x_970 = lean_alloc_ctor(1, 1, 0);
} else {
 x_970 = x_969;
}
lean_ctor_set(x_970, 0, x_968);
return x_970;
}
}
else
{
lean_object* x_971; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_971 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_971;
}
}
case 6:
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; size_t x_976; size_t x_977; uint8_t x_978; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_972 = lean_ctor_get(x_1, 0);
x_973 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_974 = lean_ctor_get(x_973, 0);
lean_inc_ref(x_974);
lean_dec_ref(x_973);
lean_inc_ref(x_972);
x_975 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_974, x_52, x_972);
lean_dec_ref(x_974);
x_976 = lean_ptr_addr(x_972);
x_977 = lean_ptr_addr(x_975);
x_978 = lean_usize_dec_eq(x_976, x_977);
if (x_978 == 0)
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_979 = x_1;
} else {
 lean_dec_ref(x_1);
 x_979 = lean_box(0);
}
if (lean_is_scalar(x_979)) {
 x_980 = lean_alloc_ctor(6, 1, 0);
} else {
 x_980 = x_979;
}
lean_ctor_set(x_980, 0, x_975);
x_981 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_981, 0, x_980);
return x_981;
}
else
{
lean_object* x_982; 
lean_dec_ref(x_975);
x_982 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_982, 0, x_1);
return x_982;
}
}
default: 
{
lean_object* x_983; lean_object* x_984; 
x_983 = lean_ctor_get(x_1, 0);
x_984 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_984);
lean_inc_ref(x_983);
x_585 = x_983;
x_586 = x_984;
x_587 = x_2;
x_588 = x_3;
x_589 = x_4;
x_590 = x_5;
x_591 = x_6;
x_592 = x_7;
x_593 = x_8;
goto block_632;
}
}
block_632:
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_594 = lean_ctor_get(x_585, 0);
x_595 = lean_ctor_get(x_585, 2);
x_596 = lean_ctor_get(x_585, 3);
x_597 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_594, x_588);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; uint8_t x_600; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
lean_dec_ref(x_597);
lean_inc(x_598);
lean_inc_ref(x_1);
lean_inc_ref(x_586);
x_599 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_599, 0, x_586);
lean_closure_set(x_599, 1, x_1);
lean_closure_set(x_599, 2, x_598);
x_600 = lean_unbox(x_598);
if (x_600 == 0)
{
uint8_t x_601; 
lean_dec(x_598);
lean_dec_ref(x_586);
x_601 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_601 == 0)
{
x_18 = x_599;
x_19 = x_585;
x_20 = x_587;
x_21 = x_588;
x_22 = x_589;
x_23 = x_590;
x_24 = x_591;
x_25 = x_592;
x_26 = x_593;
x_27 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_602; 
lean_inc_ref(x_596);
x_602 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_596, x_595);
if (x_602 == 0)
{
x_18 = x_599;
x_19 = x_585;
x_20 = x_587;
x_21 = x_588;
x_22 = x_589;
x_23 = x_590;
x_24 = x_591;
x_25 = x_592;
x_26 = x_593;
x_27 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_st_ref_get(x_588);
x_604 = lean_ctor_get(x_603, 0);
lean_inc_ref(x_604);
lean_dec_ref(x_603);
x_605 = l_Lean_Compiler_LCNF_normFunDeclImp(x_52, x_585, x_604, x_590, x_591, x_592, x_593);
lean_dec_ref(x_604);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
lean_dec_ref(x_605);
lean_inc(x_593);
lean_inc_ref(x_592);
lean_inc(x_591);
lean_inc_ref(x_590);
x_607 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_606, x_590, x_591, x_592, x_593);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; 
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
lean_dec_ref(x_607);
x_609 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_588);
if (lean_obj_tag(x_609) == 0)
{
lean_dec_ref(x_609);
x_18 = x_599;
x_19 = x_608;
x_20 = x_587;
x_21 = x_588;
x_22 = x_589;
x_23 = x_590;
x_24 = x_591;
x_25 = x_592;
x_26 = x_593;
x_27 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_608);
lean_dec_ref(x_599);
lean_dec(x_593);
lean_dec_ref(x_592);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec_ref(x_589);
lean_dec(x_588);
lean_dec_ref(x_587);
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 x_611 = x_609;
} else {
 lean_dec_ref(x_609);
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
lean_dec_ref(x_599);
lean_dec(x_593);
lean_dec_ref(x_592);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec_ref(x_589);
lean_dec(x_588);
lean_dec_ref(x_587);
x_613 = lean_ctor_get(x_607, 0);
lean_inc(x_613);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 x_614 = x_607;
} else {
 lean_dec_ref(x_607);
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
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec_ref(x_599);
lean_dec(x_593);
lean_dec_ref(x_592);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec_ref(x_589);
lean_dec(x_588);
lean_dec_ref(x_587);
x_616 = lean_ctor_get(x_605, 0);
lean_inc(x_616);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 x_617 = x_605;
} else {
 lean_dec_ref(x_605);
 x_617 = lean_box(0);
}
if (lean_is_scalar(x_617)) {
 x_618 = lean_alloc_ctor(1, 1, 0);
} else {
 x_618 = x_617;
}
lean_ctor_set(x_618, 0, x_616);
return x_618;
}
}
}
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec_ref(x_599);
x_619 = lean_st_ref_get(x_588);
x_620 = lean_ctor_get(x_619, 0);
lean_inc_ref(x_620);
lean_dec_ref(x_619);
x_621 = l_Lean_Compiler_LCNF_normFunDeclImp(x_52, x_585, x_620, x_590, x_591, x_592, x_593);
lean_dec_ref(x_620);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; uint8_t x_624; lean_object* x_625; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
lean_dec_ref(x_621);
x_623 = lean_box(0);
x_624 = lean_unbox(x_598);
lean_dec(x_598);
x_625 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_586, x_1, x_624, x_622, x_623, x_587, x_588, x_589, x_590, x_591, x_592, x_593);
return x_625;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_598);
lean_dec(x_593);
lean_dec_ref(x_592);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec_ref(x_589);
lean_dec(x_588);
lean_dec_ref(x_587);
lean_dec_ref(x_586);
lean_dec_ref(x_1);
x_626 = lean_ctor_get(x_621, 0);
lean_inc(x_626);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 x_627 = x_621;
} else {
 lean_dec_ref(x_621);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(1, 1, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_626);
return x_628;
}
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_593);
lean_dec_ref(x_592);
lean_dec(x_591);
lean_dec_ref(x_590);
lean_dec_ref(x_589);
lean_dec(x_588);
lean_dec_ref(x_587);
lean_dec_ref(x_586);
lean_dec_ref(x_585);
lean_dec_ref(x_1);
x_629 = lean_ctor_get(x_597, 0);
lean_inc(x_629);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 x_630 = x_597;
} else {
 lean_dec_ref(x_597);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(1, 1, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_629);
return x_631;
}
}
}
}
else
{
uint8_t x_985; 
lean_free_object(x_7);
lean_dec_ref(x_51);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_985 = !lean_is_exclusive(x_68);
if (x_985 == 0)
{
return x_68;
}
else
{
lean_object* x_986; lean_object* x_987; 
x_986 = lean_ctor_get(x_68, 0);
lean_inc(x_986);
lean_dec(x_68);
x_987 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_987, 0, x_986);
return x_987;
}
}
}
else
{
lean_object* x_988; 
lean_dec(x_7);
x_988 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3);
if (lean_obj_tag(x_988) == 0)
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 x_989 = x_988;
} else {
 lean_dec_ref(x_988);
 x_989 = lean_box(0);
}
x_1038 = lean_unsigned_to_nat(1u);
x_1039 = lean_nat_add(x_39, x_1038);
lean_dec(x_39);
x_1040 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_1040, 0, x_36);
lean_ctor_set(x_1040, 1, x_37);
lean_ctor_set(x_1040, 2, x_38);
lean_ctor_set(x_1040, 3, x_1039);
lean_ctor_set(x_1040, 4, x_40);
lean_ctor_set(x_1040, 5, x_41);
lean_ctor_set(x_1040, 6, x_42);
lean_ctor_set(x_1040, 7, x_43);
lean_ctor_set(x_1040, 8, x_44);
lean_ctor_set(x_1040, 9, x_45);
lean_ctor_set(x_1040, 10, x_46);
lean_ctor_set(x_1040, 11, x_47);
lean_ctor_set(x_1040, 12, x_49);
lean_ctor_set(x_1040, 13, x_51);
lean_ctor_set_uint8(x_1040, sizeof(void*)*14, x_48);
lean_ctor_set_uint8(x_1040, sizeof(void*)*14 + 1, x_50);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; uint8_t x_1052; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1180; 
lean_dec(x_989);
x_1041 = lean_ctor_get(x_1, 0);
x_1042 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1041);
x_1180 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_52, x_1041, x_3, x_6);
if (lean_obj_tag(x_1180) == 0)
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; uint8_t x_1215; 
x_1181 = lean_ctor_get(x_1180, 0);
lean_inc(x_1181);
lean_dec_ref(x_1180);
x_1215 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_1041, x_1181);
if (x_1215 == 0)
{
goto block_1214;
}
else
{
if (x_52 == 0)
{
x_1182 = x_2;
x_1183 = x_3;
x_1184 = x_4;
x_1185 = x_5;
x_1186 = x_6;
x_1187 = x_1040;
x_1188 = x_8;
x_1189 = lean_box(0);
goto block_1209;
}
else
{
goto block_1214;
}
}
block_1209:
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1190 = lean_ctor_get(x_1181, 2);
x_1191 = lean_ctor_get(x_1181, 3);
lean_inc(x_1188);
lean_inc_ref(x_1187);
lean_inc(x_1186);
lean_inc_ref(x_1185);
lean_inc_ref(x_1184);
lean_inc(x_1191);
x_1192 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_1191, x_1182, x_1184, x_1185, x_1186, x_1187, x_1188);
if (lean_obj_tag(x_1192) == 0)
{
lean_object* x_1193; 
x_1193 = lean_ctor_get(x_1192, 0);
lean_inc(x_1193);
lean_dec_ref(x_1192);
if (lean_obj_tag(x_1193) == 0)
{
lean_inc(x_1191);
lean_inc_ref(x_1190);
x_1165 = x_1181;
x_1166 = x_1190;
x_1167 = x_1191;
x_1168 = x_1182;
x_1169 = x_1183;
x_1170 = x_1184;
x_1171 = x_1185;
x_1172 = x_1186;
x_1173 = x_1187;
x_1174 = x_1188;
x_1175 = lean_box(0);
goto block_1179;
}
else
{
lean_object* x_1194; lean_object* x_1195; 
x_1194 = lean_ctor_get(x_1193, 0);
lean_inc(x_1194);
lean_dec_ref(x_1193);
x_1195 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1183);
if (lean_obj_tag(x_1195) == 0)
{
lean_object* x_1196; 
lean_dec_ref(x_1195);
x_1196 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_1181, x_1194, x_1186);
if (lean_obj_tag(x_1196) == 0)
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
x_1197 = lean_ctor_get(x_1196, 0);
lean_inc(x_1197);
lean_dec_ref(x_1196);
x_1198 = lean_ctor_get(x_1197, 2);
lean_inc_ref(x_1198);
x_1199 = lean_ctor_get(x_1197, 3);
lean_inc(x_1199);
x_1165 = x_1197;
x_1166 = x_1198;
x_1167 = x_1199;
x_1168 = x_1182;
x_1169 = x_1183;
x_1170 = x_1184;
x_1171 = x_1185;
x_1172 = x_1186;
x_1173 = x_1187;
x_1174 = x_1188;
x_1175 = lean_box(0);
goto block_1179;
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec_ref(x_1184);
lean_dec(x_1183);
lean_dec_ref(x_1182);
lean_dec_ref(x_1);
x_1200 = lean_ctor_get(x_1196, 0);
lean_inc(x_1200);
if (lean_is_exclusive(x_1196)) {
 lean_ctor_release(x_1196, 0);
 x_1201 = x_1196;
} else {
 lean_dec_ref(x_1196);
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
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
lean_dec(x_1194);
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec_ref(x_1184);
lean_dec(x_1183);
lean_dec_ref(x_1182);
lean_dec(x_1181);
lean_dec_ref(x_1);
x_1203 = lean_ctor_get(x_1195, 0);
lean_inc(x_1203);
if (lean_is_exclusive(x_1195)) {
 lean_ctor_release(x_1195, 0);
 x_1204 = x_1195;
} else {
 lean_dec_ref(x_1195);
 x_1204 = lean_box(0);
}
if (lean_is_scalar(x_1204)) {
 x_1205 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1205 = x_1204;
}
lean_ctor_set(x_1205, 0, x_1203);
return x_1205;
}
}
}
else
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec_ref(x_1184);
lean_dec(x_1183);
lean_dec_ref(x_1182);
lean_dec(x_1181);
lean_dec_ref(x_1);
x_1206 = lean_ctor_get(x_1192, 0);
lean_inc(x_1206);
if (lean_is_exclusive(x_1192)) {
 lean_ctor_release(x_1192, 0);
 x_1207 = x_1192;
} else {
 lean_dec_ref(x_1192);
 x_1207 = lean_box(0);
}
if (lean_is_scalar(x_1207)) {
 x_1208 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1208 = x_1207;
}
lean_ctor_set(x_1208, 0, x_1206);
return x_1208;
}
}
block_1214:
{
lean_object* x_1210; 
x_1210 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_1210) == 0)
{
lean_dec_ref(x_1210);
x_1182 = x_2;
x_1183 = x_3;
x_1184 = x_4;
x_1185 = x_5;
x_1186 = x_6;
x_1187 = x_1040;
x_1188 = x_8;
x_1189 = lean_box(0);
goto block_1209;
}
else
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
lean_dec(x_1181);
lean_dec_ref(x_1040);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1211 = lean_ctor_get(x_1210, 0);
lean_inc(x_1211);
if (lean_is_exclusive(x_1210)) {
 lean_ctor_release(x_1210, 0);
 x_1212 = x_1210;
} else {
 lean_dec_ref(x_1210);
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
}
else
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
lean_dec_ref(x_1040);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1216 = lean_ctor_get(x_1180, 0);
lean_inc(x_1216);
if (lean_is_exclusive(x_1180)) {
 lean_ctor_release(x_1180, 0);
 x_1217 = x_1180;
} else {
 lean_dec_ref(x_1180);
 x_1217 = lean_box(0);
}
if (lean_is_scalar(x_1217)) {
 x_1218 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1218 = x_1217;
}
lean_ctor_set(x_1218, 0, x_1216);
return x_1218;
}
block_1164:
{
if (x_1052 == 0)
{
lean_object* x_1053; 
lean_inc(x_1043);
lean_inc_ref(x_1051);
lean_inc(x_1045);
lean_inc_ref(x_1047);
lean_inc_ref(x_1044);
x_1053 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_1044, x_1047, x_1045, x_1051, x_1043);
if (lean_obj_tag(x_1053) == 0)
{
lean_object* x_1054; 
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
lean_dec_ref(x_1053);
if (lean_obj_tag(x_1054) == 0)
{
lean_object* x_1055; 
lean_inc(x_1043);
lean_inc_ref(x_1051);
lean_inc(x_1045);
lean_inc_ref(x_1047);
lean_inc_ref(x_1044);
x_1055 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1044, x_1050, x_1049, x_1047, x_1045, x_1051, x_1043);
if (lean_obj_tag(x_1055) == 0)
{
lean_object* x_1056; 
x_1056 = lean_ctor_get(x_1055, 0);
lean_inc(x_1056);
lean_dec_ref(x_1055);
if (lean_obj_tag(x_1056) == 0)
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
x_1057 = lean_ctor_get(x_1044, 0);
x_1058 = lean_ctor_get(x_1044, 3);
x_1059 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1058);
x_1060 = lean_ctor_get(x_1059, 0);
lean_inc(x_1060);
lean_dec_ref(x_1059);
if (lean_obj_tag(x_1060) == 0)
{
lean_object* x_1061; 
lean_inc(x_1043);
lean_inc_ref(x_1051);
lean_inc(x_1045);
lean_inc_ref(x_1047);
lean_inc_ref(x_1048);
lean_inc(x_1049);
lean_inc_ref(x_1050);
lean_inc_ref(x_1042);
lean_inc_ref(x_1044);
x_1061 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1044, x_1042, x_1050, x_1049, x_1048, x_1047, x_1045, x_1051, x_1043);
if (lean_obj_tag(x_1061) == 0)
{
lean_object* x_1062; 
x_1062 = lean_ctor_get(x_1061, 0);
lean_inc(x_1062);
lean_dec_ref(x_1061);
if (lean_obj_tag(x_1062) == 0)
{
lean_object* x_1063; 
lean_inc(x_1043);
lean_inc_ref(x_1051);
lean_inc(x_1045);
lean_inc_ref(x_1047);
lean_inc_ref(x_1048);
lean_inc(x_1049);
lean_inc_ref(x_1050);
lean_inc(x_1058);
x_1063 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_1058, x_1050, x_1049, x_1048, x_1047, x_1045, x_1051, x_1043);
if (lean_obj_tag(x_1063) == 0)
{
lean_object* x_1064; 
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
lean_dec_ref(x_1063);
if (lean_obj_tag(x_1064) == 0)
{
lean_object* x_1065; 
lean_inc(x_1043);
lean_inc_ref(x_1051);
lean_inc(x_1045);
lean_inc_ref(x_1047);
lean_inc_ref(x_1048);
lean_inc(x_1049);
lean_inc_ref(x_1050);
lean_inc_ref(x_1042);
x_1065 = l_Lean_Compiler_LCNF_Simp_simp(x_1042, x_1050, x_1049, x_1048, x_1047, x_1045, x_1051, x_1043);
if (lean_obj_tag(x_1065) == 0)
{
lean_object* x_1066; lean_object* x_1067; 
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
lean_dec_ref(x_1065);
x_1067 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_1057, x_1049);
if (lean_obj_tag(x_1067) == 0)
{
lean_object* x_1068; uint8_t x_1069; 
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
lean_dec_ref(x_1067);
x_1069 = lean_unbox(x_1068);
lean_dec(x_1068);
if (x_1069 == 0)
{
lean_object* x_1070; 
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1043);
lean_dec_ref(x_1);
x_1070 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1044, x_1049, x_1045);
lean_dec(x_1045);
lean_dec(x_1049);
lean_dec_ref(x_1044);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; 
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 x_1071 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1071 = lean_box(0);
}
if (lean_is_scalar(x_1071)) {
 x_1072 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1072 = x_1071;
}
lean_ctor_set(x_1072, 0, x_1066);
return x_1072;
}
else
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
lean_dec(x_1066);
x_1073 = lean_ctor_get(x_1070, 0);
lean_inc(x_1073);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 x_1074 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1074 = lean_box(0);
}
if (lean_is_scalar(x_1074)) {
 x_1075 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1075 = x_1074;
}
lean_ctor_set(x_1075, 0, x_1073);
return x_1075;
}
}
else
{
lean_object* x_1076; 
lean_inc_ref(x_1044);
x_1076 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_1044, x_1050, x_1049, x_1048, x_1047, x_1045, x_1051, x_1043);
lean_dec(x_1043);
lean_dec_ref(x_1051);
lean_dec(x_1045);
lean_dec_ref(x_1047);
lean_dec_ref(x_1048);
lean_dec(x_1049);
lean_dec_ref(x_1050);
if (lean_obj_tag(x_1076) == 0)
{
size_t x_1077; size_t x_1078; uint8_t x_1079; 
lean_dec_ref(x_1076);
x_1077 = lean_ptr_addr(x_1042);
x_1078 = lean_ptr_addr(x_1066);
x_1079 = lean_usize_dec_eq(x_1077, x_1078);
if (x_1079 == 0)
{
x_10 = x_1044;
x_11 = lean_box(0);
x_12 = x_1066;
x_13 = x_1079;
goto block_17;
}
else
{
size_t x_1080; size_t x_1081; uint8_t x_1082; 
x_1080 = lean_ptr_addr(x_1041);
x_1081 = lean_ptr_addr(x_1044);
x_1082 = lean_usize_dec_eq(x_1080, x_1081);
x_10 = x_1044;
x_11 = lean_box(0);
x_12 = x_1066;
x_13 = x_1082;
goto block_17;
}
}
else
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
lean_dec(x_1066);
lean_dec_ref(x_1044);
lean_dec_ref(x_1);
x_1083 = lean_ctor_get(x_1076, 0);
lean_inc(x_1083);
if (lean_is_exclusive(x_1076)) {
 lean_ctor_release(x_1076, 0);
 x_1084 = x_1076;
} else {
 lean_dec_ref(x_1076);
 x_1084 = lean_box(0);
}
if (lean_is_scalar(x_1084)) {
 x_1085 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1085 = x_1084;
}
lean_ctor_set(x_1085, 0, x_1083);
return x_1085;
}
}
}
else
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
lean_dec(x_1066);
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec_ref(x_1044);
lean_dec(x_1043);
lean_dec_ref(x_1);
x_1086 = lean_ctor_get(x_1067, 0);
lean_inc(x_1086);
if (lean_is_exclusive(x_1067)) {
 lean_ctor_release(x_1067, 0);
 x_1087 = x_1067;
} else {
 lean_dec_ref(x_1067);
 x_1087 = lean_box(0);
}
if (lean_is_scalar(x_1087)) {
 x_1088 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1088 = x_1087;
}
lean_ctor_set(x_1088, 0, x_1086);
return x_1088;
}
}
else
{
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec_ref(x_1044);
lean_dec(x_1043);
lean_dec_ref(x_1);
return x_1065;
}
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
lean_inc_ref(x_1042);
lean_dec_ref(x_1);
x_1089 = lean_ctor_get(x_1064, 0);
lean_inc(x_1089);
lean_dec_ref(x_1064);
x_1090 = lean_ctor_get(x_1089, 0);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_1089, 1);
lean_inc(x_1091);
lean_dec(x_1089);
lean_inc(x_1057);
x_1092 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1057, x_1091, x_1049, x_1045, x_1051, x_1043);
if (lean_obj_tag(x_1092) == 0)
{
lean_object* x_1093; 
lean_dec_ref(x_1092);
x_1093 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1044, x_1049, x_1045);
lean_dec_ref(x_1044);
if (lean_obj_tag(x_1093) == 0)
{
lean_object* x_1094; 
lean_dec_ref(x_1093);
lean_inc(x_1043);
lean_inc_ref(x_1051);
lean_inc(x_1045);
lean_inc_ref(x_1047);
lean_inc_ref(x_1048);
lean_inc(x_1049);
lean_inc_ref(x_1050);
x_1094 = l_Lean_Compiler_LCNF_Simp_simp(x_1042, x_1050, x_1049, x_1048, x_1047, x_1045, x_1051, x_1043);
if (lean_obj_tag(x_1094) == 0)
{
lean_object* x_1095; lean_object* x_1096; 
x_1095 = lean_ctor_get(x_1094, 0);
lean_inc(x_1095);
lean_dec_ref(x_1094);
x_1096 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1090, x_1095, x_1050, x_1049, x_1048, x_1047, x_1045, x_1051, x_1043);
lean_dec(x_1043);
lean_dec_ref(x_1051);
lean_dec(x_1045);
lean_dec_ref(x_1047);
lean_dec_ref(x_1048);
lean_dec(x_1049);
lean_dec_ref(x_1050);
lean_dec(x_1090);
return x_1096;
}
else
{
lean_dec(x_1090);
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec(x_1043);
return x_1094;
}
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
lean_dec(x_1090);
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec(x_1043);
lean_dec_ref(x_1042);
x_1097 = lean_ctor_get(x_1093, 0);
lean_inc(x_1097);
if (lean_is_exclusive(x_1093)) {
 lean_ctor_release(x_1093, 0);
 x_1098 = x_1093;
} else {
 lean_dec_ref(x_1093);
 x_1098 = lean_box(0);
}
if (lean_is_scalar(x_1098)) {
 x_1099 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1099 = x_1098;
}
lean_ctor_set(x_1099, 0, x_1097);
return x_1099;
}
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
lean_dec(x_1090);
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec_ref(x_1044);
lean_dec(x_1043);
lean_dec_ref(x_1042);
x_1100 = lean_ctor_get(x_1092, 0);
lean_inc(x_1100);
if (lean_is_exclusive(x_1092)) {
 lean_ctor_release(x_1092, 0);
 x_1101 = x_1092;
} else {
 lean_dec_ref(x_1092);
 x_1101 = lean_box(0);
}
if (lean_is_scalar(x_1101)) {
 x_1102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1102 = x_1101;
}
lean_ctor_set(x_1102, 0, x_1100);
return x_1102;
}
}
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec_ref(x_1044);
lean_dec(x_1043);
lean_dec_ref(x_1);
x_1103 = lean_ctor_get(x_1063, 0);
lean_inc(x_1103);
if (lean_is_exclusive(x_1063)) {
 lean_ctor_release(x_1063, 0);
 x_1104 = x_1063;
} else {
 lean_dec_ref(x_1063);
 x_1104 = lean_box(0);
}
if (lean_is_scalar(x_1104)) {
 x_1105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1105 = x_1104;
}
lean_ctor_set(x_1105, 0, x_1103);
return x_1105;
}
}
else
{
lean_object* x_1106; lean_object* x_1107; 
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1043);
lean_dec_ref(x_1);
x_1106 = lean_ctor_get(x_1062, 0);
lean_inc(x_1106);
lean_dec_ref(x_1062);
x_1107 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1044, x_1049, x_1045);
lean_dec(x_1045);
lean_dec(x_1049);
lean_dec_ref(x_1044);
if (lean_obj_tag(x_1107) == 0)
{
lean_object* x_1108; lean_object* x_1109; 
if (lean_is_exclusive(x_1107)) {
 lean_ctor_release(x_1107, 0);
 x_1108 = x_1107;
} else {
 lean_dec_ref(x_1107);
 x_1108 = lean_box(0);
}
if (lean_is_scalar(x_1108)) {
 x_1109 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1109 = x_1108;
}
lean_ctor_set(x_1109, 0, x_1106);
return x_1109;
}
else
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; 
lean_dec(x_1106);
x_1110 = lean_ctor_get(x_1107, 0);
lean_inc(x_1110);
if (lean_is_exclusive(x_1107)) {
 lean_ctor_release(x_1107, 0);
 x_1111 = x_1107;
} else {
 lean_dec_ref(x_1107);
 x_1111 = lean_box(0);
}
if (lean_is_scalar(x_1111)) {
 x_1112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1112 = x_1111;
}
lean_ctor_set(x_1112, 0, x_1110);
return x_1112;
}
}
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec_ref(x_1044);
lean_dec(x_1043);
lean_dec_ref(x_1);
x_1113 = lean_ctor_get(x_1061, 0);
lean_inc(x_1113);
if (lean_is_exclusive(x_1061)) {
 lean_ctor_release(x_1061, 0);
 x_1114 = x_1061;
} else {
 lean_dec_ref(x_1061);
 x_1114 = lean_box(0);
}
if (lean_is_scalar(x_1114)) {
 x_1115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1115 = x_1114;
}
lean_ctor_set(x_1115, 0, x_1113);
return x_1115;
}
}
else
{
lean_object* x_1116; lean_object* x_1117; 
lean_inc_ref(x_1042);
lean_dec_ref(x_1);
x_1116 = lean_ctor_get(x_1060, 0);
lean_inc(x_1116);
lean_dec_ref(x_1060);
lean_inc(x_1057);
x_1117 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1057, x_1116, x_1049, x_1045, x_1051, x_1043);
if (lean_obj_tag(x_1117) == 0)
{
lean_object* x_1118; 
lean_dec_ref(x_1117);
x_1118 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1044, x_1049, x_1045);
lean_dec_ref(x_1044);
if (lean_obj_tag(x_1118) == 0)
{
lean_dec_ref(x_1118);
x_1 = x_1042;
x_2 = x_1050;
x_3 = x_1049;
x_4 = x_1048;
x_5 = x_1047;
x_6 = x_1045;
x_7 = x_1051;
x_8 = x_1043;
goto _start;
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec(x_1043);
lean_dec_ref(x_1042);
x_1120 = lean_ctor_get(x_1118, 0);
lean_inc(x_1120);
if (lean_is_exclusive(x_1118)) {
 lean_ctor_release(x_1118, 0);
 x_1121 = x_1118;
} else {
 lean_dec_ref(x_1118);
 x_1121 = lean_box(0);
}
if (lean_is_scalar(x_1121)) {
 x_1122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1122 = x_1121;
}
lean_ctor_set(x_1122, 0, x_1120);
return x_1122;
}
}
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec_ref(x_1044);
lean_dec(x_1043);
lean_dec_ref(x_1042);
x_1123 = lean_ctor_get(x_1117, 0);
lean_inc(x_1123);
if (lean_is_exclusive(x_1117)) {
 lean_ctor_release(x_1117, 0);
 x_1124 = x_1117;
} else {
 lean_dec_ref(x_1117);
 x_1124 = lean_box(0);
}
if (lean_is_scalar(x_1124)) {
 x_1125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1125 = x_1124;
}
lean_ctor_set(x_1125, 0, x_1123);
return x_1125;
}
}
}
else
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
lean_dec_ref(x_1044);
lean_inc_ref(x_1042);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1126 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1126 = lean_box(0);
}
x_1127 = lean_ctor_get(x_1056, 0);
lean_inc(x_1127);
lean_dec_ref(x_1056);
if (lean_is_scalar(x_1126)) {
 x_1128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1128 = x_1126;
 lean_ctor_set_tag(x_1128, 1);
}
lean_ctor_set(x_1128, 0, x_1127);
lean_ctor_set(x_1128, 1, x_1042);
x_1 = x_1128;
x_2 = x_1050;
x_3 = x_1049;
x_4 = x_1048;
x_5 = x_1047;
x_6 = x_1045;
x_7 = x_1051;
x_8 = x_1043;
goto _start;
}
}
else
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec_ref(x_1044);
lean_dec(x_1043);
lean_dec_ref(x_1);
x_1130 = lean_ctor_get(x_1055, 0);
lean_inc(x_1130);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 x_1131 = x_1055;
} else {
 lean_dec_ref(x_1055);
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
lean_object* x_1133; lean_object* x_1134; 
lean_dec_ref(x_1044);
lean_inc_ref(x_1042);
lean_dec_ref(x_1);
x_1133 = lean_ctor_get(x_1054, 0);
lean_inc(x_1133);
lean_dec_ref(x_1054);
x_1134 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1049);
if (lean_obj_tag(x_1134) == 0)
{
lean_object* x_1135; 
lean_dec_ref(x_1134);
lean_inc(x_1043);
lean_inc_ref(x_1051);
lean_inc(x_1045);
lean_inc_ref(x_1047);
lean_inc_ref(x_1048);
lean_inc(x_1049);
lean_inc_ref(x_1050);
x_1135 = l_Lean_Compiler_LCNF_Simp_simp(x_1042, x_1050, x_1049, x_1048, x_1047, x_1045, x_1051, x_1043);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; lean_object* x_1137; 
x_1136 = lean_ctor_get(x_1135, 0);
lean_inc(x_1136);
lean_dec_ref(x_1135);
x_1137 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1133, x_1136, x_1050, x_1049, x_1048, x_1047, x_1045, x_1051, x_1043);
lean_dec(x_1043);
lean_dec_ref(x_1051);
lean_dec(x_1045);
lean_dec_ref(x_1047);
lean_dec_ref(x_1048);
lean_dec(x_1049);
lean_dec_ref(x_1050);
lean_dec(x_1133);
return x_1137;
}
else
{
lean_dec(x_1133);
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec(x_1043);
return x_1135;
}
}
else
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
lean_dec(x_1133);
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec(x_1043);
lean_dec_ref(x_1042);
x_1138 = lean_ctor_get(x_1134, 0);
lean_inc(x_1138);
if (lean_is_exclusive(x_1134)) {
 lean_ctor_release(x_1134, 0);
 x_1139 = x_1134;
} else {
 lean_dec_ref(x_1134);
 x_1139 = lean_box(0);
}
if (lean_is_scalar(x_1139)) {
 x_1140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1140 = x_1139;
}
lean_ctor_set(x_1140, 0, x_1138);
return x_1140;
}
}
}
else
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec_ref(x_1044);
lean_dec(x_1043);
lean_dec_ref(x_1);
x_1141 = lean_ctor_get(x_1053, 0);
lean_inc(x_1141);
if (lean_is_exclusive(x_1053)) {
 lean_ctor_release(x_1053, 0);
 x_1142 = x_1053;
} else {
 lean_dec_ref(x_1053);
 x_1142 = lean_box(0);
}
if (lean_is_scalar(x_1142)) {
 x_1143 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1143 = x_1142;
}
lean_ctor_set(x_1143, 0, x_1141);
return x_1143;
}
}
else
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; uint8_t x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
lean_inc_ref(x_1042);
lean_dec_ref(x_1);
x_1144 = lean_st_ref_take(x_1049);
x_1145 = lean_ctor_get(x_1044, 0);
x_1146 = lean_ctor_get(x_1144, 0);
lean_inc_ref(x_1146);
x_1147 = lean_ctor_get(x_1144, 1);
lean_inc_ref(x_1147);
x_1148 = lean_ctor_get(x_1144, 2);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1144, 3);
lean_inc_ref(x_1149);
x_1150 = lean_ctor_get_uint8(x_1144, sizeof(void*)*7);
x_1151 = lean_ctor_get(x_1144, 4);
lean_inc(x_1151);
x_1152 = lean_ctor_get(x_1144, 5);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1144, 6);
lean_inc(x_1153);
if (lean_is_exclusive(x_1144)) {
 lean_ctor_release(x_1144, 0);
 lean_ctor_release(x_1144, 1);
 lean_ctor_release(x_1144, 2);
 lean_ctor_release(x_1144, 3);
 lean_ctor_release(x_1144, 4);
 lean_ctor_release(x_1144, 5);
 lean_ctor_release(x_1144, 6);
 x_1154 = x_1144;
} else {
 lean_dec_ref(x_1144);
 x_1154 = lean_box(0);
}
x_1155 = lean_box(0);
lean_inc(x_1145);
x_1156 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1146, x_1145, x_1155);
if (lean_is_scalar(x_1154)) {
 x_1157 = lean_alloc_ctor(0, 7, 1);
} else {
 x_1157 = x_1154;
}
lean_ctor_set(x_1157, 0, x_1156);
lean_ctor_set(x_1157, 1, x_1147);
lean_ctor_set(x_1157, 2, x_1148);
lean_ctor_set(x_1157, 3, x_1149);
lean_ctor_set(x_1157, 4, x_1151);
lean_ctor_set(x_1157, 5, x_1152);
lean_ctor_set(x_1157, 6, x_1153);
lean_ctor_set_uint8(x_1157, sizeof(void*)*7, x_1150);
x_1158 = lean_st_ref_set(x_1049, x_1157);
x_1159 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1044, x_1049, x_1045);
lean_dec_ref(x_1044);
if (lean_obj_tag(x_1159) == 0)
{
lean_dec_ref(x_1159);
x_1 = x_1042;
x_2 = x_1050;
x_3 = x_1049;
x_4 = x_1048;
x_5 = x_1047;
x_6 = x_1045;
x_7 = x_1051;
x_8 = x_1043;
goto _start;
}
else
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
lean_dec_ref(x_1051);
lean_dec_ref(x_1050);
lean_dec(x_1049);
lean_dec_ref(x_1048);
lean_dec_ref(x_1047);
lean_dec(x_1045);
lean_dec(x_1043);
lean_dec_ref(x_1042);
x_1161 = lean_ctor_get(x_1159, 0);
lean_inc(x_1161);
if (lean_is_exclusive(x_1159)) {
 lean_ctor_release(x_1159, 0);
 x_1162 = x_1159;
} else {
 lean_dec_ref(x_1159);
 x_1162 = lean_box(0);
}
if (lean_is_scalar(x_1162)) {
 x_1163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1163 = x_1162;
}
lean_ctor_set(x_1163, 0, x_1161);
return x_1163;
}
}
}
block_1179:
{
uint8_t x_1176; 
x_1176 = l_Lean_Expr_isErased(x_1166);
lean_dec_ref(x_1166);
if (x_1176 == 0)
{
lean_dec(x_1167);
x_1043 = x_1174;
x_1044 = x_1165;
x_1045 = x_1172;
x_1046 = lean_box(0);
x_1047 = x_1171;
x_1048 = x_1170;
x_1049 = x_1169;
x_1050 = x_1168;
x_1051 = x_1173;
x_1052 = x_52;
goto block_1164;
}
else
{
lean_object* x_1177; uint8_t x_1178; 
x_1177 = lean_box(1);
x_1178 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_1167, x_1177);
lean_dec(x_1167);
if (x_1178 == 0)
{
x_1043 = x_1174;
x_1044 = x_1165;
x_1045 = x_1172;
x_1046 = lean_box(0);
x_1047 = x_1171;
x_1048 = x_1170;
x_1049 = x_1169;
x_1050 = x_1168;
x_1051 = x_1173;
x_1052 = x_1176;
goto block_1164;
}
else
{
x_1043 = x_1174;
x_1044 = x_1165;
x_1045 = x_1172;
x_1046 = lean_box(0);
x_1047 = x_1171;
x_1048 = x_1170;
x_1049 = x_1169;
x_1050 = x_1168;
x_1051 = x_1173;
x_1052 = x_52;
goto block_1164;
}
}
}
}
case 3:
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; 
lean_dec(x_989);
x_1219 = lean_ctor_get(x_1, 0);
x_1220 = lean_ctor_get(x_1, 1);
x_1221 = lean_st_ref_get(x_3);
x_1222 = lean_ctor_get(x_1221, 0);
lean_inc_ref(x_1222);
lean_dec_ref(x_1221);
lean_inc(x_1219);
x_1223 = l_Lean_Compiler_LCNF_normFVarImp(x_1222, x_1219, x_52);
lean_dec_ref(x_1222);
if (lean_obj_tag(x_1223) == 0)
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; uint8_t x_1229; lean_object* x_1235; lean_object* x_1241; 
x_1224 = lean_ctor_get(x_1223, 0);
lean_inc(x_1224);
lean_dec_ref(x_1223);
lean_inc_ref(x_1220);
x_1225 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_52, x_1220, x_3);
x_1226 = lean_ctor_get(x_1225, 0);
lean_inc(x_1226);
if (lean_is_exclusive(x_1225)) {
 lean_ctor_release(x_1225, 0);
 x_1227 = x_1225;
} else {
 lean_dec_ref(x_1225);
 x_1227 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_1040);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1226);
x_1241 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1224, x_1226, x_2, x_3, x_4, x_5, x_6, x_1040, x_8);
if (lean_obj_tag(x_1241) == 0)
{
lean_object* x_1242; 
x_1242 = lean_ctor_get(x_1241, 0);
lean_inc(x_1242);
lean_dec_ref(x_1241);
if (lean_obj_tag(x_1242) == 0)
{
lean_object* x_1243; 
lean_dec_ref(x_1040);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_1224);
x_1243 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1224, x_3);
if (lean_obj_tag(x_1243) == 0)
{
lean_object* x_1244; lean_object* x_1245; uint8_t x_1246; 
lean_dec_ref(x_1243);
x_1244 = lean_unsigned_to_nat(0u);
x_1245 = lean_array_get_size(x_1226);
x_1246 = lean_nat_dec_lt(x_1244, x_1245);
if (x_1246 == 0)
{
lean_dec(x_1245);
lean_dec(x_3);
x_1235 = lean_box(0);
goto block_1240;
}
else
{
uint8_t x_1247; 
x_1247 = lean_nat_dec_le(x_1245, x_1245);
if (x_1247 == 0)
{
lean_dec(x_1245);
lean_dec(x_3);
x_1235 = lean_box(0);
goto block_1240;
}
else
{
lean_object* x_1248; size_t x_1249; size_t x_1250; lean_object* x_1251; 
x_1248 = lean_box(0);
x_1249 = 0;
x_1250 = lean_usize_of_nat(x_1245);
lean_dec(x_1245);
x_1251 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1226, x_1249, x_1250, x_1248, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1251) == 0)
{
lean_dec_ref(x_1251);
x_1235 = lean_box(0);
goto block_1240;
}
else
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; 
lean_dec(x_1227);
lean_dec(x_1226);
lean_dec(x_1224);
lean_dec_ref(x_1);
x_1252 = lean_ctor_get(x_1251, 0);
lean_inc(x_1252);
if (lean_is_exclusive(x_1251)) {
 lean_ctor_release(x_1251, 0);
 x_1253 = x_1251;
} else {
 lean_dec_ref(x_1251);
 x_1253 = lean_box(0);
}
if (lean_is_scalar(x_1253)) {
 x_1254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1254 = x_1253;
}
lean_ctor_set(x_1254, 0, x_1252);
return x_1254;
}
}
}
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
lean_dec(x_1227);
lean_dec(x_1226);
lean_dec(x_1224);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1255 = lean_ctor_get(x_1243, 0);
lean_inc(x_1255);
if (lean_is_exclusive(x_1243)) {
 lean_ctor_release(x_1243, 0);
 x_1256 = x_1243;
} else {
 lean_dec_ref(x_1243);
 x_1256 = lean_box(0);
}
if (lean_is_scalar(x_1256)) {
 x_1257 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1257 = x_1256;
}
lean_ctor_set(x_1257, 0, x_1255);
return x_1257;
}
}
else
{
lean_object* x_1258; 
lean_dec(x_1227);
lean_dec(x_1226);
lean_dec(x_1224);
lean_dec_ref(x_1);
x_1258 = lean_ctor_get(x_1242, 0);
lean_inc(x_1258);
lean_dec_ref(x_1242);
x_1 = x_1258;
x_7 = x_1040;
goto _start;
}
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
lean_dec(x_1227);
lean_dec(x_1226);
lean_dec(x_1224);
lean_dec_ref(x_1040);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1260 = lean_ctor_get(x_1241, 0);
lean_inc(x_1260);
if (lean_is_exclusive(x_1241)) {
 lean_ctor_release(x_1241, 0);
 x_1261 = x_1241;
} else {
 lean_dec_ref(x_1241);
 x_1261 = lean_box(0);
}
if (lean_is_scalar(x_1261)) {
 x_1262 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1262 = x_1261;
}
lean_ctor_set(x_1262, 0, x_1260);
return x_1262;
}
block_1234:
{
if (x_1229 == 0)
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1230 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1230 = lean_box(0);
}
if (lean_is_scalar(x_1230)) {
 x_1231 = lean_alloc_ctor(3, 2, 0);
} else {
 x_1231 = x_1230;
}
lean_ctor_set(x_1231, 0, x_1224);
lean_ctor_set(x_1231, 1, x_1226);
if (lean_is_scalar(x_1227)) {
 x_1232 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1232 = x_1227;
}
lean_ctor_set(x_1232, 0, x_1231);
return x_1232;
}
else
{
lean_object* x_1233; 
lean_dec(x_1226);
lean_dec(x_1224);
if (lean_is_scalar(x_1227)) {
 x_1233 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1233 = x_1227;
}
lean_ctor_set(x_1233, 0, x_1);
return x_1233;
}
}
block_1240:
{
uint8_t x_1236; 
x_1236 = l_Lean_instBEqFVarId_beq(x_1219, x_1224);
if (x_1236 == 0)
{
x_1228 = lean_box(0);
x_1229 = x_1236;
goto block_1234;
}
else
{
size_t x_1237; size_t x_1238; uint8_t x_1239; 
x_1237 = lean_ptr_addr(x_1220);
x_1238 = lean_ptr_addr(x_1226);
x_1239 = lean_usize_dec_eq(x_1237, x_1238);
x_1228 = lean_box(0);
x_1229 = x_1239;
goto block_1234;
}
}
}
else
{
lean_object* x_1263; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1263 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1040, x_8);
lean_dec(x_8);
lean_dec_ref(x_1040);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1263;
}
}
case 4:
{
lean_object* x_1264; lean_object* x_1265; 
lean_dec(x_989);
x_1264 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1264);
lean_inc(x_8);
lean_inc_ref(x_1040);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1264);
x_1265 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1264, x_2, x_3, x_4, x_5, x_6, x_1040, x_8);
if (lean_obj_tag(x_1265) == 0)
{
lean_object* x_1266; lean_object* x_1267; 
x_1266 = lean_ctor_get(x_1265, 0);
lean_inc(x_1266);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 x_1267 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_1267 = lean_box(0);
}
if (lean_obj_tag(x_1266) == 0)
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; 
x_1268 = lean_st_ref_get(x_3);
x_1269 = lean_ctor_get(x_1264, 0);
lean_inc(x_1269);
x_1270 = lean_ctor_get(x_1264, 1);
lean_inc_ref(x_1270);
x_1271 = lean_ctor_get(x_1264, 2);
lean_inc(x_1271);
x_1272 = lean_ctor_get(x_1264, 3);
lean_inc_ref(x_1272);
if (lean_is_exclusive(x_1264)) {
 lean_ctor_release(x_1264, 0);
 lean_ctor_release(x_1264, 1);
 lean_ctor_release(x_1264, 2);
 lean_ctor_release(x_1264, 3);
 x_1273 = x_1264;
} else {
 lean_dec_ref(x_1264);
 x_1273 = lean_box(0);
}
x_1274 = lean_ctor_get(x_1268, 0);
lean_inc_ref(x_1274);
lean_dec_ref(x_1268);
lean_inc(x_1271);
x_1275 = l_Lean_Compiler_LCNF_normFVarImp(x_1274, x_1271, x_52);
lean_dec_ref(x_1274);
if (lean_obj_tag(x_1275) == 0)
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
x_1276 = lean_ctor_get(x_1275, 0);
lean_inc(x_1276);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 x_1277 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1277 = lean_box(0);
}
x_1278 = lean_st_ref_get(x_3);
x_1279 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_1040);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1272);
lean_inc(x_1276);
x_1280 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_1276, x_52, x_1279, x_1272, x_2, x_3, x_4, x_5, x_6, x_1040, x_8);
if (lean_obj_tag(x_1280) == 0)
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
x_1281 = lean_ctor_get(x_1280, 0);
lean_inc(x_1281);
if (lean_is_exclusive(x_1280)) {
 lean_ctor_release(x_1280, 0);
 x_1282 = x_1280;
} else {
 lean_dec_ref(x_1280);
 x_1282 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_1283 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1281, x_2, x_3, x_4, x_5, x_6, x_1040, x_8);
if (lean_obj_tag(x_1283) == 0)
{
lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1293; uint8_t x_1294; lean_object* x_1298; lean_object* x_1299; lean_object* x_1311; uint8_t x_1312; 
x_1284 = lean_ctor_get(x_1283, 0);
lean_inc(x_1284);
if (lean_is_exclusive(x_1283)) {
 lean_ctor_release(x_1283, 0);
 x_1285 = x_1283;
} else {
 lean_dec_ref(x_1283);
 x_1285 = lean_box(0);
}
x_1286 = lean_ctor_get(x_1278, 0);
lean_inc_ref(x_1286);
lean_dec_ref(x_1278);
lean_inc_ref(x_1270);
x_1287 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1286, x_52, x_1270);
lean_dec_ref(x_1286);
x_1311 = lean_array_get_size(x_1284);
x_1312 = lean_nat_dec_eq(x_1311, x_1038);
lean_dec(x_1311);
if (x_1312 == 0)
{
lean_dec(x_1267);
lean_dec(x_6);
x_1298 = x_3;
x_1299 = lean_box(0);
goto block_1310;
}
else
{
lean_object* x_1313; 
x_1313 = lean_array_fget_borrowed(x_1284, x_1279);
if (lean_obj_tag(x_1313) == 0)
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1324; lean_object* x_1325; uint8_t x_1336; lean_object* x_1337; uint8_t x_1339; 
lean_dec(x_1267);
x_1314 = lean_ctor_get(x_1313, 1);
x_1315 = lean_ctor_get(x_1313, 2);
x_1324 = lean_array_get_size(x_1314);
x_1339 = lean_nat_dec_lt(x_1279, x_1324);
if (x_1339 == 0)
{
x_1336 = x_52;
x_1337 = lean_box(0);
goto block_1338;
}
else
{
if (x_1339 == 0)
{
x_1336 = x_52;
x_1337 = lean_box(0);
goto block_1338;
}
else
{
size_t x_1340; size_t x_1341; lean_object* x_1342; 
x_1340 = 0;
x_1341 = lean_usize_of_nat(x_1324);
x_1342 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1314, x_1340, x_1341, x_3);
if (lean_obj_tag(x_1342) == 0)
{
lean_object* x_1343; uint8_t x_1344; 
x_1343 = lean_ctor_get(x_1342, 0);
lean_inc(x_1343);
lean_dec_ref(x_1342);
x_1344 = lean_unbox(x_1343);
lean_dec(x_1343);
x_1336 = x_1344;
x_1337 = lean_box(0);
goto block_1338;
}
else
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; 
lean_dec(x_1324);
lean_dec_ref(x_1287);
lean_dec(x_1285);
lean_dec(x_1284);
lean_dec(x_1282);
lean_dec(x_1277);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec_ref(x_1272);
lean_dec(x_1271);
lean_dec_ref(x_1270);
lean_dec(x_1269);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1345 = lean_ctor_get(x_1342, 0);
lean_inc(x_1345);
if (lean_is_exclusive(x_1342)) {
 lean_ctor_release(x_1342, 0);
 x_1346 = x_1342;
} else {
 lean_dec_ref(x_1342);
 x_1346 = lean_box(0);
}
if (lean_is_scalar(x_1346)) {
 x_1347 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1347 = x_1346;
}
lean_ctor_set(x_1347, 0, x_1345);
return x_1347;
}
}
}
block_1323:
{
lean_object* x_1317; 
x_1317 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1317) == 0)
{
lean_object* x_1318; lean_object* x_1319; 
if (lean_is_exclusive(x_1317)) {
 lean_ctor_release(x_1317, 0);
 x_1318 = x_1317;
} else {
 lean_dec_ref(x_1317);
 x_1318 = lean_box(0);
}
if (lean_is_scalar(x_1318)) {
 x_1319 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1319 = x_1318;
}
lean_ctor_set(x_1319, 0, x_1315);
return x_1319;
}
else
{
lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
lean_dec_ref(x_1315);
x_1320 = lean_ctor_get(x_1317, 0);
lean_inc(x_1320);
if (lean_is_exclusive(x_1317)) {
 lean_ctor_release(x_1317, 0);
 x_1321 = x_1317;
} else {
 lean_dec_ref(x_1317);
 x_1321 = lean_box(0);
}
if (lean_is_scalar(x_1321)) {
 x_1322 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1322 = x_1321;
}
lean_ctor_set(x_1322, 0, x_1320);
return x_1322;
}
}
block_1335:
{
uint8_t x_1326; 
x_1326 = lean_nat_dec_lt(x_1279, x_1324);
if (x_1326 == 0)
{
lean_dec(x_1324);
lean_dec_ref(x_1314);
lean_dec(x_6);
x_1316 = lean_box(0);
goto block_1323;
}
else
{
uint8_t x_1327; 
x_1327 = lean_nat_dec_le(x_1324, x_1324);
if (x_1327 == 0)
{
lean_dec(x_1324);
lean_dec_ref(x_1314);
lean_dec(x_6);
x_1316 = lean_box(0);
goto block_1323;
}
else
{
lean_object* x_1328; size_t x_1329; size_t x_1330; lean_object* x_1331; 
x_1328 = lean_box(0);
x_1329 = 0;
x_1330 = lean_usize_of_nat(x_1324);
lean_dec(x_1324);
x_1331 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1314, x_1329, x_1330, x_1328, x_6);
lean_dec(x_6);
lean_dec_ref(x_1314);
if (lean_obj_tag(x_1331) == 0)
{
lean_dec_ref(x_1331);
x_1316 = lean_box(0);
goto block_1323;
}
else
{
lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; 
lean_dec_ref(x_1315);
lean_dec(x_3);
x_1332 = lean_ctor_get(x_1331, 0);
lean_inc(x_1332);
if (lean_is_exclusive(x_1331)) {
 lean_ctor_release(x_1331, 0);
 x_1333 = x_1331;
} else {
 lean_dec_ref(x_1331);
 x_1333 = lean_box(0);
}
if (lean_is_scalar(x_1333)) {
 x_1334 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1334 = x_1333;
}
lean_ctor_set(x_1334, 0, x_1332);
return x_1334;
}
}
}
}
block_1338:
{
if (x_1336 == 0)
{
lean_inc_ref(x_1315);
lean_inc_ref(x_1314);
lean_dec_ref(x_1287);
lean_dec(x_1285);
lean_dec(x_1284);
lean_dec(x_1282);
lean_dec(x_1277);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec_ref(x_1272);
lean_dec(x_1271);
lean_dec_ref(x_1270);
lean_dec(x_1269);
lean_dec_ref(x_1);
x_1325 = lean_box(0);
goto block_1335;
}
else
{
if (x_52 == 0)
{
lean_dec(x_1324);
lean_dec(x_6);
x_1298 = x_3;
x_1299 = lean_box(0);
goto block_1310;
}
else
{
lean_inc_ref(x_1315);
lean_inc_ref(x_1314);
lean_dec_ref(x_1287);
lean_dec(x_1285);
lean_dec(x_1284);
lean_dec(x_1282);
lean_dec(x_1277);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec_ref(x_1272);
lean_dec(x_1271);
lean_dec_ref(x_1270);
lean_dec(x_1269);
lean_dec_ref(x_1);
x_1325 = lean_box(0);
goto block_1335;
}
}
}
}
else
{
lean_object* x_1348; lean_object* x_1349; 
lean_inc_ref(x_1313);
lean_dec_ref(x_1287);
lean_dec(x_1285);
lean_dec(x_1284);
lean_dec(x_1282);
lean_dec(x_1277);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec_ref(x_1272);
lean_dec(x_1271);
lean_dec_ref(x_1270);
lean_dec(x_1269);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1348 = lean_ctor_get(x_1313, 0);
lean_inc_ref(x_1348);
lean_dec_ref(x_1313);
if (lean_is_scalar(x_1267)) {
 x_1349 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1349 = x_1267;
}
lean_ctor_set(x_1349, 0, x_1348);
return x_1349;
}
}
block_1292:
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; 
if (lean_is_scalar(x_1273)) {
 x_1289 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1289 = x_1273;
}
lean_ctor_set(x_1289, 0, x_1269);
lean_ctor_set(x_1289, 1, x_1287);
lean_ctor_set(x_1289, 2, x_1276);
lean_ctor_set(x_1289, 3, x_1284);
if (lean_is_scalar(x_1277)) {
 x_1290 = lean_alloc_ctor(4, 1, 0);
} else {
 x_1290 = x_1277;
 lean_ctor_set_tag(x_1290, 4);
}
lean_ctor_set(x_1290, 0, x_1289);
if (lean_is_scalar(x_1285)) {
 x_1291 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1291 = x_1285;
}
lean_ctor_set(x_1291, 0, x_1290);
return x_1291;
}
block_1297:
{
if (x_1294 == 0)
{
lean_dec(x_1282);
lean_dec(x_1271);
lean_dec_ref(x_1);
x_1288 = lean_box(0);
goto block_1292;
}
else
{
uint8_t x_1295; 
x_1295 = l_Lean_instBEqFVarId_beq(x_1271, x_1276);
lean_dec(x_1271);
if (x_1295 == 0)
{
lean_dec(x_1282);
lean_dec_ref(x_1);
x_1288 = lean_box(0);
goto block_1292;
}
else
{
lean_object* x_1296; 
lean_dec_ref(x_1287);
lean_dec(x_1285);
lean_dec(x_1284);
lean_dec(x_1277);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec(x_1269);
if (lean_is_scalar(x_1282)) {
 x_1296 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1296 = x_1282;
}
lean_ctor_set(x_1296, 0, x_1);
return x_1296;
}
}
}
block_1310:
{
lean_object* x_1300; 
lean_inc(x_1276);
x_1300 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1276, x_1298);
lean_dec(x_1298);
if (lean_obj_tag(x_1300) == 0)
{
size_t x_1301; size_t x_1302; uint8_t x_1303; 
lean_dec_ref(x_1300);
x_1301 = lean_ptr_addr(x_1272);
lean_dec_ref(x_1272);
x_1302 = lean_ptr_addr(x_1284);
x_1303 = lean_usize_dec_eq(x_1301, x_1302);
if (x_1303 == 0)
{
lean_dec_ref(x_1270);
x_1293 = lean_box(0);
x_1294 = x_1303;
goto block_1297;
}
else
{
size_t x_1304; size_t x_1305; uint8_t x_1306; 
x_1304 = lean_ptr_addr(x_1270);
lean_dec_ref(x_1270);
x_1305 = lean_ptr_addr(x_1287);
x_1306 = lean_usize_dec_eq(x_1304, x_1305);
x_1293 = lean_box(0);
x_1294 = x_1306;
goto block_1297;
}
}
else
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; 
lean_dec_ref(x_1287);
lean_dec(x_1285);
lean_dec(x_1284);
lean_dec(x_1282);
lean_dec(x_1277);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec_ref(x_1272);
lean_dec(x_1271);
lean_dec_ref(x_1270);
lean_dec(x_1269);
lean_dec_ref(x_1);
x_1307 = lean_ctor_get(x_1300, 0);
lean_inc(x_1307);
if (lean_is_exclusive(x_1300)) {
 lean_ctor_release(x_1300, 0);
 x_1308 = x_1300;
} else {
 lean_dec_ref(x_1300);
 x_1308 = lean_box(0);
}
if (lean_is_scalar(x_1308)) {
 x_1309 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1309 = x_1308;
}
lean_ctor_set(x_1309, 0, x_1307);
return x_1309;
}
}
}
else
{
lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
lean_dec(x_1282);
lean_dec_ref(x_1278);
lean_dec(x_1277);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec_ref(x_1272);
lean_dec(x_1271);
lean_dec_ref(x_1270);
lean_dec(x_1269);
lean_dec(x_1267);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1350 = lean_ctor_get(x_1283, 0);
lean_inc(x_1350);
if (lean_is_exclusive(x_1283)) {
 lean_ctor_release(x_1283, 0);
 x_1351 = x_1283;
} else {
 lean_dec_ref(x_1283);
 x_1351 = lean_box(0);
}
if (lean_is_scalar(x_1351)) {
 x_1352 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1352 = x_1351;
}
lean_ctor_set(x_1352, 0, x_1350);
return x_1352;
}
}
else
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
lean_dec_ref(x_1278);
lean_dec(x_1277);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec_ref(x_1272);
lean_dec(x_1271);
lean_dec_ref(x_1270);
lean_dec(x_1269);
lean_dec(x_1267);
lean_dec_ref(x_1040);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1353 = lean_ctor_get(x_1280, 0);
lean_inc(x_1353);
if (lean_is_exclusive(x_1280)) {
 lean_ctor_release(x_1280, 0);
 x_1354 = x_1280;
} else {
 lean_dec_ref(x_1280);
 x_1354 = lean_box(0);
}
if (lean_is_scalar(x_1354)) {
 x_1355 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1355 = x_1354;
}
lean_ctor_set(x_1355, 0, x_1353);
return x_1355;
}
}
else
{
lean_object* x_1356; 
lean_dec(x_1273);
lean_dec_ref(x_1272);
lean_dec(x_1271);
lean_dec_ref(x_1270);
lean_dec(x_1269);
lean_dec(x_1267);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1356 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1040, x_8);
lean_dec(x_8);
lean_dec_ref(x_1040);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1356;
}
}
else
{
lean_object* x_1357; lean_object* x_1358; 
lean_dec_ref(x_1264);
lean_dec_ref(x_1040);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1357 = lean_ctor_get(x_1266, 0);
lean_inc(x_1357);
lean_dec_ref(x_1266);
if (lean_is_scalar(x_1267)) {
 x_1358 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1358 = x_1267;
}
lean_ctor_set(x_1358, 0, x_1357);
return x_1358;
}
}
else
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
lean_dec_ref(x_1264);
lean_dec_ref(x_1040);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1359 = lean_ctor_get(x_1265, 0);
lean_inc(x_1359);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 x_1360 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_1360 = lean_box(0);
}
if (lean_is_scalar(x_1360)) {
 x_1361 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1361 = x_1360;
}
lean_ctor_set(x_1361, 0, x_1359);
return x_1361;
}
}
case 5:
{
lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
lean_dec(x_989);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1362 = lean_ctor_get(x_1, 0);
x_1363 = lean_st_ref_get(x_3);
x_1364 = lean_ctor_get(x_1363, 0);
lean_inc_ref(x_1364);
lean_dec_ref(x_1363);
lean_inc(x_1362);
x_1365 = l_Lean_Compiler_LCNF_normFVarImp(x_1364, x_1362, x_52);
lean_dec_ref(x_1364);
if (lean_obj_tag(x_1365) == 0)
{
lean_object* x_1366; lean_object* x_1367; 
lean_dec_ref(x_1040);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1366 = lean_ctor_get(x_1365, 0);
lean_inc(x_1366);
lean_dec_ref(x_1365);
lean_inc(x_1366);
x_1367 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1366, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1367) == 0)
{
lean_object* x_1368; uint8_t x_1369; 
if (lean_is_exclusive(x_1367)) {
 lean_ctor_release(x_1367, 0);
 x_1368 = x_1367;
} else {
 lean_dec_ref(x_1367);
 x_1368 = lean_box(0);
}
x_1369 = l_Lean_instBEqFVarId_beq(x_1362, x_1366);
if (x_1369 == 0)
{
lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1370 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1370 = lean_box(0);
}
if (lean_is_scalar(x_1370)) {
 x_1371 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1371 = x_1370;
}
lean_ctor_set(x_1371, 0, x_1366);
if (lean_is_scalar(x_1368)) {
 x_1372 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1372 = x_1368;
}
lean_ctor_set(x_1372, 0, x_1371);
return x_1372;
}
else
{
lean_object* x_1373; 
lean_dec(x_1366);
if (lean_is_scalar(x_1368)) {
 x_1373 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1373 = x_1368;
}
lean_ctor_set(x_1373, 0, x_1);
return x_1373;
}
}
else
{
lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; 
lean_dec(x_1366);
lean_dec_ref(x_1);
x_1374 = lean_ctor_get(x_1367, 0);
lean_inc(x_1374);
if (lean_is_exclusive(x_1367)) {
 lean_ctor_release(x_1367, 0);
 x_1375 = x_1367;
} else {
 lean_dec_ref(x_1367);
 x_1375 = lean_box(0);
}
if (lean_is_scalar(x_1375)) {
 x_1376 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1376 = x_1375;
}
lean_ctor_set(x_1376, 0, x_1374);
return x_1376;
}
}
else
{
lean_object* x_1377; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1377 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1040, x_8);
lean_dec(x_8);
lean_dec_ref(x_1040);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1377;
}
}
case 6:
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; size_t x_1382; size_t x_1383; uint8_t x_1384; 
lean_dec_ref(x_1040);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1378 = lean_ctor_get(x_1, 0);
x_1379 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_1380 = lean_ctor_get(x_1379, 0);
lean_inc_ref(x_1380);
lean_dec_ref(x_1379);
lean_inc_ref(x_1378);
x_1381 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1380, x_52, x_1378);
lean_dec_ref(x_1380);
x_1382 = lean_ptr_addr(x_1378);
x_1383 = lean_ptr_addr(x_1381);
x_1384 = lean_usize_dec_eq(x_1382, x_1383);
if (x_1384 == 0)
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1385 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1385 = lean_box(0);
}
if (lean_is_scalar(x_1385)) {
 x_1386 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1386 = x_1385;
}
lean_ctor_set(x_1386, 0, x_1381);
if (lean_is_scalar(x_989)) {
 x_1387 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1387 = x_989;
}
lean_ctor_set(x_1387, 0, x_1386);
return x_1387;
}
else
{
lean_object* x_1388; 
lean_dec_ref(x_1381);
if (lean_is_scalar(x_989)) {
 x_1388 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1388 = x_989;
}
lean_ctor_set(x_1388, 0, x_1);
return x_1388;
}
}
default: 
{
lean_object* x_1389; lean_object* x_1390; 
lean_dec(x_989);
x_1389 = lean_ctor_get(x_1, 0);
x_1390 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1390);
lean_inc_ref(x_1389);
x_990 = x_1389;
x_991 = x_1390;
x_992 = x_2;
x_993 = x_3;
x_994 = x_4;
x_995 = x_5;
x_996 = x_6;
x_997 = x_1040;
x_998 = x_8;
goto block_1037;
}
}
block_1037:
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_999 = lean_ctor_get(x_990, 0);
x_1000 = lean_ctor_get(x_990, 2);
x_1001 = lean_ctor_get(x_990, 3);
x_1002 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_999, x_993);
if (lean_obj_tag(x_1002) == 0)
{
lean_object* x_1003; lean_object* x_1004; uint8_t x_1005; 
x_1003 = lean_ctor_get(x_1002, 0);
lean_inc(x_1003);
lean_dec_ref(x_1002);
lean_inc(x_1003);
lean_inc_ref(x_1);
lean_inc_ref(x_991);
x_1004 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_1004, 0, x_991);
lean_closure_set(x_1004, 1, x_1);
lean_closure_set(x_1004, 2, x_1003);
x_1005 = lean_unbox(x_1003);
if (x_1005 == 0)
{
uint8_t x_1006; 
lean_dec(x_1003);
lean_dec_ref(x_991);
x_1006 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_1006 == 0)
{
x_18 = x_1004;
x_19 = x_990;
x_20 = x_992;
x_21 = x_993;
x_22 = x_994;
x_23 = x_995;
x_24 = x_996;
x_25 = x_997;
x_26 = x_998;
x_27 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_1007; 
lean_inc_ref(x_1001);
x_1007 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_1001, x_1000);
if (x_1007 == 0)
{
x_18 = x_1004;
x_19 = x_990;
x_20 = x_992;
x_21 = x_993;
x_22 = x_994;
x_23 = x_995;
x_24 = x_996;
x_25 = x_997;
x_26 = x_998;
x_27 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
x_1008 = lean_st_ref_get(x_993);
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc_ref(x_1009);
lean_dec_ref(x_1008);
x_1010 = l_Lean_Compiler_LCNF_normFunDeclImp(x_52, x_990, x_1009, x_995, x_996, x_997, x_998);
lean_dec_ref(x_1009);
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1011; lean_object* x_1012; 
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
lean_dec_ref(x_1010);
lean_inc(x_998);
lean_inc_ref(x_997);
lean_inc(x_996);
lean_inc_ref(x_995);
x_1012 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_1011, x_995, x_996, x_997, x_998);
if (lean_obj_tag(x_1012) == 0)
{
lean_object* x_1013; lean_object* x_1014; 
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
lean_dec_ref(x_1012);
x_1014 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_993);
if (lean_obj_tag(x_1014) == 0)
{
lean_dec_ref(x_1014);
x_18 = x_1004;
x_19 = x_1013;
x_20 = x_992;
x_21 = x_993;
x_22 = x_994;
x_23 = x_995;
x_24 = x_996;
x_25 = x_997;
x_26 = x_998;
x_27 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
lean_dec(x_1013);
lean_dec_ref(x_1004);
lean_dec(x_998);
lean_dec_ref(x_997);
lean_dec(x_996);
lean_dec_ref(x_995);
lean_dec_ref(x_994);
lean_dec(x_993);
lean_dec_ref(x_992);
x_1015 = lean_ctor_get(x_1014, 0);
lean_inc(x_1015);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 x_1016 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1016 = lean_box(0);
}
if (lean_is_scalar(x_1016)) {
 x_1017 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1017 = x_1016;
}
lean_ctor_set(x_1017, 0, x_1015);
return x_1017;
}
}
else
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
lean_dec_ref(x_1004);
lean_dec(x_998);
lean_dec_ref(x_997);
lean_dec(x_996);
lean_dec_ref(x_995);
lean_dec_ref(x_994);
lean_dec(x_993);
lean_dec_ref(x_992);
x_1018 = lean_ctor_get(x_1012, 0);
lean_inc(x_1018);
if (lean_is_exclusive(x_1012)) {
 lean_ctor_release(x_1012, 0);
 x_1019 = x_1012;
} else {
 lean_dec_ref(x_1012);
 x_1019 = lean_box(0);
}
if (lean_is_scalar(x_1019)) {
 x_1020 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1020 = x_1019;
}
lean_ctor_set(x_1020, 0, x_1018);
return x_1020;
}
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
lean_dec_ref(x_1004);
lean_dec(x_998);
lean_dec_ref(x_997);
lean_dec(x_996);
lean_dec_ref(x_995);
lean_dec_ref(x_994);
lean_dec(x_993);
lean_dec_ref(x_992);
x_1021 = lean_ctor_get(x_1010, 0);
lean_inc(x_1021);
if (lean_is_exclusive(x_1010)) {
 lean_ctor_release(x_1010, 0);
 x_1022 = x_1010;
} else {
 lean_dec_ref(x_1010);
 x_1022 = lean_box(0);
}
if (lean_is_scalar(x_1022)) {
 x_1023 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1023 = x_1022;
}
lean_ctor_set(x_1023, 0, x_1021);
return x_1023;
}
}
}
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
lean_dec_ref(x_1004);
x_1024 = lean_st_ref_get(x_993);
x_1025 = lean_ctor_get(x_1024, 0);
lean_inc_ref(x_1025);
lean_dec_ref(x_1024);
x_1026 = l_Lean_Compiler_LCNF_normFunDeclImp(x_52, x_990, x_1025, x_995, x_996, x_997, x_998);
lean_dec_ref(x_1025);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; lean_object* x_1028; uint8_t x_1029; lean_object* x_1030; 
x_1027 = lean_ctor_get(x_1026, 0);
lean_inc(x_1027);
lean_dec_ref(x_1026);
x_1028 = lean_box(0);
x_1029 = lean_unbox(x_1003);
lean_dec(x_1003);
x_1030 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_991, x_1, x_1029, x_1027, x_1028, x_992, x_993, x_994, x_995, x_996, x_997, x_998);
return x_1030;
}
else
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
lean_dec(x_1003);
lean_dec(x_998);
lean_dec_ref(x_997);
lean_dec(x_996);
lean_dec_ref(x_995);
lean_dec_ref(x_994);
lean_dec(x_993);
lean_dec_ref(x_992);
lean_dec_ref(x_991);
lean_dec_ref(x_1);
x_1031 = lean_ctor_get(x_1026, 0);
lean_inc(x_1031);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 x_1032 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1032 = lean_box(0);
}
if (lean_is_scalar(x_1032)) {
 x_1033 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1033 = x_1032;
}
lean_ctor_set(x_1033, 0, x_1031);
return x_1033;
}
}
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
lean_dec(x_998);
lean_dec_ref(x_997);
lean_dec(x_996);
lean_dec_ref(x_995);
lean_dec_ref(x_994);
lean_dec(x_993);
lean_dec_ref(x_992);
lean_dec_ref(x_991);
lean_dec_ref(x_990);
lean_dec_ref(x_1);
x_1034 = lean_ctor_get(x_1002, 0);
lean_inc(x_1034);
if (lean_is_exclusive(x_1002)) {
 lean_ctor_release(x_1002, 0);
 x_1035 = x_1002;
} else {
 lean_dec_ref(x_1002);
 x_1035 = lean_box(0);
}
if (lean_is_scalar(x_1035)) {
 x_1036 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1036 = x_1035;
}
lean_ctor_set(x_1036, 0, x_1034);
return x_1036;
}
}
}
else
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
lean_dec_ref(x_51);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1391 = lean_ctor_get(x_988, 0);
lean_inc(x_1391);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 x_1392 = x_988;
} else {
 lean_dec_ref(x_988);
 x_1392 = lean_box(0);
}
if (lean_is_scalar(x_1392)) {
 x_1393 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1393 = x_1392;
}
lean_ctor_set(x_1393, 0, x_1391);
return x_1393;
}
}
}
else
{
lean_object* x_1394; 
lean_dec_ref(x_1);
x_1394 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1394;
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
block_35:
{
lean_object* x_28; 
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
x_28 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_box(0);
x_31 = lean_apply_10(x_18, x_29, x_30, x_20, x_21, x_22, x_23, x_24, x_25, x_26, lean_box(0));
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_24 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_22, x_20, x_23);
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
x_40 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_31, x_20, x_39);
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
x_61 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_51, x_50, x_60);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
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
x_39 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_30, x_37, x_38, x_36, x_3);
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
x_177 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_168, x_175, x_176, x_174, x_3);
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
x_276 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_267, x_274, x_275, x_273, x_3);
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
x_382 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_373, x_380, x_381, x_379, x_3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_1, x_2, x_3, x_5, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_1, x_11, x_2, x_4, x_7);
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
x_15 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_14, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_6, x_2, x_3, x_4);
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
x_12 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_6 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_5, x_2, x_3);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1, x_7, x_8, x_4, x_5);
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
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_6, x_7, x_4);
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
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1, x_7, x_8, x_4, x_5);
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
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_6, x_7, x_4);
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
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_1, x_7, x_8, x_4, x_5);
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
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_7, x_2, x_3, x_4, x_5);
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
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_12 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
