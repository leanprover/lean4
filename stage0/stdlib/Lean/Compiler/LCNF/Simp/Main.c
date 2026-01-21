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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
uint8_t l_Lean_Compiler_LCNF_instBEqLetDecl_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__3;
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_hasLocalInst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getParams(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(uint8_t, lean_object*, size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqLetValue_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getCode(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_object* l_Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
if (x_10 == 0)
{
lean_dec_ref(x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_7, x_12);
lean_dec_ref(x_7);
x_14 = l_Lean_Compiler_LCNF_Alt_getCode(x_13);
lean_dec(x_13);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_1, x_2, x_7);
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
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_1, x_2, x_12);
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
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_2, x_3, x_20);
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
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_dec(x_20);
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
lean_dec(x_29);
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
lean_dec(x_48);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_array_fget_borrowed(x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 2);
lean_inc_ref(x_19);
x_20 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_19, x_16, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = 0;
x_23 = l_Lean_Compiler_LCNF_mkAuxParam(x_21, x_22, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_10, x_26);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_27);
x_28 = lean_array_push(x_15, x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_25);
x_30 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_16, x_18, x_29);
lean_ctor_set(x_2, 1, x_30);
lean_ctor_set(x_2, 0, x_28);
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_18);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_20, 0);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_2);
x_40 = lean_array_fget_borrowed(x_9, x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 2);
lean_inc_ref(x_42);
x_43 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_42, x_39, x_12);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = 0;
x_46 = l_Lean_Compiler_LCNF_mkAuxParam(x_44, x_45, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_10, x_49);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_50);
x_51 = lean_array_push(x_38, x_47);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_48);
x_53 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_39, x_41, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_2 = x_54;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_38);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_57 = x_46;
} else {
 lean_dec_ref(x_46);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_38);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_59 = lean_ctor_get(x_43, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_60 = x_43;
} else {
 lean_dec_ref(x_43);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_1, 0);
x_63 = lean_ctor_get(x_1, 1);
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_1);
x_65 = lean_nat_dec_lt(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_2);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_2, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_69 = x_2;
} else {
 lean_dec_ref(x_2);
 x_69 = lean_box(0);
}
x_70 = lean_array_fget_borrowed(x_62, x_63);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 2);
lean_inc_ref(x_72);
x_73 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_72, x_68, x_65);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = 0;
x_76 = l_Lean_Compiler_LCNF_mkAuxParam(x_74, x_75, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_63, x_79);
lean_dec(x_63);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_62);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_64);
x_82 = lean_array_push(x_67, x_77);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_84 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_68, x_71, x_83);
if (lean_is_scalar(x_69)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_69;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_1 = x_81;
x_2 = x_85;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_88 = x_76;
} else {
 lean_dec_ref(x_76);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_91 = x_73;
} else {
 lean_dec_ref(x_73);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_f", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_15 = lean_array_get_size(x_12);
x_16 = l_Array_toSubarray___redArg(x_12, x_13, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_array_size(x_10);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_10, x_18, x_19, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_49; uint8_t x_50; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_49 = lean_array_get_size(x_10);
x_50 = lean_nat_dec_le(x_15, x_13);
if (x_50 == 0)
{
x_25 = x_15;
x_26 = x_49;
goto block_48;
}
else
{
x_25 = x_13;
x_26 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Array_toSubarray___redArg(x_10, x_25, x_26);
if (lean_is_scalar(x_23)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_23;
}
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_22);
x_29 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(x_27, x_28, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_33 = l_Lean_Compiler_LCNF_Code_internalize(x_11, x_32, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = 0;
lean_inc(x_34);
x_36 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_34, x_35, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_36);
x_37 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_38 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_31, x_34, x_37, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec(x_31);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_29, 0);
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_51 = !lean_is_exclusive(x_20);
if (x_51 == 0)
{
return x_20;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_20, 0);
lean_inc(x_52);
lean_dec(x_20);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_3, x_4, x_5, x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(x_5, x_6, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_16;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(x_2, x_3);
return x_4;
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
lean_dec(x_20);
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
x_56 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
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
x_96 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
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
x_140 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
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
x_193 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
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
x_256 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
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
x_327 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
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
lean_dec(x_371);
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
x_411 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_10;
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
lean_dec(x_7);
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
lean_dec(x_21);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(x_1, x_2, x_4);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1);
lean_dec(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_st_ref_get(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_6, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_8, x_5);
lean_dec(x_8);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_2, x_7);
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
lean_dec(x_12);
lean_inc_ref(x_11);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_13, x_1, x_11);
lean_dec_ref(x_13);
lean_inc(x_10);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18___redArg(x_7, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18___redArg(x_1, x_11, x_2, x_4, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_8, x_5);
lean_dec(x_8);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_17; uint8_t x_20; 
x_20 = lean_usize_dec_eq(x_3, x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_array_uget(x_2, x_3);
x_22 = l_Lean_Compiler_LCNF_Alt_getParams(x_21);
lean_dec(x_21);
x_23 = lean_array_get_size(x_22);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_1, x_23);
if (x_25 == 0)
{
lean_dec_ref(x_22);
x_11 = x_24;
x_12 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_23, x_23);
if (x_26 == 0)
{
if (x_25 == 0)
{
lean_dec_ref(x_22);
x_11 = x_24;
x_12 = lean_box(0);
goto block_16;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_23);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_22, x_27, x_28, x_24, x_7);
lean_dec_ref(x_22);
x_17 = x_29;
goto block_19;
}
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_23);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_22, x_30, x_31, x_24, x_7);
lean_dec_ref(x_22);
x_17 = x_32;
goto block_19;
}
}
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_5);
return x_33;
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
goto _start;
}
block_19:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_11 = x_18;
x_12 = lean_box(0);
goto block_16;
}
else
{
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18___redArg(x_1, x_4, x_2, x_3);
return x_5;
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
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7___redArg(x_1, x_4, x_5);
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
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(x_3, x_48, x_49, x_50, x_51);
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
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7___redArg(x_61, x_4, x_5);
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
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(x_3, x_64, x_65, x_66, x_67);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_19);
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
lean_dec(x_49);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 1;
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_Compiler_LCNF_Alt_getCode(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 6)
{
lean_dec_ref(x_8);
if (x_1 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_6;
}
}
else
{
lean_dec_ref(x_8);
return x_6;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_6, x_2, x_1);
lean_dec_ref(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_5, x_2, x_3);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_1, x_6, x_7, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_1, x_6, x_7, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
return x_1;
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Simp_simp___closed__2;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(364u);
x_4 = l_Lean_Compiler_LCNF_Simp_simp___closed__1;
x_5 = l_Lean_Compiler_LCNF_Simp_simp___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
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
x_18 = l_Subarray_toArray___redArg(x_17);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
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
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_12, 0);
lean_inc(x_190);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_190);
x_191 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(x_22, x_190, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
x_193 = !lean_is_exclusive(x_3);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_3, 2);
x_195 = lean_ctor_get(x_3, 3);
lean_inc(x_190);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_190);
lean_ctor_set(x_196, 1, x_194);
x_197 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_195, x_190, x_192);
lean_ctor_set(x_3, 3, x_197);
lean_ctor_set(x_3, 2, x_196);
x_131 = x_3;
x_132 = x_4;
x_133 = x_5;
x_134 = x_6;
x_135 = x_7;
x_136 = x_8;
x_137 = x_9;
x_138 = lean_box(0);
goto block_189;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_198 = lean_ctor_get(x_3, 0);
x_199 = lean_ctor_get(x_3, 1);
x_200 = lean_ctor_get(x_3, 2);
x_201 = lean_ctor_get(x_3, 3);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_3);
lean_inc(x_190);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_190);
lean_ctor_set(x_202, 1, x_200);
x_203 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_201, x_190, x_192);
x_204 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_204, 0, x_198);
lean_ctor_set(x_204, 1, x_199);
lean_ctor_set(x_204, 2, x_202);
lean_ctor_set(x_204, 3, x_203);
x_131 = x_204;
x_132 = x_4;
x_133 = x_5;
x_134 = x_6;
x_135 = x_7;
x_136 = x_8;
x_137 = x_9;
x_138 = lean_box(0);
goto block_189;
}
}
else
{
uint8_t x_205; 
lean_dec(x_190);
lean_dec_ref(x_25);
lean_dec(x_24);
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
x_205 = !lean_is_exclusive(x_191);
if (x_205 == 0)
{
return x_191;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_191, 0);
lean_inc(x_206);
lean_dec(x_191);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
}
}
else
{
lean_dec(x_12);
x_131 = x_3;
x_132 = x_4;
x_133 = x_5;
x_134 = x_6;
x_135 = x_7;
x_136 = x_8;
x_137 = x_9;
x_138 = lean_box(0);
goto block_189;
}
block_130:
{
lean_object* x_39; 
lean_inc(x_32);
lean_inc_ref(x_37);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc_ref(x_27);
lean_inc(x_38);
lean_inc_ref(x_30);
x_39 = l_Lean_Compiler_LCNF_Simp_simp(x_31, x_30, x_38, x_27, x_28, x_29, x_37, x_32);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_38);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec_ref(x_41);
lean_inc(x_40);
x_42 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec_ref(x_34);
x_43 = l_Lean_Compiler_LCNF_inferAppType(x_20, x_33, x_28, x_29, x_37, x_32);
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
lean_dec(x_35);
x_47 = l_Lean_Compiler_LCNF_mkAuxParam(x_44, x_26, x_28, x_29, x_37, x_32);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_32);
lean_inc_ref(x_37);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_49);
x_50 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_24, x_23, x_11, x_2, x_21, x_49, x_30, x_38, x_27, x_28, x_29, x_37, x_32);
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
x_56 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_54, x_51, x_55, x_28, x_29, x_37, x_32);
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
x_59 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_58, x_28, x_29, x_37, x_32);
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
if (lean_is_scalar(x_17)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_17;
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
if (lean_is_scalar(x_17)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_17;
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
lean_dec(x_17);
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
lean_dec_ref(x_37);
lean_dec(x_32);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_17);
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
lean_dec_ref(x_37);
lean_dec(x_32);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_17);
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
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_17);
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
x_80 = lean_mk_empty_array_with_capacity(x_35);
lean_dec(x_35);
x_81 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_82 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_80, x_40, x_81, x_28, x_29, x_37, x_32);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc(x_32);
lean_inc_ref(x_37);
lean_inc(x_29);
lean_inc_ref(x_28);
x_84 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_83, x_28, x_29, x_37, x_32);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_32);
lean_inc_ref(x_37);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc_ref(x_27);
lean_inc(x_38);
lean_inc_ref(x_30);
lean_inc(x_86);
x_87 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_24, x_23, x_11, x_2, x_21, x_86, x_30, x_38, x_27, x_28, x_29, x_37, x_32);
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
x_92 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_91, x_88, x_30, x_38, x_27, x_28, x_29, x_37, x_32);
lean_dec(x_32);
lean_dec_ref(x_37);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_38);
lean_dec_ref(x_30);
lean_dec_ref(x_91);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
if (lean_is_scalar(x_17)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_17;
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
if (lean_is_scalar(x_17)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_17;
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
lean_dec(x_17);
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
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_17);
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
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_17);
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
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_17);
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
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_35);
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_17);
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
lean_dec(x_38);
lean_dec(x_35);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_11);
lean_dec_ref(x_2);
x_114 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_34, x_28, x_29, x_37, x_32);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
if (lean_is_scalar(x_17)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_17;
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
if (lean_is_scalar(x_17)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_17;
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
lean_dec(x_17);
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
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_17);
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
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_17);
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
block_189:
{
if (x_26 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_inc_ref(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_19);
lean_inc_ref(x_18);
lean_dec(x_16);
x_139 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
lean_inc_ref(x_21);
x_140 = l_Array_toSubarray___redArg(x_21, x_139, x_24);
x_141 = l_Subarray_toArray___redArg(x_140);
lean_inc(x_137);
lean_inc_ref(x_136);
lean_inc(x_135);
lean_inc_ref(x_134);
lean_inc_ref(x_141);
x_142 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_18, x_19, x_141, x_26, x_131, x_132, x_133, x_134, x_135, x_136, x_137);
lean_dec_ref(x_18);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
lean_inc_ref(x_133);
lean_inc_ref(x_131);
lean_inc(x_132);
x_144 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(x_144, 0, x_132);
lean_closure_set(x_144, 1, x_25);
lean_closure_set(x_144, 2, x_131);
lean_closure_set(x_144, 3, x_133);
x_145 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_11);
if (x_145 == 0)
{
x_27 = x_133;
x_28 = x_134;
x_29 = x_135;
x_30 = x_131;
x_31 = x_143;
x_32 = x_137;
x_33 = x_141;
x_34 = x_144;
x_35 = x_139;
x_36 = lean_box(0);
x_37 = x_136;
x_38 = x_132;
goto block_130;
}
else
{
uint8_t x_146; 
x_146 = lean_nat_dec_eq(x_23, x_24);
if (x_146 == 0)
{
x_27 = x_133;
x_28 = x_134;
x_29 = x_135;
x_30 = x_131;
x_31 = x_143;
x_32 = x_137;
x_33 = x_141;
x_34 = x_144;
x_35 = x_139;
x_36 = lean_box(0);
x_37 = x_136;
x_38 = x_132;
goto block_130;
}
else
{
lean_object* x_147; 
lean_dec_ref(x_144);
lean_dec_ref(x_141);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_2);
x_147 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_132);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
lean_dec_ref(x_147);
x_148 = l_Lean_Compiler_LCNF_Simp_simp(x_143, x_131, x_132, x_133, x_134, x_135, x_136, x_137);
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
lean_dec(x_143);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
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
lean_dec_ref(x_141);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_2);
x_161 = !lean_is_exclusive(x_142);
if (x_161 == 0)
{
return x_142;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_142, 0);
lean_inc(x_162);
lean_dec(x_142);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; 
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_inc(x_137);
lean_inc_ref(x_136);
lean_inc(x_135);
lean_inc_ref(x_134);
x_164 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_16, x_131, x_132, x_133, x_134, x_135, x_136, x_137);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec_ref(x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_166, x_132, x_135, x_136, x_137);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
lean_dec_ref(x_167);
x_168 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_132);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec_ref(x_168);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_2);
x_170 = l_Lean_Compiler_LCNF_Simp_simp(x_169, x_131, x_132, x_133, x_134, x_135, x_136, x_137);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_170, 0);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_170, 0, x_173);
return x_170;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_170, 0);
lean_inc(x_174);
lean_dec(x_170);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_175);
return x_176;
}
}
else
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_170);
if (x_177 == 0)
{
return x_170;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_170, 0);
lean_inc(x_178);
lean_dec(x_170);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_165);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_2);
x_180 = !lean_is_exclusive(x_168);
if (x_180 == 0)
{
return x_168;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_168, 0);
lean_inc(x_181);
lean_dec(x_168);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_165);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_2);
x_183 = !lean_is_exclusive(x_167);
if (x_183 == 0)
{
return x_167;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_167, 0);
lean_inc(x_184);
lean_dec(x_167);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_11);
lean_dec_ref(x_2);
x_186 = !lean_is_exclusive(x_164);
if (x_186 == 0)
{
return x_164;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_164, 0);
lean_inc(x_187);
lean_dec(x_164);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
}
}
}
}
else
{
lean_object* x_208; 
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
x_208 = lean_box(0);
lean_ctor_set(x_13, 0, x_208);
return x_13;
}
}
else
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_13, 0);
lean_inc(x_209);
lean_dec(x_13);
if (lean_obj_tag(x_209) == 1)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_ctor_get(x_210, 1);
x_214 = lean_ctor_get(x_210, 2);
x_215 = lean_ctor_get(x_210, 3);
x_216 = lean_ctor_get_uint8(x_210, sizeof(void*)*4 + 2);
x_217 = lean_array_get_size(x_215);
x_218 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_210);
lean_inc_ref(x_215);
lean_inc_ref(x_2);
lean_inc(x_11);
lean_inc(x_218);
x_219 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 14, 5);
lean_closure_set(x_219, 0, x_218);
lean_closure_set(x_219, 1, x_217);
lean_closure_set(x_219, 2, x_11);
lean_closure_set(x_219, 3, x_2);
lean_closure_set(x_219, 4, x_215);
x_220 = lean_nat_dec_lt(x_217, x_218);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_12, 0);
lean_inc(x_373);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_373);
x_374 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(x_216, x_373, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
lean_dec_ref(x_374);
x_376 = lean_ctor_get(x_3, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_377);
x_378 = lean_ctor_get(x_3, 2);
lean_inc(x_378);
x_379 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_379);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_380 = x_3;
} else {
 lean_dec_ref(x_3);
 x_380 = lean_box(0);
}
lean_inc(x_373);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_373);
lean_ctor_set(x_381, 1, x_378);
x_382 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_379, x_373, x_375);
if (lean_is_scalar(x_380)) {
 x_383 = lean_alloc_ctor(0, 4, 0);
} else {
 x_383 = x_380;
}
lean_ctor_set(x_383, 0, x_376);
lean_ctor_set(x_383, 1, x_377);
lean_ctor_set(x_383, 2, x_381);
lean_ctor_set(x_383, 3, x_382);
x_318 = x_383;
x_319 = x_4;
x_320 = x_5;
x_321 = x_6;
x_322 = x_7;
x_323 = x_8;
x_324 = x_9;
x_325 = lean_box(0);
goto block_372;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_373);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_384 = lean_ctor_get(x_374, 0);
lean_inc(x_384);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_385 = x_374;
} else {
 lean_dec_ref(x_374);
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
lean_dec(x_12);
x_318 = x_3;
x_319 = x_4;
x_320 = x_5;
x_321 = x_6;
x_322 = x_7;
x_323 = x_8;
x_324 = x_9;
x_325 = lean_box(0);
goto block_372;
}
block_317:
{
lean_object* x_233; 
lean_inc(x_226);
lean_inc_ref(x_231);
lean_inc(x_223);
lean_inc_ref(x_222);
lean_inc_ref(x_221);
lean_inc(x_232);
lean_inc_ref(x_224);
x_233 = l_Lean_Compiler_LCNF_Simp_simp(x_225, x_224, x_232, x_221, x_222, x_223, x_231, x_226);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
lean_dec_ref(x_233);
x_235 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_232);
if (lean_obj_tag(x_235) == 0)
{
uint8_t x_236; 
lean_dec_ref(x_235);
lean_inc(x_234);
x_236 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_234);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec_ref(x_228);
x_237 = l_Lean_Compiler_LCNF_inferAppType(x_214, x_227, x_222, x_223, x_231, x_226);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
lean_inc(x_238);
x_239 = l_Lean_Expr_headBeta(x_238);
x_240 = l_Lean_Expr_isForall(x_239);
lean_dec_ref(x_239);
if (x_240 == 0)
{
lean_object* x_241; 
lean_dec(x_229);
x_241 = l_Lean_Compiler_LCNF_mkAuxParam(x_238, x_220, x_222, x_223, x_231, x_226);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
lean_dec_ref(x_241);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_226);
lean_inc_ref(x_231);
lean_inc(x_223);
lean_inc_ref(x_222);
lean_inc(x_243);
x_244 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_218, x_217, x_11, x_2, x_215, x_243, x_224, x_232, x_221, x_222, x_223, x_231, x_226);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec_ref(x_244);
x_246 = lean_unsigned_to_nat(1u);
x_247 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_248 = lean_array_push(x_247, x_242);
x_249 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_250 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_248, x_245, x_249, x_222, x_223, x_231, x_226);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
lean_inc(x_251);
x_252 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_252, 0, x_251);
lean_closure_set(x_252, 1, x_246);
x_253 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_234, x_252, x_222, x_223, x_231, x_226);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
x_256 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_256, 0, x_251);
lean_ctor_set(x_256, 1, x_254);
if (lean_is_scalar(x_211)) {
 x_257 = lean_alloc_ctor(1, 1, 0);
} else {
 x_257 = x_211;
}
lean_ctor_set(x_257, 0, x_256);
if (lean_is_scalar(x_255)) {
 x_258 = lean_alloc_ctor(0, 1, 0);
} else {
 x_258 = x_255;
}
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_251);
lean_dec(x_211);
x_259 = lean_ctor_get(x_253, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_260 = x_253;
} else {
 lean_dec_ref(x_253);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 1, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_259);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_234);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_211);
x_262 = lean_ctor_get(x_250, 0);
lean_inc(x_262);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_263 = x_250;
} else {
 lean_dec_ref(x_250);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 1, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_262);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_242);
lean_dec(x_234);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_211);
x_265 = lean_ctor_get(x_244, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_266 = x_244;
} else {
 lean_dec_ref(x_244);
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
lean_dec(x_234);
lean_dec(x_232);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_218);
lean_dec_ref(x_215);
lean_dec(x_211);
lean_dec(x_11);
lean_dec_ref(x_2);
x_268 = lean_ctor_get(x_241, 0);
lean_inc(x_268);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 x_269 = x_241;
} else {
 lean_dec_ref(x_241);
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
lean_dec(x_238);
x_271 = lean_mk_empty_array_with_capacity(x_229);
lean_dec(x_229);
x_272 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_273 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_271, x_234, x_272, x_222, x_223, x_231, x_226);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
lean_dec_ref(x_273);
lean_inc(x_226);
lean_inc_ref(x_231);
lean_inc(x_223);
lean_inc_ref(x_222);
x_275 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_274, x_222, x_223, x_231, x_226);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec_ref(x_275);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_226);
lean_inc_ref(x_231);
lean_inc(x_223);
lean_inc_ref(x_222);
lean_inc_ref(x_221);
lean_inc(x_232);
lean_inc_ref(x_224);
lean_inc(x_277);
x_278 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_218, x_217, x_11, x_2, x_215, x_277, x_224, x_232, x_221, x_222, x_223, x_231, x_226);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec_ref(x_278);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_276);
x_281 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_282 = lean_array_push(x_281, x_280);
x_283 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_282, x_279, x_224, x_232, x_221, x_222, x_223, x_231, x_226);
lean_dec(x_226);
lean_dec_ref(x_231);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_232);
lean_dec_ref(x_224);
lean_dec_ref(x_282);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_285 = x_283;
} else {
 lean_dec_ref(x_283);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_286 = lean_alloc_ctor(1, 1, 0);
} else {
 x_286 = x_211;
}
lean_ctor_set(x_286, 0, x_284);
if (lean_is_scalar(x_285)) {
 x_287 = lean_alloc_ctor(0, 1, 0);
} else {
 x_287 = x_285;
}
lean_ctor_set(x_287, 0, x_286);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_211);
x_288 = lean_ctor_get(x_283, 0);
lean_inc(x_288);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_289 = x_283;
} else {
 lean_dec_ref(x_283);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 1, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_288);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_276);
lean_dec(x_232);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_211);
x_291 = lean_ctor_get(x_278, 0);
lean_inc(x_291);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 x_292 = x_278;
} else {
 lean_dec_ref(x_278);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 1, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_291);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_232);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_218);
lean_dec_ref(x_215);
lean_dec(x_211);
lean_dec(x_11);
lean_dec_ref(x_2);
x_294 = lean_ctor_get(x_275, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_295 = x_275;
} else {
 lean_dec_ref(x_275);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 1, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_294);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_232);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_218);
lean_dec_ref(x_215);
lean_dec(x_211);
lean_dec(x_11);
lean_dec_ref(x_2);
x_297 = lean_ctor_get(x_273, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_298 = x_273;
} else {
 lean_dec_ref(x_273);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_297);
return x_299;
}
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_234);
lean_dec(x_232);
lean_dec_ref(x_231);
lean_dec(x_229);
lean_dec(x_226);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_218);
lean_dec_ref(x_215);
lean_dec(x_211);
lean_dec(x_11);
lean_dec_ref(x_2);
x_300 = lean_ctor_get(x_237, 0);
lean_inc(x_300);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_301 = x_237;
} else {
 lean_dec_ref(x_237);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 1, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_300);
return x_302;
}
}
else
{
lean_object* x_303; 
lean_dec(x_232);
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec_ref(x_224);
lean_dec_ref(x_221);
lean_dec(x_218);
lean_dec_ref(x_215);
lean_dec_ref(x_214);
lean_dec(x_11);
lean_dec_ref(x_2);
x_303 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_234, x_228, x_222, x_223, x_231, x_226);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 x_305 = x_303;
} else {
 lean_dec_ref(x_303);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_306 = lean_alloc_ctor(1, 1, 0);
} else {
 x_306 = x_211;
}
lean_ctor_set(x_306, 0, x_304);
if (lean_is_scalar(x_305)) {
 x_307 = lean_alloc_ctor(0, 1, 0);
} else {
 x_307 = x_305;
}
lean_ctor_set(x_307, 0, x_306);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_211);
x_308 = lean_ctor_get(x_303, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 x_309 = x_303;
} else {
 lean_dec_ref(x_303);
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
lean_dec(x_234);
lean_dec(x_232);
lean_dec_ref(x_231);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_218);
lean_dec_ref(x_215);
lean_dec_ref(x_214);
lean_dec(x_211);
lean_dec(x_11);
lean_dec_ref(x_2);
x_311 = lean_ctor_get(x_235, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_312 = x_235;
} else {
 lean_dec_ref(x_235);
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
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_232);
lean_dec_ref(x_231);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_218);
lean_dec_ref(x_215);
lean_dec_ref(x_214);
lean_dec(x_211);
lean_dec(x_11);
lean_dec_ref(x_2);
x_314 = lean_ctor_get(x_233, 0);
lean_inc(x_314);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 x_315 = x_233;
} else {
 lean_dec_ref(x_233);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 1, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_314);
return x_316;
}
}
block_372:
{
if (x_220 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_inc_ref(x_215);
lean_inc_ref(x_214);
lean_inc_ref(x_213);
lean_inc_ref(x_212);
lean_dec(x_210);
x_326 = lean_unsigned_to_nat(0u);
lean_inc(x_218);
lean_inc_ref(x_215);
x_327 = l_Array_toSubarray___redArg(x_215, x_326, x_218);
x_328 = l_Subarray_toArray___redArg(x_327);
lean_inc(x_324);
lean_inc_ref(x_323);
lean_inc(x_322);
lean_inc_ref(x_321);
lean_inc_ref(x_328);
x_329 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_212, x_213, x_328, x_220, x_318, x_319, x_320, x_321, x_322, x_323, x_324);
lean_dec_ref(x_212);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; uint8_t x_332; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
lean_dec_ref(x_329);
lean_inc_ref(x_320);
lean_inc_ref(x_318);
lean_inc(x_319);
x_331 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(x_331, 0, x_319);
lean_closure_set(x_331, 1, x_219);
lean_closure_set(x_331, 2, x_318);
lean_closure_set(x_331, 3, x_320);
x_332 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_11);
if (x_332 == 0)
{
x_221 = x_320;
x_222 = x_321;
x_223 = x_322;
x_224 = x_318;
x_225 = x_330;
x_226 = x_324;
x_227 = x_328;
x_228 = x_331;
x_229 = x_326;
x_230 = lean_box(0);
x_231 = x_323;
x_232 = x_319;
goto block_317;
}
else
{
uint8_t x_333; 
x_333 = lean_nat_dec_eq(x_217, x_218);
if (x_333 == 0)
{
x_221 = x_320;
x_222 = x_321;
x_223 = x_322;
x_224 = x_318;
x_225 = x_330;
x_226 = x_324;
x_227 = x_328;
x_228 = x_331;
x_229 = x_326;
x_230 = lean_box(0);
x_231 = x_323;
x_232 = x_319;
goto block_317;
}
else
{
lean_object* x_334; 
lean_dec_ref(x_331);
lean_dec_ref(x_328);
lean_dec(x_218);
lean_dec_ref(x_215);
lean_dec_ref(x_214);
lean_dec(x_211);
lean_dec(x_11);
lean_dec_ref(x_2);
x_334 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_319);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; 
lean_dec_ref(x_334);
x_335 = l_Lean_Compiler_LCNF_Simp_simp(x_330, x_318, x_319, x_320, x_321, x_322, x_323, x_324);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_337 = x_335;
} else {
 lean_dec_ref(x_335);
 x_337 = lean_box(0);
}
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_336);
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
x_340 = lean_ctor_get(x_335, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_341 = x_335;
} else {
 lean_dec_ref(x_335);
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
lean_dec(x_330);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_318);
x_343 = lean_ctor_get(x_334, 0);
lean_inc(x_343);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 x_344 = x_334;
} else {
 lean_dec_ref(x_334);
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
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec_ref(x_328);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec_ref(x_215);
lean_dec_ref(x_214);
lean_dec(x_211);
lean_dec(x_11);
lean_dec_ref(x_2);
x_346 = lean_ctor_get(x_329, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 x_347 = x_329;
} else {
 lean_dec_ref(x_329);
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
lean_object* x_349; 
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec(x_211);
lean_inc(x_324);
lean_inc_ref(x_323);
lean_inc(x_322);
lean_inc_ref(x_321);
x_349 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_210, x_318, x_319, x_320, x_321, x_322, x_323, x_324);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
lean_dec_ref(x_349);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_351, x_319, x_322, x_323, x_324);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; 
lean_dec_ref(x_352);
x_353 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_319);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; 
lean_dec_ref(x_353);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_2);
x_355 = l_Lean_Compiler_LCNF_Simp_simp(x_354, x_318, x_319, x_320, x_321, x_322, x_323, x_324);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 x_357 = x_355;
} else {
 lean_dec_ref(x_355);
 x_357 = lean_box(0);
}
x_358 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_358, 0, x_356);
if (lean_is_scalar(x_357)) {
 x_359 = lean_alloc_ctor(0, 1, 0);
} else {
 x_359 = x_357;
}
lean_ctor_set(x_359, 0, x_358);
return x_359;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_355, 0);
lean_inc(x_360);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 x_361 = x_355;
} else {
 lean_dec_ref(x_355);
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
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_350);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_2);
x_363 = lean_ctor_get(x_353, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 x_364 = x_353;
} else {
 lean_dec_ref(x_353);
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
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_350);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_2);
x_366 = lean_ctor_get(x_352, 0);
lean_inc(x_366);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 x_367 = x_352;
} else {
 lean_dec_ref(x_352);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 1, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_366);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_318);
lean_dec(x_11);
lean_dec_ref(x_2);
x_369 = lean_ctor_get(x_349, 0);
lean_inc(x_369);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 x_370 = x_349;
} else {
 lean_dec_ref(x_349);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 1, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_369);
return x_371;
}
}
}
}
else
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_209);
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
x_387 = lean_box(0);
x_388 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_388, 0, x_387);
return x_388;
}
}
}
else
{
uint8_t x_389; 
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
x_389 = !lean_is_exclusive(x_13);
if (x_389 == 0)
{
return x_13;
}
else
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_13, 0);
lean_inc(x_390);
lean_dec(x_13);
x_391 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_391, 0, x_390);
return x_391;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_st_ref_get(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = 0;
lean_inc(x_10);
x_14 = l_Lean_Compiler_LCNF_normFVarImp(x_12, x_10, x_13);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
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
x_57 = lean_ctor_get(x_31, 3);
lean_inc(x_57);
lean_dec_ref(x_31);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_32);
x_60 = lean_nat_dec_le(x_57, x_58);
if (x_60 == 0)
{
x_33 = x_57;
x_34 = x_59;
goto block_56;
}
else
{
lean_dec(x_57);
x_33 = x_58;
x_34 = x_59;
goto block_56;
}
block_56:
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = l_Array_toSubarray___redArg(x_32, x_33, x_34);
x_36 = lean_array_size(x_29);
x_37 = 0;
x_38 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_29, x_36, x_37, x_35, x_3);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
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
else
{
uint8_t x_53; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_38);
if (x_53 == 0)
{
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_38, 0);
lean_inc(x_54);
lean_dec(x_38);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_62);
lean_dec_ref(x_25);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_64, x_65);
if (x_66 == 1)
{
lean_object* x_67; 
lean_free_object(x_20);
lean_dec(x_64);
lean_dec_ref(x_61);
lean_free_object(x_23);
x_67 = l_Lean_Compiler_LCNF_Simp_simp(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
if (lean_is_scalar(x_21)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_21;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_67, 0, x_70);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
lean_dec(x_67);
if (lean_is_scalar(x_21)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_21;
}
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_21);
x_74 = !lean_is_exclusive(x_67);
if (x_74 == 0)
{
return x_67;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
lean_dec(x_67);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_sub(x_64, x_77);
lean_dec(x_64);
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_78);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_20);
x_80 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_81 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_79, x_80, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = l_Lean_Compiler_LCNF_instInhabitedParam_default;
x_84 = lean_array_get_borrowed(x_83, x_61, x_65);
x_85 = lean_ctor_get(x_84, 0);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_inc(x_85);
x_87 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_85, x_86, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
lean_dec_ref(x_87);
lean_inc(x_6);
x_88 = l_Lean_Compiler_LCNF_Simp_simp(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_61, x_6);
lean_dec(x_6);
lean_dec_ref(x_61);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
lean_ctor_set(x_23, 1, x_89);
lean_ctor_set(x_23, 0, x_82);
if (lean_is_scalar(x_21)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_21;
}
lean_ctor_set(x_93, 0, x_23);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_90);
lean_ctor_set(x_23, 1, x_89);
lean_ctor_set(x_23, 0, x_82);
if (lean_is_scalar(x_21)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_21;
}
lean_ctor_set(x_94, 0, x_23);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_dec(x_89);
lean_dec(x_82);
lean_free_object(x_23);
lean_dec(x_21);
x_96 = !lean_is_exclusive(x_90);
if (x_96 == 0)
{
return x_90;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_90, 0);
lean_inc(x_97);
lean_dec(x_90);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_82);
lean_dec_ref(x_61);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_6);
x_99 = !lean_is_exclusive(x_88);
if (x_99 == 0)
{
return x_88;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_88, 0);
lean_inc(x_100);
lean_dec(x_88);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_82);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_105 = !lean_is_exclusive(x_81);
if (x_105 == 0)
{
return x_81;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_81, 0);
lean_inc(x_106);
lean_dec(x_81);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_20, 0);
lean_inc(x_108);
lean_dec(x_20);
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_dec_eq(x_108, x_109);
if (x_110 == 1)
{
lean_object* x_111; 
lean_dec(x_108);
lean_dec_ref(x_61);
lean_free_object(x_23);
x_111 = l_Lean_Compiler_LCNF_Simp_simp(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_21;
}
lean_ctor_set(x_114, 0, x_112);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 1, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_21);
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_sub(x_108, x_119);
lean_dec(x_108);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_124 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_122, x_123, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = l_Lean_Compiler_LCNF_instInhabitedParam_default;
x_127 = lean_array_get_borrowed(x_126, x_61, x_109);
x_128 = lean_ctor_get(x_127, 0);
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
lean_inc(x_128);
x_130 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_128, x_129, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
lean_dec_ref(x_130);
lean_inc(x_6);
x_131 = l_Lean_Compiler_LCNF_Simp_simp(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_61, x_6);
lean_dec(x_6);
lean_dec_ref(x_61);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_134 = x_133;
} else {
 lean_dec_ref(x_133);
 x_134 = lean_box(0);
}
lean_ctor_set(x_23, 1, x_132);
lean_ctor_set(x_23, 0, x_125);
if (lean_is_scalar(x_21)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_21;
}
lean_ctor_set(x_135, 0, x_23);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 1, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_132);
lean_dec(x_125);
lean_free_object(x_23);
lean_dec(x_21);
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_138 = x_133;
} else {
 lean_dec_ref(x_133);
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
lean_dec(x_125);
lean_dec_ref(x_61);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_6);
x_140 = lean_ctor_get(x_131, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_141 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_dec(x_125);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_143 = lean_ctor_get(x_130, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_144 = x_130;
} else {
 lean_dec_ref(x_130);
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
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_146 = lean_ctor_get(x_124, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_147 = x_124;
} else {
 lean_dec_ref(x_124);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
return x_148;
}
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_free_object(x_23);
lean_dec(x_20);
x_149 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_149);
lean_dec_ref(x_25);
x_150 = l_Lean_Compiler_LCNF_Simp_simp(x_149, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_150) == 0)
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_150, 0);
if (lean_is_scalar(x_21)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_21;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_150, 0, x_153);
return x_150;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_150, 0);
lean_inc(x_154);
lean_dec(x_150);
if (lean_is_scalar(x_21)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_21;
}
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
else
{
uint8_t x_157; 
lean_dec(x_21);
x_157 = !lean_is_exclusive(x_150);
if (x_157 == 0)
{
return x_150;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_150, 0);
lean_inc(x_158);
lean_dec(x_150);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
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
x_160 = !lean_is_exclusive(x_28);
if (x_160 == 0)
{
return x_28;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_28, 0);
lean_inc(x_161);
lean_dec(x_28);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
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
x_163 = !lean_is_exclusive(x_27);
if (x_163 == 0)
{
return x_27;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_27, 0);
lean_inc(x_164);
lean_dec(x_27);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_23, 0);
x_167 = lean_ctor_get(x_23, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_23);
lean_ctor_set_tag(x_14, 4);
lean_ctor_set(x_14, 0, x_167);
x_168 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_14, x_6);
lean_dec_ref(x_14);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
lean_dec_ref(x_168);
x_169 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_169) == 0)
{
lean_dec_ref(x_169);
if (lean_obj_tag(x_166) == 0)
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_170 = lean_ctor_get(x_166, 1);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_166, 2);
lean_inc_ref(x_171);
lean_dec_ref(x_166);
x_172 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_173);
lean_dec_ref(x_20);
x_196 = lean_ctor_get(x_172, 3);
lean_inc(x_196);
lean_dec_ref(x_172);
x_197 = lean_unsigned_to_nat(0u);
x_198 = lean_array_get_size(x_173);
x_199 = lean_nat_dec_le(x_196, x_197);
if (x_199 == 0)
{
x_174 = x_196;
x_175 = x_198;
goto block_195;
}
else
{
lean_dec(x_196);
x_174 = x_197;
x_175 = x_198;
goto block_195;
}
block_195:
{
lean_object* x_176; size_t x_177; size_t x_178; lean_object* x_179; 
x_176 = l_Array_toSubarray___redArg(x_173, x_174, x_175);
x_177 = lean_array_size(x_170);
x_178 = 0;
x_179 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_170, x_177, x_178, x_176, x_3);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
lean_dec_ref(x_179);
lean_inc(x_6);
x_180 = l_Lean_Compiler_LCNF_Simp_simp(x_171, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_170, x_6);
lean_dec(x_6);
lean_dec_ref(x_170);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_183 = x_182;
} else {
 lean_dec_ref(x_182);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_21;
}
lean_ctor_set(x_184, 0, x_181);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 1, 0);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_181);
lean_dec(x_21);
x_186 = lean_ctor_get(x_182, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_187 = x_182;
} else {
 lean_dec_ref(x_182);
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
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec_ref(x_170);
lean_dec(x_21);
lean_dec(x_6);
x_189 = lean_ctor_get(x_180, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_190 = x_180;
} else {
 lean_dec_ref(x_180);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec_ref(x_171);
lean_dec_ref(x_170);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_192 = lean_ctor_get(x_179, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 x_193 = x_179;
} else {
 lean_dec_ref(x_179);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
return x_194;
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_ctor_get(x_166, 1);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_166, 2);
lean_inc_ref(x_201);
lean_dec_ref(x_166);
x_202 = lean_ctor_get(x_20, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_203 = x_20;
} else {
 lean_dec_ref(x_20);
 x_203 = lean_box(0);
}
x_204 = lean_unsigned_to_nat(0u);
x_205 = lean_nat_dec_eq(x_202, x_204);
if (x_205 == 1)
{
lean_object* x_206; 
lean_dec(x_203);
lean_dec(x_202);
lean_dec_ref(x_200);
x_206 = l_Lean_Compiler_LCNF_Simp_simp(x_201, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_209 = lean_alloc_ctor(1, 1, 0);
} else {
 x_209 = x_21;
}
lean_ctor_set(x_209, 0, x_207);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 1, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_21);
x_211 = lean_ctor_get(x_206, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_212 = x_206;
} else {
 lean_dec_ref(x_206);
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
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_214 = lean_unsigned_to_nat(1u);
x_215 = lean_nat_sub(x_202, x_214);
lean_dec(x_202);
if (lean_is_scalar(x_203)) {
 x_216 = lean_alloc_ctor(0, 1, 0);
} else {
 x_216 = x_203;
 lean_ctor_set_tag(x_216, 0);
}
lean_ctor_set(x_216, 0, x_215);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_216);
x_218 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_219 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_217, x_218, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
x_221 = l_Lean_Compiler_LCNF_instInhabitedParam_default;
x_222 = lean_array_get_borrowed(x_221, x_200, x_204);
x_223 = lean_ctor_get(x_222, 0);
x_224 = lean_ctor_get(x_220, 0);
lean_inc(x_224);
lean_inc(x_223);
x_225 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_223, x_224, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
lean_dec_ref(x_225);
lean_inc(x_6);
x_226 = l_Lean_Compiler_LCNF_Simp_simp(x_201, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
x_228 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_200, x_6);
lean_dec(x_6);
lean_dec_ref(x_200);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_229 = x_228;
} else {
 lean_dec_ref(x_228);
 x_229 = lean_box(0);
}
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_220);
lean_ctor_set(x_230, 1, x_227);
if (lean_is_scalar(x_21)) {
 x_231 = lean_alloc_ctor(1, 1, 0);
} else {
 x_231 = x_21;
}
lean_ctor_set(x_231, 0, x_230);
if (lean_is_scalar(x_229)) {
 x_232 = lean_alloc_ctor(0, 1, 0);
} else {
 x_232 = x_229;
}
lean_ctor_set(x_232, 0, x_231);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_227);
lean_dec(x_220);
lean_dec(x_21);
x_233 = lean_ctor_get(x_228, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_234 = x_228;
} else {
 lean_dec_ref(x_228);
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
lean_dec(x_220);
lean_dec_ref(x_200);
lean_dec(x_21);
lean_dec(x_6);
x_236 = lean_ctor_get(x_226, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_237 = x_226;
} else {
 lean_dec_ref(x_226);
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
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_220);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_239 = lean_ctor_get(x_225, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 x_240 = x_225;
} else {
 lean_dec_ref(x_225);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 1, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_242 = lean_ctor_get(x_219, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_243 = x_219;
} else {
 lean_dec_ref(x_219);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_242);
return x_244;
}
}
}
}
else
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_20);
x_245 = lean_ctor_get(x_166, 0);
lean_inc_ref(x_245);
lean_dec_ref(x_166);
x_246 = l_Lean_Compiler_LCNF_Simp_simp(x_245, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_249 = lean_alloc_ctor(1, 1, 0);
} else {
 x_249 = x_21;
}
lean_ctor_set(x_249, 0, x_247);
if (lean_is_scalar(x_248)) {
 x_250 = lean_alloc_ctor(0, 1, 0);
} else {
 x_250 = x_248;
}
lean_ctor_set(x_250, 0, x_249);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_21);
x_251 = lean_ctor_get(x_246, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_252 = x_246;
} else {
 lean_dec_ref(x_246);
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
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_166);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_254 = lean_ctor_get(x_169, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_255 = x_169;
} else {
 lean_dec_ref(x_169);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 1, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_166);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_257 = lean_ctor_get(x_168, 0);
lean_inc(x_257);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_258 = x_168;
} else {
 lean_dec_ref(x_168);
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
else
{
lean_object* x_260; 
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
x_260 = lean_box(0);
lean_ctor_set(x_17, 0, x_260);
return x_17;
}
}
else
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_17, 0);
lean_inc(x_261);
lean_dec(x_17);
if (lean_obj_tag(x_261) == 1)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
x_264 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_262);
x_265 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_264);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_268 = x_265;
} else {
 lean_dec_ref(x_265);
 x_268 = lean_box(0);
}
lean_ctor_set_tag(x_14, 4);
lean_ctor_set(x_14, 0, x_267);
x_269 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_14, x_6);
lean_dec_ref(x_14);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
lean_dec_ref(x_269);
x_270 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_270) == 0)
{
lean_dec_ref(x_270);
if (lean_obj_tag(x_266) == 0)
{
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
lean_dec(x_268);
x_271 = lean_ctor_get(x_266, 1);
lean_inc_ref(x_271);
x_272 = lean_ctor_get(x_266, 2);
lean_inc_ref(x_272);
lean_dec_ref(x_266);
x_273 = lean_ctor_get(x_262, 0);
lean_inc_ref(x_273);
x_274 = lean_ctor_get(x_262, 1);
lean_inc_ref(x_274);
lean_dec_ref(x_262);
x_297 = lean_ctor_get(x_273, 3);
lean_inc(x_297);
lean_dec_ref(x_273);
x_298 = lean_unsigned_to_nat(0u);
x_299 = lean_array_get_size(x_274);
x_300 = lean_nat_dec_le(x_297, x_298);
if (x_300 == 0)
{
x_275 = x_297;
x_276 = x_299;
goto block_296;
}
else
{
lean_dec(x_297);
x_275 = x_298;
x_276 = x_299;
goto block_296;
}
block_296:
{
lean_object* x_277; size_t x_278; size_t x_279; lean_object* x_280; 
x_277 = l_Array_toSubarray___redArg(x_274, x_275, x_276);
x_278 = lean_array_size(x_271);
x_279 = 0;
x_280 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_271, x_278, x_279, x_277, x_3);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; 
lean_dec_ref(x_280);
lean_inc(x_6);
x_281 = l_Lean_Compiler_LCNF_Simp_simp(x_272, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
lean_dec_ref(x_281);
x_283 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_271, x_6);
lean_dec(x_6);
lean_dec_ref(x_271);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_284 = x_283;
} else {
 lean_dec_ref(x_283);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_285 = lean_alloc_ctor(1, 1, 0);
} else {
 x_285 = x_263;
}
lean_ctor_set(x_285, 0, x_282);
if (lean_is_scalar(x_284)) {
 x_286 = lean_alloc_ctor(0, 1, 0);
} else {
 x_286 = x_284;
}
lean_ctor_set(x_286, 0, x_285);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_282);
lean_dec(x_263);
x_287 = lean_ctor_get(x_283, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_288 = x_283;
} else {
 lean_dec_ref(x_283);
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
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec_ref(x_271);
lean_dec(x_263);
lean_dec(x_6);
x_290 = lean_ctor_get(x_281, 0);
lean_inc(x_290);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 x_291 = x_281;
} else {
 lean_dec_ref(x_281);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 1, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_290);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec_ref(x_272);
lean_dec_ref(x_271);
lean_dec(x_263);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_293 = lean_ctor_get(x_280, 0);
lean_inc(x_293);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_294 = x_280;
} else {
 lean_dec_ref(x_280);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 1, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_293);
return x_295;
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_301 = lean_ctor_get(x_266, 1);
lean_inc_ref(x_301);
x_302 = lean_ctor_get(x_266, 2);
lean_inc_ref(x_302);
lean_dec_ref(x_266);
x_303 = lean_ctor_get(x_262, 0);
lean_inc(x_303);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 x_304 = x_262;
} else {
 lean_dec_ref(x_262);
 x_304 = lean_box(0);
}
x_305 = lean_unsigned_to_nat(0u);
x_306 = lean_nat_dec_eq(x_303, x_305);
if (x_306 == 1)
{
lean_object* x_307; 
lean_dec(x_304);
lean_dec(x_303);
lean_dec_ref(x_301);
lean_dec(x_268);
x_307 = l_Lean_Compiler_LCNF_Simp_simp(x_302, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_309 = x_307;
} else {
 lean_dec_ref(x_307);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_310 = lean_alloc_ctor(1, 1, 0);
} else {
 x_310 = x_263;
}
lean_ctor_set(x_310, 0, x_308);
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
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_263);
x_312 = lean_ctor_get(x_307, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_313 = x_307;
} else {
 lean_dec_ref(x_307);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 1, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_312);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_315 = lean_unsigned_to_nat(1u);
x_316 = lean_nat_sub(x_303, x_315);
lean_dec(x_303);
if (lean_is_scalar(x_304)) {
 x_317 = lean_alloc_ctor(0, 1, 0);
} else {
 x_317 = x_304;
 lean_ctor_set_tag(x_317, 0);
}
lean_ctor_set(x_317, 0, x_316);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_317);
x_319 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_320 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_318, x_319, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
lean_dec_ref(x_320);
x_322 = l_Lean_Compiler_LCNF_instInhabitedParam_default;
x_323 = lean_array_get_borrowed(x_322, x_301, x_305);
x_324 = lean_ctor_get(x_323, 0);
x_325 = lean_ctor_get(x_321, 0);
lean_inc(x_325);
lean_inc(x_324);
x_326 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_324, x_325, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
lean_dec_ref(x_326);
lean_inc(x_6);
x_327 = l_Lean_Compiler_LCNF_Simp_simp(x_302, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
lean_dec_ref(x_327);
x_329 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_301, x_6);
lean_dec(x_6);
lean_dec_ref(x_301);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 x_330 = x_329;
} else {
 lean_dec_ref(x_329);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_268;
}
lean_ctor_set(x_331, 0, x_321);
lean_ctor_set(x_331, 1, x_328);
if (lean_is_scalar(x_263)) {
 x_332 = lean_alloc_ctor(1, 1, 0);
} else {
 x_332 = x_263;
}
lean_ctor_set(x_332, 0, x_331);
if (lean_is_scalar(x_330)) {
 x_333 = lean_alloc_ctor(0, 1, 0);
} else {
 x_333 = x_330;
}
lean_ctor_set(x_333, 0, x_332);
return x_333;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_328);
lean_dec(x_321);
lean_dec(x_268);
lean_dec(x_263);
x_334 = lean_ctor_get(x_329, 0);
lean_inc(x_334);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 x_335 = x_329;
} else {
 lean_dec_ref(x_329);
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
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_321);
lean_dec_ref(x_301);
lean_dec(x_268);
lean_dec(x_263);
lean_dec(x_6);
x_337 = lean_ctor_get(x_327, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 x_338 = x_327;
} else {
 lean_dec_ref(x_327);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 1, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_337);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_321);
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec(x_268);
lean_dec(x_263);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_340 = lean_ctor_get(x_326, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_341 = x_326;
} else {
 lean_dec_ref(x_326);
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
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec(x_268);
lean_dec(x_263);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_343 = lean_ctor_get(x_320, 0);
lean_inc(x_343);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_344 = x_320;
} else {
 lean_dec_ref(x_320);
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
}
else
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_268);
lean_dec(x_262);
x_346 = lean_ctor_get(x_266, 0);
lean_inc_ref(x_346);
lean_dec_ref(x_266);
x_347 = l_Lean_Compiler_LCNF_Simp_simp(x_346, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
if (lean_is_scalar(x_263)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_263;
}
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
lean_dec(x_263);
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
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_268);
lean_dec(x_266);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_355 = lean_ctor_get(x_270, 0);
lean_inc(x_355);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 x_356 = x_270;
} else {
 lean_dec_ref(x_270);
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
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_268);
lean_dec(x_266);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_358 = lean_ctor_get(x_269, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 x_359 = x_269;
} else {
 lean_dec_ref(x_269);
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
else
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_261);
lean_free_object(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_361 = lean_box(0);
x_362 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_362, 0, x_361);
return x_362;
}
}
}
else
{
uint8_t x_363; 
lean_free_object(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_363 = !lean_is_exclusive(x_17);
if (x_363 == 0)
{
return x_17;
}
else
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_17, 0);
lean_inc(x_364);
lean_dec(x_17);
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_364);
return x_365;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_14, 0);
lean_inc(x_366);
lean_dec(x_14);
x_367 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_366, x_4, x_6, x_8);
lean_dec(x_366);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 x_369 = x_367;
} else {
 lean_dec_ref(x_367);
 x_369 = lean_box(0);
}
if (lean_obj_tag(x_368) == 1)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_369);
x_370 = lean_ctor_get(x_368, 0);
lean_inc(x_370);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 x_371 = x_368;
} else {
 lean_dec_ref(x_368);
 x_371 = lean_box(0);
}
x_372 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_370);
x_373 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_372);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_376 = x_373;
} else {
 lean_dec_ref(x_373);
 x_376 = lean_box(0);
}
x_377 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_377, 0, x_375);
x_378 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_377, x_6);
lean_dec_ref(x_377);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
lean_dec_ref(x_378);
x_379 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_379) == 0)
{
lean_dec_ref(x_379);
if (lean_obj_tag(x_374) == 0)
{
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
lean_dec(x_376);
x_380 = lean_ctor_get(x_374, 1);
lean_inc_ref(x_380);
x_381 = lean_ctor_get(x_374, 2);
lean_inc_ref(x_381);
lean_dec_ref(x_374);
x_382 = lean_ctor_get(x_370, 0);
lean_inc_ref(x_382);
x_383 = lean_ctor_get(x_370, 1);
lean_inc_ref(x_383);
lean_dec_ref(x_370);
x_406 = lean_ctor_get(x_382, 3);
lean_inc(x_406);
lean_dec_ref(x_382);
x_407 = lean_unsigned_to_nat(0u);
x_408 = lean_array_get_size(x_383);
x_409 = lean_nat_dec_le(x_406, x_407);
if (x_409 == 0)
{
x_384 = x_406;
x_385 = x_408;
goto block_405;
}
else
{
lean_dec(x_406);
x_384 = x_407;
x_385 = x_408;
goto block_405;
}
block_405:
{
lean_object* x_386; size_t x_387; size_t x_388; lean_object* x_389; 
x_386 = l_Array_toSubarray___redArg(x_383, x_384, x_385);
x_387 = lean_array_size(x_380);
x_388 = 0;
x_389 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_380, x_387, x_388, x_386, x_3);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; 
lean_dec_ref(x_389);
lean_inc(x_6);
x_390 = l_Lean_Compiler_LCNF_Simp_simp(x_381, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec_ref(x_390);
x_392 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_380, x_6);
lean_dec(x_6);
lean_dec_ref(x_380);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 x_393 = x_392;
} else {
 lean_dec_ref(x_392);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_394 = lean_alloc_ctor(1, 1, 0);
} else {
 x_394 = x_371;
}
lean_ctor_set(x_394, 0, x_391);
if (lean_is_scalar(x_393)) {
 x_395 = lean_alloc_ctor(0, 1, 0);
} else {
 x_395 = x_393;
}
lean_ctor_set(x_395, 0, x_394);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_391);
lean_dec(x_371);
x_396 = lean_ctor_get(x_392, 0);
lean_inc(x_396);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 x_397 = x_392;
} else {
 lean_dec_ref(x_392);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 1, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_396);
return x_398;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec_ref(x_380);
lean_dec(x_371);
lean_dec(x_6);
x_399 = lean_ctor_get(x_390, 0);
lean_inc(x_399);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_400 = x_390;
} else {
 lean_dec_ref(x_390);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 1, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_399);
return x_401;
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec(x_371);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_402 = lean_ctor_get(x_389, 0);
lean_inc(x_402);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 x_403 = x_389;
} else {
 lean_dec_ref(x_389);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(1, 1, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_402);
return x_404;
}
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_410 = lean_ctor_get(x_374, 1);
lean_inc_ref(x_410);
x_411 = lean_ctor_get(x_374, 2);
lean_inc_ref(x_411);
lean_dec_ref(x_374);
x_412 = lean_ctor_get(x_370, 0);
lean_inc(x_412);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 x_413 = x_370;
} else {
 lean_dec_ref(x_370);
 x_413 = lean_box(0);
}
x_414 = lean_unsigned_to_nat(0u);
x_415 = lean_nat_dec_eq(x_412, x_414);
if (x_415 == 1)
{
lean_object* x_416; 
lean_dec(x_413);
lean_dec(x_412);
lean_dec_ref(x_410);
lean_dec(x_376);
x_416 = l_Lean_Compiler_LCNF_Simp_simp(x_411, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_418 = x_416;
} else {
 lean_dec_ref(x_416);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_419 = lean_alloc_ctor(1, 1, 0);
} else {
 x_419 = x_371;
}
lean_ctor_set(x_419, 0, x_417);
if (lean_is_scalar(x_418)) {
 x_420 = lean_alloc_ctor(0, 1, 0);
} else {
 x_420 = x_418;
}
lean_ctor_set(x_420, 0, x_419);
return x_420;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_371);
x_421 = lean_ctor_get(x_416, 0);
lean_inc(x_421);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_422 = x_416;
} else {
 lean_dec_ref(x_416);
 x_422 = lean_box(0);
}
if (lean_is_scalar(x_422)) {
 x_423 = lean_alloc_ctor(1, 1, 0);
} else {
 x_423 = x_422;
}
lean_ctor_set(x_423, 0, x_421);
return x_423;
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_424 = lean_unsigned_to_nat(1u);
x_425 = lean_nat_sub(x_412, x_424);
lean_dec(x_412);
if (lean_is_scalar(x_413)) {
 x_426 = lean_alloc_ctor(0, 1, 0);
} else {
 x_426 = x_413;
 lean_ctor_set_tag(x_426, 0);
}
lean_ctor_set(x_426, 0, x_425);
x_427 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_427, 0, x_426);
x_428 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_429 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_427, x_428, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
lean_dec_ref(x_429);
x_431 = l_Lean_Compiler_LCNF_instInhabitedParam_default;
x_432 = lean_array_get_borrowed(x_431, x_410, x_414);
x_433 = lean_ctor_get(x_432, 0);
x_434 = lean_ctor_get(x_430, 0);
lean_inc(x_434);
lean_inc(x_433);
x_435 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_433, x_434, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; 
lean_dec_ref(x_435);
lean_inc(x_6);
x_436 = l_Lean_Compiler_LCNF_Simp_simp(x_411, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
lean_dec_ref(x_436);
x_438 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_410, x_6);
lean_dec(x_6);
lean_dec_ref(x_410);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 x_439 = x_438;
} else {
 lean_dec_ref(x_438);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_376;
}
lean_ctor_set(x_440, 0, x_430);
lean_ctor_set(x_440, 1, x_437);
if (lean_is_scalar(x_371)) {
 x_441 = lean_alloc_ctor(1, 1, 0);
} else {
 x_441 = x_371;
}
lean_ctor_set(x_441, 0, x_440);
if (lean_is_scalar(x_439)) {
 x_442 = lean_alloc_ctor(0, 1, 0);
} else {
 x_442 = x_439;
}
lean_ctor_set(x_442, 0, x_441);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_437);
lean_dec(x_430);
lean_dec(x_376);
lean_dec(x_371);
x_443 = lean_ctor_get(x_438, 0);
lean_inc(x_443);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 x_444 = x_438;
} else {
 lean_dec_ref(x_438);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 1, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_430);
lean_dec_ref(x_410);
lean_dec(x_376);
lean_dec(x_371);
lean_dec(x_6);
x_446 = lean_ctor_get(x_436, 0);
lean_inc(x_446);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_447 = x_436;
} else {
 lean_dec_ref(x_436);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 1, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_446);
return x_448;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_430);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec(x_376);
lean_dec(x_371);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_449 = lean_ctor_get(x_435, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 x_450 = x_435;
} else {
 lean_dec_ref(x_435);
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
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec(x_376);
lean_dec(x_371);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_452 = lean_ctor_get(x_429, 0);
lean_inc(x_452);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 x_453 = x_429;
} else {
 lean_dec_ref(x_429);
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
}
}
else
{
lean_object* x_455; lean_object* x_456; 
lean_dec(x_376);
lean_dec(x_370);
x_455 = lean_ctor_get(x_374, 0);
lean_inc_ref(x_455);
lean_dec_ref(x_374);
x_456 = l_Lean_Compiler_LCNF_Simp_simp(x_455, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 x_458 = x_456;
} else {
 lean_dec_ref(x_456);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_459 = lean_alloc_ctor(1, 1, 0);
} else {
 x_459 = x_371;
}
lean_ctor_set(x_459, 0, x_457);
if (lean_is_scalar(x_458)) {
 x_460 = lean_alloc_ctor(0, 1, 0);
} else {
 x_460 = x_458;
}
lean_ctor_set(x_460, 0, x_459);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_371);
x_461 = lean_ctor_get(x_456, 0);
lean_inc(x_461);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 x_462 = x_456;
} else {
 lean_dec_ref(x_456);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 1, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_461);
return x_463;
}
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_dec(x_376);
lean_dec(x_374);
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_464 = lean_ctor_get(x_379, 0);
lean_inc(x_464);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_465 = x_379;
} else {
 lean_dec_ref(x_379);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(1, 1, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_464);
return x_466;
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_376);
lean_dec(x_374);
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_467 = lean_ctor_get(x_378, 0);
lean_inc(x_467);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 x_468 = x_378;
} else {
 lean_dec_ref(x_378);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(1, 1, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_467);
return x_469;
}
}
else
{
lean_object* x_470; lean_object* x_471; 
lean_dec(x_368);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_470 = lean_box(0);
if (lean_is_scalar(x_369)) {
 x_471 = lean_alloc_ctor(0, 1, 0);
} else {
 x_471 = x_369;
}
lean_ctor_set(x_471, 0, x_470);
return x_471;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_472 = lean_ctor_get(x_367, 0);
lean_inc(x_472);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 x_473 = x_367;
} else {
 lean_dec_ref(x_367);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 1, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_472);
return x_474;
}
}
}
else
{
lean_object* x_475; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_475 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_475) == 0)
{
uint8_t x_476; 
x_476 = !lean_is_exclusive(x_475);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; 
x_477 = lean_ctor_get(x_475, 0);
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_475, 0, x_478);
return x_475;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_475, 0);
lean_inc(x_479);
lean_dec(x_475);
x_480 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_480, 0, x_479);
x_481 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_481, 0, x_480);
return x_481;
}
}
else
{
uint8_t x_482; 
x_482 = !lean_is_exclusive(x_475);
if (x_482 == 0)
{
return x_475;
}
else
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_475, 0);
lean_inc(x_483);
lean_dec(x_475);
x_484 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_484, 0, x_483);
return x_484;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7_spec__8(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_3, x_13);
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
x_67 = x_2;
x_68 = lean_box(0);
goto block_69;
}
else
{
if (x_72 == 0)
{
x_67 = x_2;
x_68 = lean_box(0);
goto block_69;
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_71);
x_75 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_31, x_73, x_74, x_11);
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
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_3, x_13);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_46; uint8_t x_47; lean_object* x_64; uint8_t x_65; uint8_t x_67; lean_object* x_68; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
x_32 = lean_ctor_get(x_16, 2);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_array_get_size(x_31);
x_72 = lean_nat_dec_lt(x_70, x_71);
if (x_72 == 0)
{
x_67 = x_2;
x_68 = lean_box(0);
goto block_69;
}
else
{
if (x_72 == 0)
{
x_67 = x_2;
x_68 = lean_box(0);
goto block_69;
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_71);
x_75 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_31, x_73, x_74, x_11);
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
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
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
x_47 = x_65;
goto block_63;
}
}
block_69:
{
if (lean_obj_tag(x_32) == 6)
{
x_64 = lean_box(0);
x_65 = x_67;
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
x_64 = lean_box(0);
x_65 = x_67;
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
x_25 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7_spec__8(x_1, x_2, x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7_spec__8(x_1, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; uint8_t x_122; 
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
lean_inc_ref(x_108);
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
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_349; 
lean_free_object(x_138);
x_191 = lean_ctor_get(x_1, 0);
x_192 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_191);
x_349 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_122, x_191, x_3, x_6);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_384; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
lean_dec_ref(x_349);
x_384 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_191, x_350);
if (x_384 == 0)
{
goto block_383;
}
else
{
if (x_122 == 0)
{
x_351 = x_2;
x_352 = x_3;
x_353 = x_4;
x_354 = x_5;
x_355 = x_6;
x_356 = x_7;
x_357 = x_8;
x_358 = lean_box(0);
goto block_378;
}
else
{
goto block_383;
}
}
block_378:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_350, 2);
x_360 = lean_ctor_get(x_350, 3);
lean_inc(x_357);
lean_inc_ref(x_356);
lean_inc(x_355);
lean_inc_ref(x_354);
lean_inc_ref(x_353);
lean_inc(x_360);
x_361 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_360, x_351, x_353, x_354, x_355, x_356, x_357);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
lean_dec_ref(x_361);
if (lean_obj_tag(x_362) == 1)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec_ref(x_362);
x_364 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_352);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; 
lean_dec_ref(x_364);
x_365 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_350, x_363, x_355);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
lean_dec_ref(x_365);
x_367 = lean_ctor_get(x_366, 2);
lean_inc_ref(x_367);
x_368 = lean_ctor_get(x_366, 3);
lean_inc(x_368);
x_334 = x_366;
x_335 = x_367;
x_336 = x_368;
x_337 = x_351;
x_338 = x_352;
x_339 = x_353;
x_340 = x_354;
x_341 = x_355;
x_342 = x_356;
x_343 = x_357;
x_344 = lean_box(0);
goto block_348;
}
else
{
uint8_t x_369; 
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_351);
lean_dec_ref(x_1);
x_369 = !lean_is_exclusive(x_365);
if (x_369 == 0)
{
return x_365;
}
else
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_365, 0);
lean_inc(x_370);
lean_dec(x_365);
x_371 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_371, 0, x_370);
return x_371;
}
}
}
else
{
uint8_t x_372; 
lean_dec(x_363);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_351);
lean_dec(x_350);
lean_dec_ref(x_1);
x_372 = !lean_is_exclusive(x_364);
if (x_372 == 0)
{
return x_364;
}
else
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_364, 0);
lean_inc(x_373);
lean_dec(x_364);
x_374 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_374, 0, x_373);
return x_374;
}
}
}
else
{
lean_dec(x_362);
lean_inc(x_360);
lean_inc_ref(x_359);
x_334 = x_350;
x_335 = x_359;
x_336 = x_360;
x_337 = x_351;
x_338 = x_352;
x_339 = x_353;
x_340 = x_354;
x_341 = x_355;
x_342 = x_356;
x_343 = x_357;
x_344 = lean_box(0);
goto block_348;
}
}
else
{
uint8_t x_375; 
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_351);
lean_dec(x_350);
lean_dec_ref(x_1);
x_375 = !lean_is_exclusive(x_361);
if (x_375 == 0)
{
return x_361;
}
else
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_ctor_get(x_361, 0);
lean_inc(x_376);
lean_dec(x_361);
x_377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_377, 0, x_376);
return x_377;
}
}
}
block_383:
{
lean_object* x_379; 
x_379 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_379) == 0)
{
lean_dec_ref(x_379);
x_351 = x_2;
x_352 = x_3;
x_353 = x_4;
x_354 = x_5;
x_355 = x_6;
x_356 = x_7;
x_357 = x_8;
x_358 = lean_box(0);
goto block_378;
}
else
{
uint8_t x_380; 
lean_dec(x_350);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_380 = !lean_is_exclusive(x_379);
if (x_380 == 0)
{
return x_379;
}
else
{
lean_object* x_381; lean_object* x_382; 
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
lean_dec(x_379);
x_382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_382, 0, x_381);
return x_382;
}
}
}
}
else
{
uint8_t x_385; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_385 = !lean_is_exclusive(x_349);
if (x_385 == 0)
{
return x_349;
}
else
{
lean_object* x_386; lean_object* x_387; 
x_386 = lean_ctor_get(x_349, 0);
lean_inc(x_386);
lean_dec(x_349);
x_387 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_387, 0, x_386);
return x_387;
}
}
block_333:
{
if (x_202 == 0)
{
lean_object* x_203; 
lean_inc(x_201);
lean_inc_ref(x_193);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc_ref(x_200);
x_203 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_200, x_196, x_199, x_193, x_201);
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
lean_inc(x_201);
lean_inc_ref(x_193);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc_ref(x_198);
lean_inc(x_195);
lean_inc_ref(x_194);
x_207 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_194, x_195, x_198, x_196, x_199, x_193, x_201);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_205, x_208, x_194, x_195, x_198, x_196, x_199, x_193, x_201);
lean_dec(x_201);
lean_dec_ref(x_193);
lean_dec(x_199);
lean_dec_ref(x_196);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_205);
return x_209;
}
else
{
lean_dec(x_205);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
return x_207;
}
}
else
{
uint8_t x_210; 
lean_dec(x_205);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
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
lean_inc(x_201);
lean_inc_ref(x_193);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc_ref(x_200);
x_213 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_200, x_194, x_195, x_196, x_199, x_193, x_201);
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
x_2 = x_194;
x_3 = x_195;
x_4 = x_198;
x_5 = x_196;
x_6 = x_199;
x_7 = x_193;
x_8 = x_201;
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
x_2 = x_194;
x_3 = x_195;
x_4 = x_198;
x_5 = x_196;
x_6 = x_199;
x_7 = x_193;
x_8 = x_201;
goto _start;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_214);
x_223 = lean_ctor_get(x_200, 0);
x_224 = lean_ctor_get(x_200, 3);
x_225 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_224);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
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
x_228 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_223, x_227, x_195, x_199, x_193, x_201);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
lean_dec_ref(x_228);
x_229 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_199);
lean_dec_ref(x_200);
if (lean_obj_tag(x_229) == 0)
{
lean_dec_ref(x_229);
x_1 = x_192;
x_2 = x_194;
x_3 = x_195;
x_4 = x_198;
x_5 = x_196;
x_6 = x_199;
x_7 = x_193;
x_8 = x_201;
goto _start;
}
else
{
uint8_t x_231; 
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
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
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
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
lean_inc(x_201);
lean_inc_ref(x_193);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc_ref(x_198);
lean_inc(x_195);
lean_inc_ref(x_194);
lean_inc_ref(x_192);
lean_inc_ref(x_200);
x_237 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_200, x_192, x_194, x_195, x_198, x_196, x_199, x_193, x_201);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
if (lean_obj_tag(x_238) == 1)
{
lean_object* x_239; lean_object* x_240; 
lean_dec(x_201);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_199);
lean_dec(x_199);
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
lean_inc(x_201);
lean_inc_ref(x_193);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc_ref(x_198);
lean_inc(x_195);
lean_inc_ref(x_194);
lean_inc(x_224);
x_247 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_224, x_194, x_195, x_198, x_196, x_199, x_193, x_201);
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
x_252 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_223, x_251, x_195, x_199, x_193, x_201);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; 
lean_dec_ref(x_252);
x_253 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_199);
lean_dec_ref(x_200);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; 
lean_dec_ref(x_253);
lean_inc(x_201);
lean_inc_ref(x_193);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc_ref(x_198);
lean_inc(x_195);
lean_inc_ref(x_194);
x_254 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_194, x_195, x_198, x_196, x_199, x_193, x_201);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_250, x_255, x_194, x_195, x_198, x_196, x_199, x_193, x_201);
lean_dec(x_201);
lean_dec_ref(x_193);
lean_dec(x_199);
lean_dec_ref(x_196);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_250);
return x_256;
}
else
{
lean_dec(x_250);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
return x_254;
}
}
else
{
uint8_t x_257; 
lean_dec(x_250);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
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
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
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
lean_inc(x_201);
lean_inc_ref(x_193);
lean_inc(x_199);
lean_inc_ref(x_196);
lean_inc_ref(x_198);
lean_inc(x_195);
lean_inc_ref(x_194);
lean_inc_ref(x_192);
x_263 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_194, x_195, x_198, x_196, x_199, x_193, x_201);
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
lean_dec(x_201);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_268 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_199);
lean_dec(x_199);
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
x_275 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_200, x_194, x_195, x_198, x_196, x_199, x_193, x_201);
lean_dec(x_201);
lean_dec_ref(x_193);
lean_dec(x_199);
lean_dec_ref(x_196);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec_ref(x_194);
if (lean_obj_tag(x_275) == 0)
{
size_t x_276; size_t x_277; uint8_t x_278; 
lean_dec_ref(x_275);
x_276 = lean_ptr_addr(x_192);
x_277 = lean_ptr_addr(x_264);
x_278 = lean_usize_dec_eq(x_276, x_277);
if (x_278 == 0)
{
x_98 = x_264;
x_99 = lean_box(0);
x_100 = x_200;
x_101 = x_278;
goto block_105;
}
else
{
size_t x_279; size_t x_280; uint8_t x_281; 
x_279 = lean_ptr_addr(x_191);
x_280 = lean_ptr_addr(x_200);
x_281 = lean_usize_dec_eq(x_279, x_280);
x_98 = x_264;
x_99 = lean_box(0);
x_100 = x_200;
x_101 = x_281;
goto block_105;
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
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
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
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
return x_263;
}
}
}
else
{
uint8_t x_288; 
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
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
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
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
else
{
uint8_t x_294; 
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_294 = !lean_is_exclusive(x_225);
if (x_294 == 0)
{
return x_225;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_225, 0);
lean_inc(x_295);
lean_dec(x_225);
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
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_297 = !lean_is_exclusive(x_213);
if (x_297 == 0)
{
return x_213;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_213, 0);
lean_inc(x_298);
lean_dec(x_213);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_298);
return x_299;
}
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_300 = !lean_is_exclusive(x_203);
if (x_300 == 0)
{
return x_203;
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_203, 0);
lean_inc(x_301);
lean_dec(x_203);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_301);
return x_302;
}
}
}
else
{
lean_object* x_303; uint8_t x_304; 
lean_inc_ref(x_192);
lean_dec_ref(x_1);
x_303 = lean_st_ref_take(x_195);
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_305 = lean_ctor_get(x_200, 0);
x_306 = lean_ctor_get(x_303, 0);
x_307 = lean_box(0);
lean_inc(x_305);
x_308 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_306, x_305, x_307);
lean_ctor_set(x_303, 0, x_308);
x_309 = lean_st_ref_set(x_195, x_303);
x_310 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_199);
lean_dec_ref(x_200);
if (lean_obj_tag(x_310) == 0)
{
lean_dec_ref(x_310);
x_1 = x_192;
x_2 = x_194;
x_3 = x_195;
x_4 = x_198;
x_5 = x_196;
x_6 = x_199;
x_7 = x_193;
x_8 = x_201;
goto _start;
}
else
{
uint8_t x_312; 
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
x_312 = !lean_is_exclusive(x_310);
if (x_312 == 0)
{
return x_310;
}
else
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_310, 0);
lean_inc(x_313);
lean_dec(x_310);
x_314 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_314, 0, x_313);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_315 = lean_ctor_get(x_200, 0);
x_316 = lean_ctor_get(x_303, 0);
x_317 = lean_ctor_get(x_303, 1);
x_318 = lean_ctor_get(x_303, 2);
x_319 = lean_ctor_get(x_303, 3);
x_320 = lean_ctor_get_uint8(x_303, sizeof(void*)*7);
x_321 = lean_ctor_get(x_303, 4);
x_322 = lean_ctor_get(x_303, 5);
x_323 = lean_ctor_get(x_303, 6);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_303);
x_324 = lean_box(0);
lean_inc(x_315);
x_325 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_316, x_315, x_324);
x_326 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_317);
lean_ctor_set(x_326, 2, x_318);
lean_ctor_set(x_326, 3, x_319);
lean_ctor_set(x_326, 4, x_321);
lean_ctor_set(x_326, 5, x_322);
lean_ctor_set(x_326, 6, x_323);
lean_ctor_set_uint8(x_326, sizeof(void*)*7, x_320);
x_327 = lean_st_ref_set(x_195, x_326);
x_328 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_195, x_199);
lean_dec_ref(x_200);
if (lean_obj_tag(x_328) == 0)
{
lean_dec_ref(x_328);
x_1 = x_192;
x_2 = x_194;
x_3 = x_195;
x_4 = x_198;
x_5 = x_196;
x_6 = x_199;
x_7 = x_193;
x_8 = x_201;
goto _start;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
x_330 = lean_ctor_get(x_328, 0);
lean_inc(x_330);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_331 = x_328;
} else {
 lean_dec_ref(x_328);
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
}
}
block_348:
{
uint8_t x_345; 
x_345 = l_Lean_Expr_isErased(x_335);
lean_dec_ref(x_335);
if (x_345 == 0)
{
lean_dec(x_336);
x_193 = x_342;
x_194 = x_337;
x_195 = x_338;
x_196 = x_340;
x_197 = lean_box(0);
x_198 = x_339;
x_199 = x_341;
x_200 = x_334;
x_201 = x_343;
x_202 = x_122;
goto block_333;
}
else
{
lean_object* x_346; uint8_t x_347; 
x_346 = lean_box(1);
x_347 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_336, x_346);
lean_dec(x_336);
if (x_347 == 0)
{
x_193 = x_342;
x_194 = x_337;
x_195 = x_338;
x_196 = x_340;
x_197 = lean_box(0);
x_198 = x_339;
x_199 = x_341;
x_200 = x_334;
x_201 = x_343;
x_202 = x_345;
goto block_333;
}
else
{
x_193 = x_342;
x_194 = x_337;
x_195 = x_338;
x_196 = x_340;
x_197 = lean_box(0);
x_198 = x_339;
x_199 = x_341;
x_200 = x_334;
x_201 = x_343;
x_202 = x_122;
goto block_333;
}
}
}
}
case 3:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_free_object(x_138);
x_388 = lean_ctor_get(x_1, 0);
x_389 = lean_ctor_get(x_1, 1);
x_390 = lean_st_ref_get(x_3);
x_391 = lean_ctor_get(x_390, 0);
lean_inc_ref(x_391);
lean_dec(x_390);
lean_inc(x_388);
x_392 = l_Lean_Compiler_LCNF_normFVarImp(x_391, x_388, x_122);
lean_dec_ref(x_391);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
lean_dec_ref(x_392);
lean_inc_ref(x_389);
x_394 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_122, x_389, x_3);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_407; lean_object* x_413; lean_object* x_418; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 x_396 = x_394;
} else {
 lean_dec_ref(x_394);
 x_396 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_395);
x_418 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_393, x_395, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
lean_dec_ref(x_418);
if (lean_obj_tag(x_419) == 1)
{
lean_object* x_420; 
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_393);
lean_dec_ref(x_1);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
lean_dec_ref(x_419);
x_1 = x_420;
goto _start;
}
else
{
lean_object* x_422; 
lean_dec(x_419);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_393);
x_422 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_393, x_3);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; 
lean_dec_ref(x_422);
x_423 = lean_unsigned_to_nat(0u);
x_424 = lean_array_get_size(x_395);
x_425 = lean_nat_dec_lt(x_423, x_424);
if (x_425 == 0)
{
lean_dec(x_3);
x_407 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_426; uint8_t x_427; 
x_426 = lean_box(0);
x_427 = lean_nat_dec_le(x_424, x_424);
if (x_427 == 0)
{
if (x_425 == 0)
{
lean_dec(x_3);
x_407 = lean_box(0);
goto block_412;
}
else
{
size_t x_428; size_t x_429; lean_object* x_430; 
x_428 = 0;
x_429 = lean_usize_of_nat(x_424);
x_430 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_395, x_428, x_429, x_426, x_3);
lean_dec(x_3);
x_413 = x_430;
goto block_417;
}
}
else
{
size_t x_431; size_t x_432; lean_object* x_433; 
x_431 = 0;
x_432 = lean_usize_of_nat(x_424);
x_433 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_395, x_431, x_432, x_426, x_3);
lean_dec(x_3);
x_413 = x_433;
goto block_417;
}
}
}
else
{
uint8_t x_434; 
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_393);
lean_dec(x_3);
lean_dec_ref(x_1);
x_434 = !lean_is_exclusive(x_422);
if (x_434 == 0)
{
return x_422;
}
else
{
lean_object* x_435; lean_object* x_436; 
x_435 = lean_ctor_get(x_422, 0);
lean_inc(x_435);
lean_dec(x_422);
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_435);
return x_436;
}
}
}
}
else
{
uint8_t x_437; 
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_393);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_437 = !lean_is_exclusive(x_418);
if (x_437 == 0)
{
return x_418;
}
else
{
lean_object* x_438; lean_object* x_439; 
x_438 = lean_ctor_get(x_418, 0);
lean_inc(x_438);
lean_dec(x_418);
x_439 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_439, 0, x_438);
return x_439;
}
}
block_406:
{
if (x_398 == 0)
{
uint8_t x_399; 
x_399 = !lean_is_exclusive(x_1);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_1, 1);
lean_dec(x_400);
x_401 = lean_ctor_get(x_1, 0);
lean_dec(x_401);
lean_ctor_set(x_1, 1, x_395);
lean_ctor_set(x_1, 0, x_393);
if (lean_is_scalar(x_396)) {
 x_402 = lean_alloc_ctor(0, 1, 0);
} else {
 x_402 = x_396;
}
lean_ctor_set(x_402, 0, x_1);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; 
lean_dec(x_1);
x_403 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_403, 0, x_393);
lean_ctor_set(x_403, 1, x_395);
if (lean_is_scalar(x_396)) {
 x_404 = lean_alloc_ctor(0, 1, 0);
} else {
 x_404 = x_396;
}
lean_ctor_set(x_404, 0, x_403);
return x_404;
}
}
else
{
lean_object* x_405; 
lean_dec(x_395);
lean_dec(x_393);
if (lean_is_scalar(x_396)) {
 x_405 = lean_alloc_ctor(0, 1, 0);
} else {
 x_405 = x_396;
}
lean_ctor_set(x_405, 0, x_1);
return x_405;
}
}
block_412:
{
uint8_t x_408; 
x_408 = l_Lean_instBEqFVarId_beq(x_388, x_393);
if (x_408 == 0)
{
x_397 = lean_box(0);
x_398 = x_408;
goto block_406;
}
else
{
size_t x_409; size_t x_410; uint8_t x_411; 
x_409 = lean_ptr_addr(x_389);
x_410 = lean_ptr_addr(x_395);
x_411 = lean_usize_dec_eq(x_409, x_410);
x_397 = lean_box(0);
x_398 = x_411;
goto block_406;
}
}
block_417:
{
if (lean_obj_tag(x_413) == 0)
{
lean_dec_ref(x_413);
x_407 = lean_box(0);
goto block_412;
}
else
{
uint8_t x_414; 
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_393);
lean_dec_ref(x_1);
x_414 = !lean_is_exclusive(x_413);
if (x_414 == 0)
{
return x_413;
}
else
{
lean_object* x_415; lean_object* x_416; 
x_415 = lean_ctor_get(x_413, 0);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_416, 0, x_415);
return x_416;
}
}
}
}
else
{
uint8_t x_440; 
lean_dec(x_393);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_440 = !lean_is_exclusive(x_394);
if (x_440 == 0)
{
return x_394;
}
else
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_394, 0);
lean_inc(x_441);
lean_dec(x_394);
x_442 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_442, 0, x_441);
return x_442;
}
}
}
else
{
lean_object* x_443; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_443 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_443;
}
}
case 4:
{
lean_object* x_444; lean_object* x_445; 
lean_free_object(x_138);
x_444 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_444);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_444);
x_445 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_444, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_445) == 0)
{
uint8_t x_446; 
x_446 = !lean_is_exclusive(x_445);
if (x_446 == 0)
{
lean_object* x_447; 
x_447 = lean_ctor_get(x_445, 0);
if (lean_obj_tag(x_447) == 1)
{
lean_object* x_448; 
lean_dec_ref(x_444);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
lean_dec_ref(x_447);
lean_ctor_set(x_445, 0, x_448);
return x_445;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_447);
x_449 = lean_ctor_get(x_444, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_444, 1);
lean_inc_ref(x_450);
x_451 = lean_ctor_get(x_444, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_444, 3);
lean_inc_ref(x_452);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 lean_ctor_release(x_444, 2);
 lean_ctor_release(x_444, 3);
 x_453 = x_444;
} else {
 lean_dec_ref(x_444);
 x_453 = lean_box(0);
}
x_454 = lean_st_ref_get(x_3);
x_455 = lean_ctor_get(x_454, 0);
lean_inc_ref(x_455);
lean_dec(x_454);
lean_inc(x_451);
x_456 = l_Lean_Compiler_LCNF_normFVarImp(x_455, x_451, x_122);
lean_dec_ref(x_455);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 x_458 = x_456;
} else {
 lean_dec_ref(x_456);
 x_458 = lean_box(0);
}
x_459 = lean_st_ref_get(x_3);
x_460 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_452);
lean_inc(x_457);
x_461 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_457, x_122, x_460, x_452, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 x_463 = x_461;
} else {
 lean_dec_ref(x_461);
 x_463 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_464 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_462, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_481; lean_object* x_482; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_504; lean_object* x_509; uint8_t x_510; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_536; uint8_t x_537; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 x_466 = x_464;
} else {
 lean_dec_ref(x_464);
 x_466 = lean_box(0);
}
x_467 = lean_ctor_get(x_459, 0);
lean_inc_ref(x_467);
lean_dec(x_459);
lean_inc_ref(x_450);
x_468 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_467, x_122, x_450);
lean_dec_ref(x_467);
x_536 = lean_array_get_size(x_465);
x_537 = lean_nat_dec_eq(x_536, x_189);
if (x_537 == 0)
{
lean_free_object(x_445);
x_514 = x_3;
x_515 = x_5;
x_516 = x_6;
x_517 = x_7;
x_518 = x_8;
x_519 = lean_box(0);
goto block_535;
}
else
{
lean_object* x_538; 
x_538 = lean_array_fget_borrowed(x_465, x_460);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_550; lean_object* x_555; lean_object* x_556; uint8_t x_567; lean_object* x_568; uint8_t x_570; 
lean_free_object(x_445);
x_539 = lean_ctor_get(x_538, 1);
x_540 = lean_ctor_get(x_538, 2);
x_555 = lean_array_get_size(x_539);
x_570 = lean_nat_dec_lt(x_460, x_555);
if (x_570 == 0)
{
x_567 = x_122;
x_568 = lean_box(0);
goto block_569;
}
else
{
if (x_570 == 0)
{
x_567 = x_122;
x_568 = lean_box(0);
goto block_569;
}
else
{
size_t x_571; size_t x_572; lean_object* x_573; 
x_571 = 0;
x_572 = lean_usize_of_nat(x_555);
x_573 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_539, x_571, x_572, x_3);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; uint8_t x_575; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
lean_dec_ref(x_573);
x_575 = lean_unbox(x_574);
lean_dec(x_574);
x_567 = x_575;
x_568 = lean_box(0);
goto block_569;
}
else
{
uint8_t x_576; 
lean_dec_ref(x_468);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_463);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_576 = !lean_is_exclusive(x_573);
if (x_576 == 0)
{
return x_573;
}
else
{
lean_object* x_577; lean_object* x_578; 
x_577 = lean_ctor_get(x_573, 0);
lean_inc(x_577);
lean_dec(x_573);
x_578 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_578, 0, x_577);
return x_578;
}
}
}
}
block_549:
{
lean_object* x_542; 
x_542 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_542) == 0)
{
uint8_t x_543; 
x_543 = !lean_is_exclusive(x_542);
if (x_543 == 0)
{
lean_object* x_544; 
x_544 = lean_ctor_get(x_542, 0);
lean_dec(x_544);
lean_ctor_set(x_542, 0, x_540);
return x_542;
}
else
{
lean_object* x_545; 
lean_dec(x_542);
x_545 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_545, 0, x_540);
return x_545;
}
}
else
{
uint8_t x_546; 
lean_dec_ref(x_540);
x_546 = !lean_is_exclusive(x_542);
if (x_546 == 0)
{
return x_542;
}
else
{
lean_object* x_547; lean_object* x_548; 
x_547 = lean_ctor_get(x_542, 0);
lean_inc(x_547);
lean_dec(x_542);
x_548 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_548, 0, x_547);
return x_548;
}
}
}
block_554:
{
if (lean_obj_tag(x_550) == 0)
{
lean_dec_ref(x_550);
x_541 = lean_box(0);
goto block_549;
}
else
{
uint8_t x_551; 
lean_dec_ref(x_540);
lean_dec(x_3);
x_551 = !lean_is_exclusive(x_550);
if (x_551 == 0)
{
return x_550;
}
else
{
lean_object* x_552; lean_object* x_553; 
x_552 = lean_ctor_get(x_550, 0);
lean_inc(x_552);
lean_dec(x_550);
x_553 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_553, 0, x_552);
return x_553;
}
}
}
block_566:
{
uint8_t x_557; 
x_557 = lean_nat_dec_lt(x_460, x_555);
if (x_557 == 0)
{
lean_dec_ref(x_539);
lean_dec(x_6);
x_541 = lean_box(0);
goto block_549;
}
else
{
lean_object* x_558; uint8_t x_559; 
x_558 = lean_box(0);
x_559 = lean_nat_dec_le(x_555, x_555);
if (x_559 == 0)
{
if (x_557 == 0)
{
lean_dec_ref(x_539);
lean_dec(x_6);
x_541 = lean_box(0);
goto block_549;
}
else
{
size_t x_560; size_t x_561; lean_object* x_562; 
x_560 = 0;
x_561 = lean_usize_of_nat(x_555);
x_562 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_539, x_560, x_561, x_558, x_6);
lean_dec(x_6);
lean_dec_ref(x_539);
x_550 = x_562;
goto block_554;
}
}
else
{
size_t x_563; size_t x_564; lean_object* x_565; 
x_563 = 0;
x_564 = lean_usize_of_nat(x_555);
x_565 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_539, x_563, x_564, x_558, x_6);
lean_dec(x_6);
lean_dec_ref(x_539);
x_550 = x_565;
goto block_554;
}
}
}
block_569:
{
if (x_567 == 0)
{
lean_inc_ref(x_540);
lean_inc_ref(x_539);
lean_dec_ref(x_468);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_463);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_556 = lean_box(0);
goto block_566;
}
else
{
if (x_122 == 0)
{
x_514 = x_3;
x_515 = x_5;
x_516 = x_6;
x_517 = x_7;
x_518 = x_8;
x_519 = lean_box(0);
goto block_535;
}
else
{
lean_inc_ref(x_540);
lean_inc_ref(x_539);
lean_dec_ref(x_468);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_463);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_556 = lean_box(0);
goto block_566;
}
}
}
}
else
{
lean_object* x_579; 
lean_inc_ref(x_538);
lean_dec_ref(x_468);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_463);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_579 = lean_ctor_get(x_538, 0);
lean_inc_ref(x_579);
lean_dec_ref(x_538);
lean_ctor_set(x_445, 0, x_579);
return x_445;
}
}
block_480:
{
lean_object* x_471; 
x_471 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_469);
lean_dec(x_469);
if (lean_obj_tag(x_471) == 0)
{
uint8_t x_472; 
x_472 = !lean_is_exclusive(x_471);
if (x_472 == 0)
{
lean_object* x_473; lean_object* x_474; 
x_473 = lean_ctor_get(x_471, 0);
lean_dec(x_473);
if (lean_is_scalar(x_458)) {
 x_474 = lean_alloc_ctor(6, 1, 0);
} else {
 x_474 = x_458;
 lean_ctor_set_tag(x_474, 6);
}
lean_ctor_set(x_474, 0, x_468);
lean_ctor_set(x_471, 0, x_474);
return x_471;
}
else
{
lean_object* x_475; lean_object* x_476; 
lean_dec(x_471);
if (lean_is_scalar(x_458)) {
 x_475 = lean_alloc_ctor(6, 1, 0);
} else {
 x_475 = x_458;
 lean_ctor_set_tag(x_475, 6);
}
lean_ctor_set(x_475, 0, x_468);
x_476 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_476, 0, x_475);
return x_476;
}
}
else
{
uint8_t x_477; 
lean_dec_ref(x_468);
lean_dec(x_458);
x_477 = !lean_is_exclusive(x_471);
if (x_477 == 0)
{
return x_471;
}
else
{
lean_object* x_478; lean_object* x_479; 
x_478 = lean_ctor_get(x_471, 0);
lean_inc(x_478);
lean_dec(x_471);
x_479 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_479, 0, x_478);
return x_479;
}
}
}
block_486:
{
if (lean_obj_tag(x_482) == 0)
{
lean_dec_ref(x_482);
x_469 = x_481;
x_470 = lean_box(0);
goto block_480;
}
else
{
uint8_t x_483; 
lean_dec(x_481);
lean_dec_ref(x_468);
lean_dec(x_458);
x_483 = !lean_is_exclusive(x_482);
if (x_483 == 0)
{
return x_482;
}
else
{
lean_object* x_484; lean_object* x_485; 
x_484 = lean_ctor_get(x_482, 0);
lean_inc(x_484);
lean_dec(x_482);
x_485 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_485, 0, x_484);
return x_485;
}
}
}
block_503:
{
uint8_t x_494; 
x_494 = lean_nat_dec_lt(x_460, x_493);
if (x_494 == 0)
{
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec(x_489);
lean_dec_ref(x_488);
lean_dec(x_487);
lean_dec(x_465);
x_469 = x_491;
x_470 = lean_box(0);
goto block_480;
}
else
{
lean_object* x_495; uint8_t x_496; 
x_495 = lean_box(0);
x_496 = lean_nat_dec_le(x_493, x_493);
if (x_496 == 0)
{
if (x_494 == 0)
{
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec(x_489);
lean_dec_ref(x_488);
lean_dec(x_487);
lean_dec(x_465);
x_469 = x_491;
x_470 = lean_box(0);
goto block_480;
}
else
{
size_t x_497; size_t x_498; lean_object* x_499; 
x_497 = 0;
x_498 = lean_usize_of_nat(x_493);
lean_dec(x_493);
x_499 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_460, x_465, x_497, x_498, x_495, x_488, x_487, x_492, x_489);
lean_dec(x_489);
lean_dec_ref(x_492);
lean_dec(x_487);
lean_dec_ref(x_488);
lean_dec(x_465);
x_481 = x_491;
x_482 = x_499;
goto block_486;
}
}
else
{
size_t x_500; size_t x_501; lean_object* x_502; 
x_500 = 0;
x_501 = lean_usize_of_nat(x_493);
lean_dec(x_493);
x_502 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_460, x_465, x_500, x_501, x_495, x_488, x_487, x_492, x_489);
lean_dec(x_489);
lean_dec_ref(x_492);
lean_dec(x_487);
lean_dec_ref(x_488);
lean_dec(x_465);
x_481 = x_491;
x_482 = x_502;
goto block_486;
}
}
}
block_508:
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; 
if (lean_is_scalar(x_453)) {
 x_505 = lean_alloc_ctor(0, 4, 0);
} else {
 x_505 = x_453;
}
lean_ctor_set(x_505, 0, x_449);
lean_ctor_set(x_505, 1, x_468);
lean_ctor_set(x_505, 2, x_457);
lean_ctor_set(x_505, 3, x_465);
x_506 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_506, 0, x_505);
if (lean_is_scalar(x_466)) {
 x_507 = lean_alloc_ctor(0, 1, 0);
} else {
 x_507 = x_466;
}
lean_ctor_set(x_507, 0, x_506);
return x_507;
}
block_513:
{
if (x_510 == 0)
{
lean_dec(x_463);
lean_dec(x_451);
lean_dec_ref(x_1);
x_504 = lean_box(0);
goto block_508;
}
else
{
uint8_t x_511; 
x_511 = l_Lean_instBEqFVarId_beq(x_451, x_457);
lean_dec(x_451);
if (x_511 == 0)
{
lean_dec(x_463);
lean_dec_ref(x_1);
x_504 = lean_box(0);
goto block_508;
}
else
{
lean_object* x_512; 
lean_dec_ref(x_468);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_457);
lean_dec(x_453);
lean_dec(x_449);
if (lean_is_scalar(x_463)) {
 x_512 = lean_alloc_ctor(0, 1, 0);
} else {
 x_512 = x_463;
}
lean_ctor_set(x_512, 0, x_1);
return x_512;
}
}
}
block_535:
{
lean_object* x_520; uint8_t x_521; 
x_520 = lean_array_get_size(x_465);
x_521 = lean_nat_dec_lt(x_460, x_520);
if (x_521 == 0)
{
lean_dec(x_466);
lean_dec(x_463);
lean_dec(x_457);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_dec_ref(x_1);
x_487 = x_516;
x_488 = x_515;
x_489 = x_518;
x_490 = lean_box(0);
x_491 = x_514;
x_492 = x_517;
x_493 = x_520;
goto block_503;
}
else
{
if (x_521 == 0)
{
lean_dec(x_466);
lean_dec(x_463);
lean_dec(x_457);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_dec_ref(x_1);
x_487 = x_516;
x_488 = x_515;
x_489 = x_518;
x_490 = lean_box(0);
x_491 = x_514;
x_492 = x_517;
x_493 = x_520;
goto block_503;
}
else
{
size_t x_522; size_t x_523; uint8_t x_524; 
x_522 = 0;
x_523 = lean_usize_of_nat(x_520);
x_524 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_122, x_465, x_522, x_523);
if (x_524 == 0)
{
lean_dec(x_466);
lean_dec(x_463);
lean_dec(x_457);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_dec_ref(x_1);
x_487 = x_516;
x_488 = x_515;
x_489 = x_518;
x_490 = lean_box(0);
x_491 = x_514;
x_492 = x_517;
x_493 = x_520;
goto block_503;
}
else
{
if (x_122 == 0)
{
lean_object* x_525; 
lean_dec(x_518);
lean_dec_ref(x_517);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_458);
lean_inc(x_457);
x_525 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_457, x_514);
lean_dec(x_514);
if (lean_obj_tag(x_525) == 0)
{
size_t x_526; size_t x_527; uint8_t x_528; 
lean_dec_ref(x_525);
x_526 = lean_ptr_addr(x_452);
lean_dec_ref(x_452);
x_527 = lean_ptr_addr(x_465);
x_528 = lean_usize_dec_eq(x_526, x_527);
if (x_528 == 0)
{
lean_dec_ref(x_450);
x_509 = lean_box(0);
x_510 = x_528;
goto block_513;
}
else
{
size_t x_529; size_t x_530; uint8_t x_531; 
x_529 = lean_ptr_addr(x_450);
lean_dec_ref(x_450);
x_530 = lean_ptr_addr(x_468);
x_531 = lean_usize_dec_eq(x_529, x_530);
x_509 = lean_box(0);
x_510 = x_531;
goto block_513;
}
}
else
{
uint8_t x_532; 
lean_dec_ref(x_468);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_463);
lean_dec(x_457);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_dec_ref(x_1);
x_532 = !lean_is_exclusive(x_525);
if (x_532 == 0)
{
return x_525;
}
else
{
lean_object* x_533; lean_object* x_534; 
x_533 = lean_ctor_get(x_525, 0);
lean_inc(x_533);
lean_dec(x_525);
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_533);
return x_534;
}
}
}
else
{
lean_dec(x_466);
lean_dec(x_463);
lean_dec(x_457);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_dec_ref(x_1);
x_487 = x_516;
x_488 = x_515;
x_489 = x_518;
x_490 = lean_box(0);
x_491 = x_514;
x_492 = x_517;
x_493 = x_520;
goto block_503;
}
}
}
}
}
}
else
{
uint8_t x_580; 
lean_dec(x_463);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_free_object(x_445);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_580 = !lean_is_exclusive(x_464);
if (x_580 == 0)
{
return x_464;
}
else
{
lean_object* x_581; lean_object* x_582; 
x_581 = lean_ctor_get(x_464, 0);
lean_inc(x_581);
lean_dec(x_464);
x_582 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_582, 0, x_581);
return x_582;
}
}
}
else
{
uint8_t x_583; 
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_free_object(x_445);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_583 = !lean_is_exclusive(x_461);
if (x_583 == 0)
{
return x_461;
}
else
{
lean_object* x_584; lean_object* x_585; 
x_584 = lean_ctor_get(x_461, 0);
lean_inc(x_584);
lean_dec(x_461);
x_585 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_585, 0, x_584);
return x_585;
}
}
}
else
{
lean_object* x_586; 
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec(x_449);
lean_free_object(x_445);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_586 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_586;
}
}
}
else
{
lean_object* x_587; 
x_587 = lean_ctor_get(x_445, 0);
lean_inc(x_587);
lean_dec(x_445);
if (lean_obj_tag(x_587) == 1)
{
lean_object* x_588; lean_object* x_589; 
lean_dec_ref(x_444);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
lean_dec_ref(x_587);
x_589 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_589, 0, x_588);
return x_589;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_587);
x_590 = lean_ctor_get(x_444, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_444, 1);
lean_inc_ref(x_591);
x_592 = lean_ctor_get(x_444, 2);
lean_inc(x_592);
x_593 = lean_ctor_get(x_444, 3);
lean_inc_ref(x_593);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 lean_ctor_release(x_444, 2);
 lean_ctor_release(x_444, 3);
 x_594 = x_444;
} else {
 lean_dec_ref(x_444);
 x_594 = lean_box(0);
}
x_595 = lean_st_ref_get(x_3);
x_596 = lean_ctor_get(x_595, 0);
lean_inc_ref(x_596);
lean_dec(x_595);
lean_inc(x_592);
x_597 = l_Lean_Compiler_LCNF_normFVarImp(x_596, x_592, x_122);
lean_dec_ref(x_596);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 x_599 = x_597;
} else {
 lean_dec_ref(x_597);
 x_599 = lean_box(0);
}
x_600 = lean_st_ref_get(x_3);
x_601 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_593);
lean_inc(x_598);
x_602 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_598, x_122, x_601, x_593, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 x_604 = x_602;
} else {
 lean_dec_ref(x_602);
 x_604 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_605 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_603, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_620; lean_object* x_621; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_643; lean_object* x_648; uint8_t x_649; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_675; uint8_t x_676; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 x_607 = x_605;
} else {
 lean_dec_ref(x_605);
 x_607 = lean_box(0);
}
x_608 = lean_ctor_get(x_600, 0);
lean_inc_ref(x_608);
lean_dec(x_600);
lean_inc_ref(x_591);
x_609 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_608, x_122, x_591);
lean_dec_ref(x_608);
x_675 = lean_array_get_size(x_606);
x_676 = lean_nat_dec_eq(x_675, x_189);
if (x_676 == 0)
{
x_653 = x_3;
x_654 = x_5;
x_655 = x_6;
x_656 = x_7;
x_657 = x_8;
x_658 = lean_box(0);
goto block_674;
}
else
{
lean_object* x_677; 
x_677 = lean_array_fget_borrowed(x_606, x_601);
if (lean_obj_tag(x_677) == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_688; lean_object* x_693; lean_object* x_694; uint8_t x_705; lean_object* x_706; uint8_t x_708; 
x_678 = lean_ctor_get(x_677, 1);
x_679 = lean_ctor_get(x_677, 2);
x_693 = lean_array_get_size(x_678);
x_708 = lean_nat_dec_lt(x_601, x_693);
if (x_708 == 0)
{
x_705 = x_122;
x_706 = lean_box(0);
goto block_707;
}
else
{
if (x_708 == 0)
{
x_705 = x_122;
x_706 = lean_box(0);
goto block_707;
}
else
{
size_t x_709; size_t x_710; lean_object* x_711; 
x_709 = 0;
x_710 = lean_usize_of_nat(x_693);
x_711 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_678, x_709, x_710, x_3);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; uint8_t x_713; 
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
lean_dec_ref(x_711);
x_713 = lean_unbox(x_712);
lean_dec(x_712);
x_705 = x_713;
x_706 = lean_box(0);
goto block_707;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec_ref(x_609);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_604);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_714 = lean_ctor_get(x_711, 0);
lean_inc(x_714);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 x_715 = x_711;
} else {
 lean_dec_ref(x_711);
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
}
block_687:
{
lean_object* x_681; 
x_681 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; 
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 x_682 = x_681;
} else {
 lean_dec_ref(x_681);
 x_682 = lean_box(0);
}
if (lean_is_scalar(x_682)) {
 x_683 = lean_alloc_ctor(0, 1, 0);
} else {
 x_683 = x_682;
}
lean_ctor_set(x_683, 0, x_679);
return x_683;
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; 
lean_dec_ref(x_679);
x_684 = lean_ctor_get(x_681, 0);
lean_inc(x_684);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 x_685 = x_681;
} else {
 lean_dec_ref(x_681);
 x_685 = lean_box(0);
}
if (lean_is_scalar(x_685)) {
 x_686 = lean_alloc_ctor(1, 1, 0);
} else {
 x_686 = x_685;
}
lean_ctor_set(x_686, 0, x_684);
return x_686;
}
}
block_692:
{
if (lean_obj_tag(x_688) == 0)
{
lean_dec_ref(x_688);
x_680 = lean_box(0);
goto block_687;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
lean_dec_ref(x_679);
lean_dec(x_3);
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 x_690 = x_688;
} else {
 lean_dec_ref(x_688);
 x_690 = lean_box(0);
}
if (lean_is_scalar(x_690)) {
 x_691 = lean_alloc_ctor(1, 1, 0);
} else {
 x_691 = x_690;
}
lean_ctor_set(x_691, 0, x_689);
return x_691;
}
}
block_704:
{
uint8_t x_695; 
x_695 = lean_nat_dec_lt(x_601, x_693);
if (x_695 == 0)
{
lean_dec_ref(x_678);
lean_dec(x_6);
x_680 = lean_box(0);
goto block_687;
}
else
{
lean_object* x_696; uint8_t x_697; 
x_696 = lean_box(0);
x_697 = lean_nat_dec_le(x_693, x_693);
if (x_697 == 0)
{
if (x_695 == 0)
{
lean_dec_ref(x_678);
lean_dec(x_6);
x_680 = lean_box(0);
goto block_687;
}
else
{
size_t x_698; size_t x_699; lean_object* x_700; 
x_698 = 0;
x_699 = lean_usize_of_nat(x_693);
x_700 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_678, x_698, x_699, x_696, x_6);
lean_dec(x_6);
lean_dec_ref(x_678);
x_688 = x_700;
goto block_692;
}
}
else
{
size_t x_701; size_t x_702; lean_object* x_703; 
x_701 = 0;
x_702 = lean_usize_of_nat(x_693);
x_703 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_678, x_701, x_702, x_696, x_6);
lean_dec(x_6);
lean_dec_ref(x_678);
x_688 = x_703;
goto block_692;
}
}
}
block_707:
{
if (x_705 == 0)
{
lean_inc_ref(x_679);
lean_inc_ref(x_678);
lean_dec_ref(x_609);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_604);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_694 = lean_box(0);
goto block_704;
}
else
{
if (x_122 == 0)
{
x_653 = x_3;
x_654 = x_5;
x_655 = x_6;
x_656 = x_7;
x_657 = x_8;
x_658 = lean_box(0);
goto block_674;
}
else
{
lean_inc_ref(x_679);
lean_inc_ref(x_678);
lean_dec_ref(x_609);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_604);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_694 = lean_box(0);
goto block_704;
}
}
}
}
else
{
lean_object* x_717; lean_object* x_718; 
lean_inc_ref(x_677);
lean_dec_ref(x_609);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_604);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_717 = lean_ctor_get(x_677, 0);
lean_inc_ref(x_717);
lean_dec_ref(x_677);
x_718 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_718, 0, x_717);
return x_718;
}
}
block_619:
{
lean_object* x_612; 
x_612 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_610);
lean_dec(x_610);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 x_613 = x_612;
} else {
 lean_dec_ref(x_612);
 x_613 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_614 = lean_alloc_ctor(6, 1, 0);
} else {
 x_614 = x_599;
 lean_ctor_set_tag(x_614, 6);
}
lean_ctor_set(x_614, 0, x_609);
if (lean_is_scalar(x_613)) {
 x_615 = lean_alloc_ctor(0, 1, 0);
} else {
 x_615 = x_613;
}
lean_ctor_set(x_615, 0, x_614);
return x_615;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec_ref(x_609);
lean_dec(x_599);
x_616 = lean_ctor_get(x_612, 0);
lean_inc(x_616);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 x_617 = x_612;
} else {
 lean_dec_ref(x_612);
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
block_625:
{
if (lean_obj_tag(x_621) == 0)
{
lean_dec_ref(x_621);
x_610 = x_620;
x_611 = lean_box(0);
goto block_619;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_620);
lean_dec_ref(x_609);
lean_dec(x_599);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 x_623 = x_621;
} else {
 lean_dec_ref(x_621);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 1, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_622);
return x_624;
}
}
block_642:
{
uint8_t x_633; 
x_633 = lean_nat_dec_lt(x_601, x_632);
if (x_633 == 0)
{
lean_dec(x_632);
lean_dec_ref(x_631);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec(x_606);
x_610 = x_630;
x_611 = lean_box(0);
goto block_619;
}
else
{
lean_object* x_634; uint8_t x_635; 
x_634 = lean_box(0);
x_635 = lean_nat_dec_le(x_632, x_632);
if (x_635 == 0)
{
if (x_633 == 0)
{
lean_dec(x_632);
lean_dec_ref(x_631);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec(x_606);
x_610 = x_630;
x_611 = lean_box(0);
goto block_619;
}
else
{
size_t x_636; size_t x_637; lean_object* x_638; 
x_636 = 0;
x_637 = lean_usize_of_nat(x_632);
lean_dec(x_632);
x_638 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_601, x_606, x_636, x_637, x_634, x_627, x_626, x_631, x_628);
lean_dec(x_628);
lean_dec_ref(x_631);
lean_dec(x_626);
lean_dec_ref(x_627);
lean_dec(x_606);
x_620 = x_630;
x_621 = x_638;
goto block_625;
}
}
else
{
size_t x_639; size_t x_640; lean_object* x_641; 
x_639 = 0;
x_640 = lean_usize_of_nat(x_632);
lean_dec(x_632);
x_641 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_601, x_606, x_639, x_640, x_634, x_627, x_626, x_631, x_628);
lean_dec(x_628);
lean_dec_ref(x_631);
lean_dec(x_626);
lean_dec_ref(x_627);
lean_dec(x_606);
x_620 = x_630;
x_621 = x_641;
goto block_625;
}
}
}
block_647:
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
if (lean_is_scalar(x_594)) {
 x_644 = lean_alloc_ctor(0, 4, 0);
} else {
 x_644 = x_594;
}
lean_ctor_set(x_644, 0, x_590);
lean_ctor_set(x_644, 1, x_609);
lean_ctor_set(x_644, 2, x_598);
lean_ctor_set(x_644, 3, x_606);
x_645 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_645, 0, x_644);
if (lean_is_scalar(x_607)) {
 x_646 = lean_alloc_ctor(0, 1, 0);
} else {
 x_646 = x_607;
}
lean_ctor_set(x_646, 0, x_645);
return x_646;
}
block_652:
{
if (x_649 == 0)
{
lean_dec(x_604);
lean_dec(x_592);
lean_dec_ref(x_1);
x_643 = lean_box(0);
goto block_647;
}
else
{
uint8_t x_650; 
x_650 = l_Lean_instBEqFVarId_beq(x_592, x_598);
lean_dec(x_592);
if (x_650 == 0)
{
lean_dec(x_604);
lean_dec_ref(x_1);
x_643 = lean_box(0);
goto block_647;
}
else
{
lean_object* x_651; 
lean_dec_ref(x_609);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_598);
lean_dec(x_594);
lean_dec(x_590);
if (lean_is_scalar(x_604)) {
 x_651 = lean_alloc_ctor(0, 1, 0);
} else {
 x_651 = x_604;
}
lean_ctor_set(x_651, 0, x_1);
return x_651;
}
}
}
block_674:
{
lean_object* x_659; uint8_t x_660; 
x_659 = lean_array_get_size(x_606);
x_660 = lean_nat_dec_lt(x_601, x_659);
if (x_660 == 0)
{
lean_dec(x_607);
lean_dec(x_604);
lean_dec(x_598);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_1);
x_626 = x_655;
x_627 = x_654;
x_628 = x_657;
x_629 = lean_box(0);
x_630 = x_653;
x_631 = x_656;
x_632 = x_659;
goto block_642;
}
else
{
if (x_660 == 0)
{
lean_dec(x_607);
lean_dec(x_604);
lean_dec(x_598);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_1);
x_626 = x_655;
x_627 = x_654;
x_628 = x_657;
x_629 = lean_box(0);
x_630 = x_653;
x_631 = x_656;
x_632 = x_659;
goto block_642;
}
else
{
size_t x_661; size_t x_662; uint8_t x_663; 
x_661 = 0;
x_662 = lean_usize_of_nat(x_659);
x_663 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_122, x_606, x_661, x_662);
if (x_663 == 0)
{
lean_dec(x_607);
lean_dec(x_604);
lean_dec(x_598);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_1);
x_626 = x_655;
x_627 = x_654;
x_628 = x_657;
x_629 = lean_box(0);
x_630 = x_653;
x_631 = x_656;
x_632 = x_659;
goto block_642;
}
else
{
if (x_122 == 0)
{
lean_object* x_664; 
lean_dec(x_657);
lean_dec_ref(x_656);
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_599);
lean_inc(x_598);
x_664 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_598, x_653);
lean_dec(x_653);
if (lean_obj_tag(x_664) == 0)
{
size_t x_665; size_t x_666; uint8_t x_667; 
lean_dec_ref(x_664);
x_665 = lean_ptr_addr(x_593);
lean_dec_ref(x_593);
x_666 = lean_ptr_addr(x_606);
x_667 = lean_usize_dec_eq(x_665, x_666);
if (x_667 == 0)
{
lean_dec_ref(x_591);
x_648 = lean_box(0);
x_649 = x_667;
goto block_652;
}
else
{
size_t x_668; size_t x_669; uint8_t x_670; 
x_668 = lean_ptr_addr(x_591);
lean_dec_ref(x_591);
x_669 = lean_ptr_addr(x_609);
x_670 = lean_usize_dec_eq(x_668, x_669);
x_648 = lean_box(0);
x_649 = x_670;
goto block_652;
}
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec_ref(x_609);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_604);
lean_dec(x_598);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_1);
x_671 = lean_ctor_get(x_664, 0);
lean_inc(x_671);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 x_672 = x_664;
} else {
 lean_dec_ref(x_664);
 x_672 = lean_box(0);
}
if (lean_is_scalar(x_672)) {
 x_673 = lean_alloc_ctor(1, 1, 0);
} else {
 x_673 = x_672;
}
lean_ctor_set(x_673, 0, x_671);
return x_673;
}
}
else
{
lean_dec(x_607);
lean_dec(x_604);
lean_dec(x_598);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_1);
x_626 = x_655;
x_627 = x_654;
x_628 = x_657;
x_629 = lean_box(0);
x_630 = x_653;
x_631 = x_656;
x_632 = x_659;
goto block_642;
}
}
}
}
}
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec(x_604);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_719 = lean_ctor_get(x_605, 0);
lean_inc(x_719);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 x_720 = x_605;
} else {
 lean_dec_ref(x_605);
 x_720 = lean_box(0);
}
if (lean_is_scalar(x_720)) {
 x_721 = lean_alloc_ctor(1, 1, 0);
} else {
 x_721 = x_720;
}
lean_ctor_set(x_721, 0, x_719);
return x_721;
}
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_722 = lean_ctor_get(x_602, 0);
lean_inc(x_722);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 x_723 = x_602;
} else {
 lean_dec_ref(x_602);
 x_723 = lean_box(0);
}
if (lean_is_scalar(x_723)) {
 x_724 = lean_alloc_ctor(1, 1, 0);
} else {
 x_724 = x_723;
}
lean_ctor_set(x_724, 0, x_722);
return x_724;
}
}
else
{
lean_object* x_725; 
lean_dec(x_594);
lean_dec_ref(x_593);
lean_dec(x_592);
lean_dec_ref(x_591);
lean_dec(x_590);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_725 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_725;
}
}
}
}
else
{
uint8_t x_726; 
lean_dec_ref(x_444);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_726 = !lean_is_exclusive(x_445);
if (x_726 == 0)
{
return x_445;
}
else
{
lean_object* x_727; lean_object* x_728; 
x_727 = lean_ctor_get(x_445, 0);
lean_inc(x_727);
lean_dec(x_445);
x_728 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_728, 0, x_727);
return x_728;
}
}
}
case 5:
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_free_object(x_138);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_729 = lean_ctor_get(x_1, 0);
x_730 = lean_st_ref_get(x_3);
x_731 = lean_ctor_get(x_730, 0);
lean_inc_ref(x_731);
lean_dec(x_730);
lean_inc(x_729);
x_732 = l_Lean_Compiler_LCNF_normFVarImp(x_731, x_729, x_122);
lean_dec_ref(x_731);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; lean_object* x_734; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
lean_dec_ref(x_732);
lean_inc(x_733);
x_734 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_733, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_734) == 0)
{
uint8_t x_735; 
x_735 = !lean_is_exclusive(x_734);
if (x_735 == 0)
{
lean_object* x_736; uint8_t x_737; 
x_736 = lean_ctor_get(x_734, 0);
lean_dec(x_736);
x_737 = l_Lean_instBEqFVarId_beq(x_729, x_733);
if (x_737 == 0)
{
uint8_t x_738; 
x_738 = !lean_is_exclusive(x_1);
if (x_738 == 0)
{
lean_object* x_739; 
x_739 = lean_ctor_get(x_1, 0);
lean_dec(x_739);
lean_ctor_set(x_1, 0, x_733);
lean_ctor_set(x_734, 0, x_1);
return x_734;
}
else
{
lean_object* x_740; 
lean_dec(x_1);
x_740 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_740, 0, x_733);
lean_ctor_set(x_734, 0, x_740);
return x_734;
}
}
else
{
lean_dec(x_733);
lean_ctor_set(x_734, 0, x_1);
return x_734;
}
}
else
{
uint8_t x_741; 
lean_dec(x_734);
x_741 = l_Lean_instBEqFVarId_beq(x_729, x_733);
if (x_741 == 0)
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_742 = x_1;
} else {
 lean_dec_ref(x_1);
 x_742 = lean_box(0);
}
if (lean_is_scalar(x_742)) {
 x_743 = lean_alloc_ctor(5, 1, 0);
} else {
 x_743 = x_742;
}
lean_ctor_set(x_743, 0, x_733);
x_744 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_744, 0, x_743);
return x_744;
}
else
{
lean_object* x_745; 
lean_dec(x_733);
x_745 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_745, 0, x_1);
return x_745;
}
}
}
else
{
uint8_t x_746; 
lean_dec(x_733);
lean_dec_ref(x_1);
x_746 = !lean_is_exclusive(x_734);
if (x_746 == 0)
{
return x_734;
}
else
{
lean_object* x_747; lean_object* x_748; 
x_747 = lean_ctor_get(x_734, 0);
lean_inc(x_747);
lean_dec(x_734);
x_748 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_748, 0, x_747);
return x_748;
}
}
}
else
{
lean_object* x_749; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_749 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_749;
}
}
case 6:
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; size_t x_754; size_t x_755; uint8_t x_756; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_750 = lean_ctor_get(x_1, 0);
x_751 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_752 = lean_ctor_get(x_751, 0);
lean_inc_ref(x_752);
lean_dec(x_751);
lean_inc_ref(x_750);
x_753 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_752, x_122, x_750);
lean_dec_ref(x_752);
x_754 = lean_ptr_addr(x_750);
x_755 = lean_ptr_addr(x_753);
x_756 = lean_usize_dec_eq(x_754, x_755);
if (x_756 == 0)
{
uint8_t x_757; 
x_757 = !lean_is_exclusive(x_1);
if (x_757 == 0)
{
lean_object* x_758; 
x_758 = lean_ctor_get(x_1, 0);
lean_dec(x_758);
lean_ctor_set(x_1, 0, x_753);
lean_ctor_set(x_138, 0, x_1);
return x_138;
}
else
{
lean_object* x_759; 
lean_dec(x_1);
x_759 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_759, 0, x_753);
lean_ctor_set(x_138, 0, x_759);
return x_138;
}
}
else
{
lean_dec_ref(x_753);
lean_ctor_set(x_138, 0, x_1);
return x_138;
}
}
default: 
{
lean_object* x_760; lean_object* x_761; 
lean_free_object(x_138);
x_760 = lean_ctor_get(x_1, 0);
x_761 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_761);
lean_inc_ref(x_760);
x_141 = x_760;
x_142 = x_761;
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
x_81 = x_157;
x_82 = x_142;
x_83 = x_141;
x_84 = x_143;
x_85 = x_144;
x_86 = x_145;
x_87 = x_146;
x_88 = x_147;
x_89 = x_148;
x_90 = x_149;
x_91 = lean_box(0);
goto block_97;
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
x_81 = x_159;
x_82 = x_142;
x_83 = x_141;
x_84 = x_143;
x_85 = x_144;
x_86 = x_145;
x_87 = x_146;
x_88 = x_147;
x_89 = x_148;
x_90 = x_149;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_st_ref_get(x_144);
x_161 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_161);
lean_dec(x_160);
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
x_81 = x_167;
x_82 = x_142;
x_83 = x_165;
x_84 = x_143;
x_85 = x_144;
x_86 = x_145;
x_87 = x_146;
x_88 = x_147;
x_89 = x_148;
x_90 = x_149;
x_91 = lean_box(0);
goto block_97;
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
lean_dec(x_177);
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
x_49 = x_181;
x_50 = x_142;
x_51 = x_180;
x_52 = x_143;
x_53 = x_144;
x_54 = x_145;
x_55 = x_146;
x_56 = x_147;
x_57 = x_148;
x_58 = x_149;
x_59 = lean_box(0);
goto block_80;
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
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_810; lean_object* x_811; 
lean_dec(x_138);
x_810 = lean_unsigned_to_nat(1u);
x_811 = lean_nat_add(x_109, x_810);
lean_dec(x_109);
lean_ctor_set(x_7, 3, x_811);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_823; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_954; 
x_812 = lean_ctor_get(x_1, 0);
x_813 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_812);
x_954 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_122, x_812, x_3, x_6);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; uint8_t x_989; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
lean_dec_ref(x_954);
x_989 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_812, x_955);
if (x_989 == 0)
{
goto block_988;
}
else
{
if (x_122 == 0)
{
x_956 = x_2;
x_957 = x_3;
x_958 = x_4;
x_959 = x_5;
x_960 = x_6;
x_961 = x_7;
x_962 = x_8;
x_963 = lean_box(0);
goto block_983;
}
else
{
goto block_988;
}
}
block_983:
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; 
x_964 = lean_ctor_get(x_955, 2);
x_965 = lean_ctor_get(x_955, 3);
lean_inc(x_962);
lean_inc_ref(x_961);
lean_inc(x_960);
lean_inc_ref(x_959);
lean_inc_ref(x_958);
lean_inc(x_965);
x_966 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_965, x_956, x_958, x_959, x_960, x_961, x_962);
if (lean_obj_tag(x_966) == 0)
{
lean_object* x_967; 
x_967 = lean_ctor_get(x_966, 0);
lean_inc(x_967);
lean_dec_ref(x_966);
if (lean_obj_tag(x_967) == 1)
{
lean_object* x_968; lean_object* x_969; 
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
lean_dec_ref(x_967);
x_969 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_957);
if (lean_obj_tag(x_969) == 0)
{
lean_object* x_970; 
lean_dec_ref(x_969);
x_970 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_955, x_968, x_960);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
lean_dec_ref(x_970);
x_972 = lean_ctor_get(x_971, 2);
lean_inc_ref(x_972);
x_973 = lean_ctor_get(x_971, 3);
lean_inc(x_973);
x_939 = x_971;
x_940 = x_972;
x_941 = x_973;
x_942 = x_956;
x_943 = x_957;
x_944 = x_958;
x_945 = x_959;
x_946 = x_960;
x_947 = x_961;
x_948 = x_962;
x_949 = lean_box(0);
goto block_953;
}
else
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; 
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec_ref(x_958);
lean_dec(x_957);
lean_dec_ref(x_956);
lean_dec_ref(x_1);
x_974 = lean_ctor_get(x_970, 0);
lean_inc(x_974);
if (lean_is_exclusive(x_970)) {
 lean_ctor_release(x_970, 0);
 x_975 = x_970;
} else {
 lean_dec_ref(x_970);
 x_975 = lean_box(0);
}
if (lean_is_scalar(x_975)) {
 x_976 = lean_alloc_ctor(1, 1, 0);
} else {
 x_976 = x_975;
}
lean_ctor_set(x_976, 0, x_974);
return x_976;
}
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; 
lean_dec(x_968);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec_ref(x_958);
lean_dec(x_957);
lean_dec_ref(x_956);
lean_dec(x_955);
lean_dec_ref(x_1);
x_977 = lean_ctor_get(x_969, 0);
lean_inc(x_977);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 x_978 = x_969;
} else {
 lean_dec_ref(x_969);
 x_978 = lean_box(0);
}
if (lean_is_scalar(x_978)) {
 x_979 = lean_alloc_ctor(1, 1, 0);
} else {
 x_979 = x_978;
}
lean_ctor_set(x_979, 0, x_977);
return x_979;
}
}
else
{
lean_dec(x_967);
lean_inc(x_965);
lean_inc_ref(x_964);
x_939 = x_955;
x_940 = x_964;
x_941 = x_965;
x_942 = x_956;
x_943 = x_957;
x_944 = x_958;
x_945 = x_959;
x_946 = x_960;
x_947 = x_961;
x_948 = x_962;
x_949 = lean_box(0);
goto block_953;
}
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; 
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec_ref(x_958);
lean_dec(x_957);
lean_dec_ref(x_956);
lean_dec(x_955);
lean_dec_ref(x_1);
x_980 = lean_ctor_get(x_966, 0);
lean_inc(x_980);
if (lean_is_exclusive(x_966)) {
 lean_ctor_release(x_966, 0);
 x_981 = x_966;
} else {
 lean_dec_ref(x_966);
 x_981 = lean_box(0);
}
if (lean_is_scalar(x_981)) {
 x_982 = lean_alloc_ctor(1, 1, 0);
} else {
 x_982 = x_981;
}
lean_ctor_set(x_982, 0, x_980);
return x_982;
}
}
block_988:
{
lean_object* x_984; 
x_984 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_984) == 0)
{
lean_dec_ref(x_984);
x_956 = x_2;
x_957 = x_3;
x_958 = x_4;
x_959 = x_5;
x_960 = x_6;
x_961 = x_7;
x_962 = x_8;
x_963 = lean_box(0);
goto block_983;
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; 
lean_dec(x_955);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_985 = lean_ctor_get(x_984, 0);
lean_inc(x_985);
if (lean_is_exclusive(x_984)) {
 lean_ctor_release(x_984, 0);
 x_986 = x_984;
} else {
 lean_dec_ref(x_984);
 x_986 = lean_box(0);
}
if (lean_is_scalar(x_986)) {
 x_987 = lean_alloc_ctor(1, 1, 0);
} else {
 x_987 = x_986;
}
lean_ctor_set(x_987, 0, x_985);
return x_987;
}
}
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_990 = lean_ctor_get(x_954, 0);
lean_inc(x_990);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 x_991 = x_954;
} else {
 lean_dec_ref(x_954);
 x_991 = lean_box(0);
}
if (lean_is_scalar(x_991)) {
 x_992 = lean_alloc_ctor(1, 1, 0);
} else {
 x_992 = x_991;
}
lean_ctor_set(x_992, 0, x_990);
return x_992;
}
block_938:
{
if (x_823 == 0)
{
lean_object* x_824; 
lean_inc(x_822);
lean_inc_ref(x_814);
lean_inc(x_820);
lean_inc_ref(x_817);
lean_inc_ref(x_821);
x_824 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_821, x_817, x_820, x_814, x_822);
if (lean_obj_tag(x_824) == 0)
{
lean_object* x_825; 
x_825 = lean_ctor_get(x_824, 0);
lean_inc(x_825);
lean_dec_ref(x_824);
if (lean_obj_tag(x_825) == 1)
{
lean_object* x_826; lean_object* x_827; 
lean_dec_ref(x_821);
lean_inc_ref(x_813);
lean_dec_ref(x_1);
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
lean_dec_ref(x_825);
x_827 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_816);
if (lean_obj_tag(x_827) == 0)
{
lean_object* x_828; 
lean_dec_ref(x_827);
lean_inc(x_822);
lean_inc_ref(x_814);
lean_inc(x_820);
lean_inc_ref(x_817);
lean_inc_ref(x_819);
lean_inc(x_816);
lean_inc_ref(x_815);
x_828 = l_Lean_Compiler_LCNF_Simp_simp(x_813, x_815, x_816, x_819, x_817, x_820, x_814, x_822);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; lean_object* x_830; 
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
lean_dec_ref(x_828);
x_830 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_826, x_829, x_815, x_816, x_819, x_817, x_820, x_814, x_822);
lean_dec(x_822);
lean_dec_ref(x_814);
lean_dec(x_820);
lean_dec_ref(x_817);
lean_dec_ref(x_819);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec(x_826);
return x_830;
}
else
{
lean_dec(x_826);
lean_dec(x_822);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
return x_828;
}
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; 
lean_dec(x_826);
lean_dec(x_822);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_813);
x_831 = lean_ctor_get(x_827, 0);
lean_inc(x_831);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 x_832 = x_827;
} else {
 lean_dec_ref(x_827);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(1, 1, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_831);
return x_833;
}
}
else
{
lean_object* x_834; 
lean_dec(x_825);
lean_inc(x_822);
lean_inc_ref(x_814);
lean_inc(x_820);
lean_inc_ref(x_817);
lean_inc_ref(x_821);
x_834 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_821, x_815, x_816, x_817, x_820, x_814, x_822);
if (lean_obj_tag(x_834) == 0)
{
lean_object* x_835; 
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
lean_dec_ref(x_834);
if (lean_obj_tag(x_835) == 1)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
lean_dec_ref(x_821);
lean_inc_ref(x_813);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_836 = x_1;
} else {
 lean_dec_ref(x_1);
 x_836 = lean_box(0);
}
x_837 = lean_ctor_get(x_835, 0);
lean_inc(x_837);
lean_dec_ref(x_835);
if (lean_is_scalar(x_836)) {
 x_838 = lean_alloc_ctor(1, 2, 0);
} else {
 x_838 = x_836;
 lean_ctor_set_tag(x_838, 1);
}
lean_ctor_set(x_838, 0, x_837);
lean_ctor_set(x_838, 1, x_813);
x_1 = x_838;
x_2 = x_815;
x_3 = x_816;
x_4 = x_819;
x_5 = x_817;
x_6 = x_820;
x_7 = x_814;
x_8 = x_822;
goto _start;
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_835);
x_840 = lean_ctor_get(x_821, 0);
x_841 = lean_ctor_get(x_821, 3);
x_842 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_841);
if (lean_obj_tag(x_842) == 0)
{
lean_object* x_843; 
x_843 = lean_ctor_get(x_842, 0);
lean_inc(x_843);
lean_dec_ref(x_842);
if (lean_obj_tag(x_843) == 1)
{
lean_object* x_844; lean_object* x_845; 
lean_inc_ref(x_813);
lean_dec_ref(x_1);
x_844 = lean_ctor_get(x_843, 0);
lean_inc(x_844);
lean_dec_ref(x_843);
lean_inc(x_840);
x_845 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_840, x_844, x_816, x_820, x_814, x_822);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; 
lean_dec_ref(x_845);
x_846 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_821, x_816, x_820);
lean_dec_ref(x_821);
if (lean_obj_tag(x_846) == 0)
{
lean_dec_ref(x_846);
x_1 = x_813;
x_2 = x_815;
x_3 = x_816;
x_4 = x_819;
x_5 = x_817;
x_6 = x_820;
x_7 = x_814;
x_8 = x_822;
goto _start;
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_822);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_813);
x_848 = lean_ctor_get(x_846, 0);
lean_inc(x_848);
if (lean_is_exclusive(x_846)) {
 lean_ctor_release(x_846, 0);
 x_849 = x_846;
} else {
 lean_dec_ref(x_846);
 x_849 = lean_box(0);
}
if (lean_is_scalar(x_849)) {
 x_850 = lean_alloc_ctor(1, 1, 0);
} else {
 x_850 = x_849;
}
lean_ctor_set(x_850, 0, x_848);
return x_850;
}
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; 
lean_dec(x_822);
lean_dec_ref(x_821);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_813);
x_851 = lean_ctor_get(x_845, 0);
lean_inc(x_851);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 x_852 = x_845;
} else {
 lean_dec_ref(x_845);
 x_852 = lean_box(0);
}
if (lean_is_scalar(x_852)) {
 x_853 = lean_alloc_ctor(1, 1, 0);
} else {
 x_853 = x_852;
}
lean_ctor_set(x_853, 0, x_851);
return x_853;
}
}
else
{
lean_object* x_854; 
lean_dec(x_843);
lean_inc(x_822);
lean_inc_ref(x_814);
lean_inc(x_820);
lean_inc_ref(x_817);
lean_inc_ref(x_819);
lean_inc(x_816);
lean_inc_ref(x_815);
lean_inc_ref(x_813);
lean_inc_ref(x_821);
x_854 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_821, x_813, x_815, x_816, x_819, x_817, x_820, x_814, x_822);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
lean_dec_ref(x_854);
if (lean_obj_tag(x_855) == 1)
{
lean_object* x_856; lean_object* x_857; 
lean_dec(x_822);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_1);
x_856 = lean_ctor_get(x_855, 0);
lean_inc(x_856);
lean_dec_ref(x_855);
x_857 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_821, x_816, x_820);
lean_dec(x_820);
lean_dec(x_816);
lean_dec_ref(x_821);
if (lean_obj_tag(x_857) == 0)
{
lean_object* x_858; lean_object* x_859; 
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 x_858 = x_857;
} else {
 lean_dec_ref(x_857);
 x_858 = lean_box(0);
}
if (lean_is_scalar(x_858)) {
 x_859 = lean_alloc_ctor(0, 1, 0);
} else {
 x_859 = x_858;
}
lean_ctor_set(x_859, 0, x_856);
return x_859;
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_856);
x_860 = lean_ctor_get(x_857, 0);
lean_inc(x_860);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 x_861 = x_857;
} else {
 lean_dec_ref(x_857);
 x_861 = lean_box(0);
}
if (lean_is_scalar(x_861)) {
 x_862 = lean_alloc_ctor(1, 1, 0);
} else {
 x_862 = x_861;
}
lean_ctor_set(x_862, 0, x_860);
return x_862;
}
}
else
{
lean_object* x_863; 
lean_dec(x_855);
lean_inc(x_822);
lean_inc_ref(x_814);
lean_inc(x_820);
lean_inc_ref(x_817);
lean_inc_ref(x_819);
lean_inc(x_816);
lean_inc_ref(x_815);
lean_inc(x_841);
x_863 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_841, x_815, x_816, x_819, x_817, x_820, x_814, x_822);
if (lean_obj_tag(x_863) == 0)
{
lean_object* x_864; 
x_864 = lean_ctor_get(x_863, 0);
lean_inc(x_864);
lean_dec_ref(x_863);
if (lean_obj_tag(x_864) == 1)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_inc_ref(x_813);
lean_dec_ref(x_1);
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
lean_dec_ref(x_864);
x_866 = lean_ctor_get(x_865, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_865, 1);
lean_inc(x_867);
lean_dec(x_865);
lean_inc(x_840);
x_868 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_840, x_867, x_816, x_820, x_814, x_822);
if (lean_obj_tag(x_868) == 0)
{
lean_object* x_869; 
lean_dec_ref(x_868);
x_869 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_821, x_816, x_820);
lean_dec_ref(x_821);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; 
lean_dec_ref(x_869);
lean_inc(x_822);
lean_inc_ref(x_814);
lean_inc(x_820);
lean_inc_ref(x_817);
lean_inc_ref(x_819);
lean_inc(x_816);
lean_inc_ref(x_815);
x_870 = l_Lean_Compiler_LCNF_Simp_simp(x_813, x_815, x_816, x_819, x_817, x_820, x_814, x_822);
if (lean_obj_tag(x_870) == 0)
{
lean_object* x_871; lean_object* x_872; 
x_871 = lean_ctor_get(x_870, 0);
lean_inc(x_871);
lean_dec_ref(x_870);
x_872 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_866, x_871, x_815, x_816, x_819, x_817, x_820, x_814, x_822);
lean_dec(x_822);
lean_dec_ref(x_814);
lean_dec(x_820);
lean_dec_ref(x_817);
lean_dec_ref(x_819);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec(x_866);
return x_872;
}
else
{
lean_dec(x_866);
lean_dec(x_822);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
return x_870;
}
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_dec(x_866);
lean_dec(x_822);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_813);
x_873 = lean_ctor_get(x_869, 0);
lean_inc(x_873);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 x_874 = x_869;
} else {
 lean_dec_ref(x_869);
 x_874 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_875 = lean_alloc_ctor(1, 1, 0);
} else {
 x_875 = x_874;
}
lean_ctor_set(x_875, 0, x_873);
return x_875;
}
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
lean_dec(x_866);
lean_dec(x_822);
lean_dec_ref(x_821);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_813);
x_876 = lean_ctor_get(x_868, 0);
lean_inc(x_876);
if (lean_is_exclusive(x_868)) {
 lean_ctor_release(x_868, 0);
 x_877 = x_868;
} else {
 lean_dec_ref(x_868);
 x_877 = lean_box(0);
}
if (lean_is_scalar(x_877)) {
 x_878 = lean_alloc_ctor(1, 1, 0);
} else {
 x_878 = x_877;
}
lean_ctor_set(x_878, 0, x_876);
return x_878;
}
}
else
{
lean_object* x_879; 
lean_dec(x_864);
lean_inc(x_822);
lean_inc_ref(x_814);
lean_inc(x_820);
lean_inc_ref(x_817);
lean_inc_ref(x_819);
lean_inc(x_816);
lean_inc_ref(x_815);
lean_inc_ref(x_813);
x_879 = l_Lean_Compiler_LCNF_Simp_simp(x_813, x_815, x_816, x_819, x_817, x_820, x_814, x_822);
if (lean_obj_tag(x_879) == 0)
{
lean_object* x_880; lean_object* x_881; 
x_880 = lean_ctor_get(x_879, 0);
lean_inc(x_880);
lean_dec_ref(x_879);
x_881 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_840, x_816);
if (lean_obj_tag(x_881) == 0)
{
lean_object* x_882; uint8_t x_883; 
x_882 = lean_ctor_get(x_881, 0);
lean_inc(x_882);
lean_dec_ref(x_881);
x_883 = lean_unbox(x_882);
lean_dec(x_882);
if (x_883 == 0)
{
lean_object* x_884; 
lean_dec(x_822);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_1);
x_884 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_821, x_816, x_820);
lean_dec(x_820);
lean_dec(x_816);
lean_dec_ref(x_821);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; 
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 x_885 = x_884;
} else {
 lean_dec_ref(x_884);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(0, 1, 0);
} else {
 x_886 = x_885;
}
lean_ctor_set(x_886, 0, x_880);
return x_886;
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; 
lean_dec(x_880);
x_887 = lean_ctor_get(x_884, 0);
lean_inc(x_887);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 x_888 = x_884;
} else {
 lean_dec_ref(x_884);
 x_888 = lean_box(0);
}
if (lean_is_scalar(x_888)) {
 x_889 = lean_alloc_ctor(1, 1, 0);
} else {
 x_889 = x_888;
}
lean_ctor_set(x_889, 0, x_887);
return x_889;
}
}
else
{
lean_object* x_890; 
lean_inc_ref(x_821);
x_890 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_821, x_815, x_816, x_819, x_817, x_820, x_814, x_822);
lean_dec(x_822);
lean_dec_ref(x_814);
lean_dec(x_820);
lean_dec_ref(x_817);
lean_dec_ref(x_819);
lean_dec(x_816);
lean_dec_ref(x_815);
if (lean_obj_tag(x_890) == 0)
{
size_t x_891; size_t x_892; uint8_t x_893; 
lean_dec_ref(x_890);
x_891 = lean_ptr_addr(x_813);
x_892 = lean_ptr_addr(x_880);
x_893 = lean_usize_dec_eq(x_891, x_892);
if (x_893 == 0)
{
x_98 = x_880;
x_99 = lean_box(0);
x_100 = x_821;
x_101 = x_893;
goto block_105;
}
else
{
size_t x_894; size_t x_895; uint8_t x_896; 
x_894 = lean_ptr_addr(x_812);
x_895 = lean_ptr_addr(x_821);
x_896 = lean_usize_dec_eq(x_894, x_895);
x_98 = x_880;
x_99 = lean_box(0);
x_100 = x_821;
x_101 = x_896;
goto block_105;
}
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
lean_dec(x_880);
lean_dec_ref(x_821);
lean_dec_ref(x_1);
x_897 = lean_ctor_get(x_890, 0);
lean_inc(x_897);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 x_898 = x_890;
} else {
 lean_dec_ref(x_890);
 x_898 = lean_box(0);
}
if (lean_is_scalar(x_898)) {
 x_899 = lean_alloc_ctor(1, 1, 0);
} else {
 x_899 = x_898;
}
lean_ctor_set(x_899, 0, x_897);
return x_899;
}
}
}
else
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_880);
lean_dec(x_822);
lean_dec_ref(x_821);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_1);
x_900 = lean_ctor_get(x_881, 0);
lean_inc(x_900);
if (lean_is_exclusive(x_881)) {
 lean_ctor_release(x_881, 0);
 x_901 = x_881;
} else {
 lean_dec_ref(x_881);
 x_901 = lean_box(0);
}
if (lean_is_scalar(x_901)) {
 x_902 = lean_alloc_ctor(1, 1, 0);
} else {
 x_902 = x_901;
}
lean_ctor_set(x_902, 0, x_900);
return x_902;
}
}
else
{
lean_dec(x_822);
lean_dec_ref(x_821);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_1);
return x_879;
}
}
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; 
lean_dec(x_822);
lean_dec_ref(x_821);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_1);
x_903 = lean_ctor_get(x_863, 0);
lean_inc(x_903);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 x_904 = x_863;
} else {
 lean_dec_ref(x_863);
 x_904 = lean_box(0);
}
if (lean_is_scalar(x_904)) {
 x_905 = lean_alloc_ctor(1, 1, 0);
} else {
 x_905 = x_904;
}
lean_ctor_set(x_905, 0, x_903);
return x_905;
}
}
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; 
lean_dec(x_822);
lean_dec_ref(x_821);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_1);
x_906 = lean_ctor_get(x_854, 0);
lean_inc(x_906);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 x_907 = x_854;
} else {
 lean_dec_ref(x_854);
 x_907 = lean_box(0);
}
if (lean_is_scalar(x_907)) {
 x_908 = lean_alloc_ctor(1, 1, 0);
} else {
 x_908 = x_907;
}
lean_ctor_set(x_908, 0, x_906);
return x_908;
}
}
}
else
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; 
lean_dec(x_822);
lean_dec_ref(x_821);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_1);
x_909 = lean_ctor_get(x_842, 0);
lean_inc(x_909);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 x_910 = x_842;
} else {
 lean_dec_ref(x_842);
 x_910 = lean_box(0);
}
if (lean_is_scalar(x_910)) {
 x_911 = lean_alloc_ctor(1, 1, 0);
} else {
 x_911 = x_910;
}
lean_ctor_set(x_911, 0, x_909);
return x_911;
}
}
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; 
lean_dec(x_822);
lean_dec_ref(x_821);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_1);
x_912 = lean_ctor_get(x_834, 0);
lean_inc(x_912);
if (lean_is_exclusive(x_834)) {
 lean_ctor_release(x_834, 0);
 x_913 = x_834;
} else {
 lean_dec_ref(x_834);
 x_913 = lean_box(0);
}
if (lean_is_scalar(x_913)) {
 x_914 = lean_alloc_ctor(1, 1, 0);
} else {
 x_914 = x_913;
}
lean_ctor_set(x_914, 0, x_912);
return x_914;
}
}
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; 
lean_dec(x_822);
lean_dec_ref(x_821);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_1);
x_915 = lean_ctor_get(x_824, 0);
lean_inc(x_915);
if (lean_is_exclusive(x_824)) {
 lean_ctor_release(x_824, 0);
 x_916 = x_824;
} else {
 lean_dec_ref(x_824);
 x_916 = lean_box(0);
}
if (lean_is_scalar(x_916)) {
 x_917 = lean_alloc_ctor(1, 1, 0);
} else {
 x_917 = x_916;
}
lean_ctor_set(x_917, 0, x_915);
return x_917;
}
}
else
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; uint8_t x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
lean_inc_ref(x_813);
lean_dec_ref(x_1);
x_918 = lean_st_ref_take(x_816);
x_919 = lean_ctor_get(x_821, 0);
x_920 = lean_ctor_get(x_918, 0);
lean_inc_ref(x_920);
x_921 = lean_ctor_get(x_918, 1);
lean_inc_ref(x_921);
x_922 = lean_ctor_get(x_918, 2);
lean_inc(x_922);
x_923 = lean_ctor_get(x_918, 3);
lean_inc_ref(x_923);
x_924 = lean_ctor_get_uint8(x_918, sizeof(void*)*7);
x_925 = lean_ctor_get(x_918, 4);
lean_inc(x_925);
x_926 = lean_ctor_get(x_918, 5);
lean_inc(x_926);
x_927 = lean_ctor_get(x_918, 6);
lean_inc(x_927);
if (lean_is_exclusive(x_918)) {
 lean_ctor_release(x_918, 0);
 lean_ctor_release(x_918, 1);
 lean_ctor_release(x_918, 2);
 lean_ctor_release(x_918, 3);
 lean_ctor_release(x_918, 4);
 lean_ctor_release(x_918, 5);
 lean_ctor_release(x_918, 6);
 x_928 = x_918;
} else {
 lean_dec_ref(x_918);
 x_928 = lean_box(0);
}
x_929 = lean_box(0);
lean_inc(x_919);
x_930 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_920, x_919, x_929);
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
x_932 = lean_st_ref_set(x_816, x_931);
x_933 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_821, x_816, x_820);
lean_dec_ref(x_821);
if (lean_obj_tag(x_933) == 0)
{
lean_dec_ref(x_933);
x_1 = x_813;
x_2 = x_815;
x_3 = x_816;
x_4 = x_819;
x_5 = x_817;
x_6 = x_820;
x_7 = x_814;
x_8 = x_822;
goto _start;
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; 
lean_dec(x_822);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_817);
lean_dec(x_816);
lean_dec_ref(x_815);
lean_dec_ref(x_814);
lean_dec_ref(x_813);
x_935 = lean_ctor_get(x_933, 0);
lean_inc(x_935);
if (lean_is_exclusive(x_933)) {
 lean_ctor_release(x_933, 0);
 x_936 = x_933;
} else {
 lean_dec_ref(x_933);
 x_936 = lean_box(0);
}
if (lean_is_scalar(x_936)) {
 x_937 = lean_alloc_ctor(1, 1, 0);
} else {
 x_937 = x_936;
}
lean_ctor_set(x_937, 0, x_935);
return x_937;
}
}
}
block_953:
{
uint8_t x_950; 
x_950 = l_Lean_Expr_isErased(x_940);
lean_dec_ref(x_940);
if (x_950 == 0)
{
lean_dec(x_941);
x_814 = x_947;
x_815 = x_942;
x_816 = x_943;
x_817 = x_945;
x_818 = lean_box(0);
x_819 = x_944;
x_820 = x_946;
x_821 = x_939;
x_822 = x_948;
x_823 = x_122;
goto block_938;
}
else
{
lean_object* x_951; uint8_t x_952; 
x_951 = lean_box(1);
x_952 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_941, x_951);
lean_dec(x_941);
if (x_952 == 0)
{
x_814 = x_947;
x_815 = x_942;
x_816 = x_943;
x_817 = x_945;
x_818 = lean_box(0);
x_819 = x_944;
x_820 = x_946;
x_821 = x_939;
x_822 = x_948;
x_823 = x_950;
goto block_938;
}
else
{
x_814 = x_947;
x_815 = x_942;
x_816 = x_943;
x_817 = x_945;
x_818 = lean_box(0);
x_819 = x_944;
x_820 = x_946;
x_821 = x_939;
x_822 = x_948;
x_823 = x_122;
goto block_938;
}
}
}
}
case 3:
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; 
x_993 = lean_ctor_get(x_1, 0);
x_994 = lean_ctor_get(x_1, 1);
x_995 = lean_st_ref_get(x_3);
x_996 = lean_ctor_get(x_995, 0);
lean_inc_ref(x_996);
lean_dec(x_995);
lean_inc(x_993);
x_997 = l_Lean_Compiler_LCNF_normFVarImp(x_996, x_993, x_122);
lean_dec_ref(x_996);
if (lean_obj_tag(x_997) == 0)
{
lean_object* x_998; lean_object* x_999; 
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
lean_dec_ref(x_997);
lean_inc_ref(x_994);
x_999 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_122, x_994, x_3);
if (lean_obj_tag(x_999) == 0)
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; lean_object* x_1009; lean_object* x_1015; lean_object* x_1020; 
x_1000 = lean_ctor_get(x_999, 0);
lean_inc(x_1000);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 x_1001 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1001 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1000);
x_1020 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_998, x_1000, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1020) == 0)
{
lean_object* x_1021; 
x_1021 = lean_ctor_get(x_1020, 0);
lean_inc(x_1021);
lean_dec_ref(x_1020);
if (lean_obj_tag(x_1021) == 1)
{
lean_object* x_1022; 
lean_dec(x_1001);
lean_dec(x_1000);
lean_dec(x_998);
lean_dec_ref(x_1);
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
lean_dec_ref(x_1021);
x_1 = x_1022;
goto _start;
}
else
{
lean_object* x_1024; 
lean_dec(x_1021);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_998);
x_1024 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_998, x_3);
if (lean_obj_tag(x_1024) == 0)
{
lean_object* x_1025; lean_object* x_1026; uint8_t x_1027; 
lean_dec_ref(x_1024);
x_1025 = lean_unsigned_to_nat(0u);
x_1026 = lean_array_get_size(x_1000);
x_1027 = lean_nat_dec_lt(x_1025, x_1026);
if (x_1027 == 0)
{
lean_dec(x_3);
x_1009 = lean_box(0);
goto block_1014;
}
else
{
lean_object* x_1028; uint8_t x_1029; 
x_1028 = lean_box(0);
x_1029 = lean_nat_dec_le(x_1026, x_1026);
if (x_1029 == 0)
{
if (x_1027 == 0)
{
lean_dec(x_3);
x_1009 = lean_box(0);
goto block_1014;
}
else
{
size_t x_1030; size_t x_1031; lean_object* x_1032; 
x_1030 = 0;
x_1031 = lean_usize_of_nat(x_1026);
x_1032 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1000, x_1030, x_1031, x_1028, x_3);
lean_dec(x_3);
x_1015 = x_1032;
goto block_1019;
}
}
else
{
size_t x_1033; size_t x_1034; lean_object* x_1035; 
x_1033 = 0;
x_1034 = lean_usize_of_nat(x_1026);
x_1035 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1000, x_1033, x_1034, x_1028, x_3);
lean_dec(x_3);
x_1015 = x_1035;
goto block_1019;
}
}
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
lean_dec(x_1001);
lean_dec(x_1000);
lean_dec(x_998);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1036 = lean_ctor_get(x_1024, 0);
lean_inc(x_1036);
if (lean_is_exclusive(x_1024)) {
 lean_ctor_release(x_1024, 0);
 x_1037 = x_1024;
} else {
 lean_dec_ref(x_1024);
 x_1037 = lean_box(0);
}
if (lean_is_scalar(x_1037)) {
 x_1038 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1038 = x_1037;
}
lean_ctor_set(x_1038, 0, x_1036);
return x_1038;
}
}
}
else
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
lean_dec(x_1001);
lean_dec(x_1000);
lean_dec(x_998);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1039 = lean_ctor_get(x_1020, 0);
lean_inc(x_1039);
if (lean_is_exclusive(x_1020)) {
 lean_ctor_release(x_1020, 0);
 x_1040 = x_1020;
} else {
 lean_dec_ref(x_1020);
 x_1040 = lean_box(0);
}
if (lean_is_scalar(x_1040)) {
 x_1041 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1041 = x_1040;
}
lean_ctor_set(x_1041, 0, x_1039);
return x_1041;
}
block_1008:
{
if (x_1003 == 0)
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1004 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1004 = lean_box(0);
}
if (lean_is_scalar(x_1004)) {
 x_1005 = lean_alloc_ctor(3, 2, 0);
} else {
 x_1005 = x_1004;
}
lean_ctor_set(x_1005, 0, x_998);
lean_ctor_set(x_1005, 1, x_1000);
if (lean_is_scalar(x_1001)) {
 x_1006 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1006 = x_1001;
}
lean_ctor_set(x_1006, 0, x_1005);
return x_1006;
}
else
{
lean_object* x_1007; 
lean_dec(x_1000);
lean_dec(x_998);
if (lean_is_scalar(x_1001)) {
 x_1007 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1007 = x_1001;
}
lean_ctor_set(x_1007, 0, x_1);
return x_1007;
}
}
block_1014:
{
uint8_t x_1010; 
x_1010 = l_Lean_instBEqFVarId_beq(x_993, x_998);
if (x_1010 == 0)
{
x_1002 = lean_box(0);
x_1003 = x_1010;
goto block_1008;
}
else
{
size_t x_1011; size_t x_1012; uint8_t x_1013; 
x_1011 = lean_ptr_addr(x_994);
x_1012 = lean_ptr_addr(x_1000);
x_1013 = lean_usize_dec_eq(x_1011, x_1012);
x_1002 = lean_box(0);
x_1003 = x_1013;
goto block_1008;
}
}
block_1019:
{
if (lean_obj_tag(x_1015) == 0)
{
lean_dec_ref(x_1015);
x_1009 = lean_box(0);
goto block_1014;
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
lean_dec(x_1001);
lean_dec(x_1000);
lean_dec(x_998);
lean_dec_ref(x_1);
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
if (lean_is_exclusive(x_1015)) {
 lean_ctor_release(x_1015, 0);
 x_1017 = x_1015;
} else {
 lean_dec_ref(x_1015);
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
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
lean_dec(x_998);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1042 = lean_ctor_get(x_999, 0);
lean_inc(x_1042);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 x_1043 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1043 = lean_box(0);
}
if (lean_is_scalar(x_1043)) {
 x_1044 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1044 = x_1043;
}
lean_ctor_set(x_1044, 0, x_1042);
return x_1044;
}
}
else
{
lean_object* x_1045; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1045 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1045;
}
}
case 4:
{
lean_object* x_1046; lean_object* x_1047; 
x_1046 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1046);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1046);
x_1047 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1046, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1047) == 0)
{
lean_object* x_1048; lean_object* x_1049; 
x_1048 = lean_ctor_get(x_1047, 0);
lean_inc(x_1048);
if (lean_is_exclusive(x_1047)) {
 lean_ctor_release(x_1047, 0);
 x_1049 = x_1047;
} else {
 lean_dec_ref(x_1047);
 x_1049 = lean_box(0);
}
if (lean_obj_tag(x_1048) == 1)
{
lean_object* x_1050; lean_object* x_1051; 
lean_dec_ref(x_1046);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1050 = lean_ctor_get(x_1048, 0);
lean_inc(x_1050);
lean_dec_ref(x_1048);
if (lean_is_scalar(x_1049)) {
 x_1051 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1051 = x_1049;
}
lean_ctor_set(x_1051, 0, x_1050);
return x_1051;
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
lean_dec(x_1048);
x_1052 = lean_ctor_get(x_1046, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1046, 1);
lean_inc_ref(x_1053);
x_1054 = lean_ctor_get(x_1046, 2);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1046, 3);
lean_inc_ref(x_1055);
if (lean_is_exclusive(x_1046)) {
 lean_ctor_release(x_1046, 0);
 lean_ctor_release(x_1046, 1);
 lean_ctor_release(x_1046, 2);
 lean_ctor_release(x_1046, 3);
 x_1056 = x_1046;
} else {
 lean_dec_ref(x_1046);
 x_1056 = lean_box(0);
}
x_1057 = lean_st_ref_get(x_3);
x_1058 = lean_ctor_get(x_1057, 0);
lean_inc_ref(x_1058);
lean_dec(x_1057);
lean_inc(x_1054);
x_1059 = l_Lean_Compiler_LCNF_normFVarImp(x_1058, x_1054, x_122);
lean_dec_ref(x_1058);
if (lean_obj_tag(x_1059) == 0)
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
x_1060 = lean_ctor_get(x_1059, 0);
lean_inc(x_1060);
if (lean_is_exclusive(x_1059)) {
 lean_ctor_release(x_1059, 0);
 x_1061 = x_1059;
} else {
 lean_dec_ref(x_1059);
 x_1061 = lean_box(0);
}
x_1062 = lean_st_ref_get(x_3);
x_1063 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1055);
lean_inc(x_1060);
x_1064 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_1060, x_122, x_1063, x_1055, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1064) == 0)
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
x_1065 = lean_ctor_get(x_1064, 0);
lean_inc(x_1065);
if (lean_is_exclusive(x_1064)) {
 lean_ctor_release(x_1064, 0);
 x_1066 = x_1064;
} else {
 lean_dec_ref(x_1064);
 x_1066 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_1067 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1065, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1067) == 0)
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1082; lean_object* x_1083; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1105; lean_object* x_1110; uint8_t x_1111; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1137; uint8_t x_1138; 
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
if (lean_is_exclusive(x_1067)) {
 lean_ctor_release(x_1067, 0);
 x_1069 = x_1067;
} else {
 lean_dec_ref(x_1067);
 x_1069 = lean_box(0);
}
x_1070 = lean_ctor_get(x_1062, 0);
lean_inc_ref(x_1070);
lean_dec(x_1062);
lean_inc_ref(x_1053);
x_1071 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1070, x_122, x_1053);
lean_dec_ref(x_1070);
x_1137 = lean_array_get_size(x_1068);
x_1138 = lean_nat_dec_eq(x_1137, x_810);
if (x_1138 == 0)
{
lean_dec(x_1049);
x_1115 = x_3;
x_1116 = x_5;
x_1117 = x_6;
x_1118 = x_7;
x_1119 = x_8;
x_1120 = lean_box(0);
goto block_1136;
}
else
{
lean_object* x_1139; 
x_1139 = lean_array_fget_borrowed(x_1068, x_1063);
if (lean_obj_tag(x_1139) == 0)
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1150; lean_object* x_1155; lean_object* x_1156; uint8_t x_1167; lean_object* x_1168; uint8_t x_1170; 
lean_dec(x_1049);
x_1140 = lean_ctor_get(x_1139, 1);
x_1141 = lean_ctor_get(x_1139, 2);
x_1155 = lean_array_get_size(x_1140);
x_1170 = lean_nat_dec_lt(x_1063, x_1155);
if (x_1170 == 0)
{
x_1167 = x_122;
x_1168 = lean_box(0);
goto block_1169;
}
else
{
if (x_1170 == 0)
{
x_1167 = x_122;
x_1168 = lean_box(0);
goto block_1169;
}
else
{
size_t x_1171; size_t x_1172; lean_object* x_1173; 
x_1171 = 0;
x_1172 = lean_usize_of_nat(x_1155);
x_1173 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_1140, x_1171, x_1172, x_3);
if (lean_obj_tag(x_1173) == 0)
{
lean_object* x_1174; uint8_t x_1175; 
x_1174 = lean_ctor_get(x_1173, 0);
lean_inc(x_1174);
lean_dec_ref(x_1173);
x_1175 = lean_unbox(x_1174);
lean_dec(x_1174);
x_1167 = x_1175;
x_1168 = lean_box(0);
goto block_1169;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
lean_dec_ref(x_1071);
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1066);
lean_dec(x_1061);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1176 = lean_ctor_get(x_1173, 0);
lean_inc(x_1176);
if (lean_is_exclusive(x_1173)) {
 lean_ctor_release(x_1173, 0);
 x_1177 = x_1173;
} else {
 lean_dec_ref(x_1173);
 x_1177 = lean_box(0);
}
if (lean_is_scalar(x_1177)) {
 x_1178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1178 = x_1177;
}
lean_ctor_set(x_1178, 0, x_1176);
return x_1178;
}
}
}
block_1149:
{
lean_object* x_1143; 
x_1143 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1143) == 0)
{
lean_object* x_1144; lean_object* x_1145; 
if (lean_is_exclusive(x_1143)) {
 lean_ctor_release(x_1143, 0);
 x_1144 = x_1143;
} else {
 lean_dec_ref(x_1143);
 x_1144 = lean_box(0);
}
if (lean_is_scalar(x_1144)) {
 x_1145 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1145 = x_1144;
}
lean_ctor_set(x_1145, 0, x_1141);
return x_1145;
}
else
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
lean_dec_ref(x_1141);
x_1146 = lean_ctor_get(x_1143, 0);
lean_inc(x_1146);
if (lean_is_exclusive(x_1143)) {
 lean_ctor_release(x_1143, 0);
 x_1147 = x_1143;
} else {
 lean_dec_ref(x_1143);
 x_1147 = lean_box(0);
}
if (lean_is_scalar(x_1147)) {
 x_1148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1148 = x_1147;
}
lean_ctor_set(x_1148, 0, x_1146);
return x_1148;
}
}
block_1154:
{
if (lean_obj_tag(x_1150) == 0)
{
lean_dec_ref(x_1150);
x_1142 = lean_box(0);
goto block_1149;
}
else
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; 
lean_dec_ref(x_1141);
lean_dec(x_3);
x_1151 = lean_ctor_get(x_1150, 0);
lean_inc(x_1151);
if (lean_is_exclusive(x_1150)) {
 lean_ctor_release(x_1150, 0);
 x_1152 = x_1150;
} else {
 lean_dec_ref(x_1150);
 x_1152 = lean_box(0);
}
if (lean_is_scalar(x_1152)) {
 x_1153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1153 = x_1152;
}
lean_ctor_set(x_1153, 0, x_1151);
return x_1153;
}
}
block_1166:
{
uint8_t x_1157; 
x_1157 = lean_nat_dec_lt(x_1063, x_1155);
if (x_1157 == 0)
{
lean_dec_ref(x_1140);
lean_dec(x_6);
x_1142 = lean_box(0);
goto block_1149;
}
else
{
lean_object* x_1158; uint8_t x_1159; 
x_1158 = lean_box(0);
x_1159 = lean_nat_dec_le(x_1155, x_1155);
if (x_1159 == 0)
{
if (x_1157 == 0)
{
lean_dec_ref(x_1140);
lean_dec(x_6);
x_1142 = lean_box(0);
goto block_1149;
}
else
{
size_t x_1160; size_t x_1161; lean_object* x_1162; 
x_1160 = 0;
x_1161 = lean_usize_of_nat(x_1155);
x_1162 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1140, x_1160, x_1161, x_1158, x_6);
lean_dec(x_6);
lean_dec_ref(x_1140);
x_1150 = x_1162;
goto block_1154;
}
}
else
{
size_t x_1163; size_t x_1164; lean_object* x_1165; 
x_1163 = 0;
x_1164 = lean_usize_of_nat(x_1155);
x_1165 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1140, x_1163, x_1164, x_1158, x_6);
lean_dec(x_6);
lean_dec_ref(x_1140);
x_1150 = x_1165;
goto block_1154;
}
}
}
block_1169:
{
if (x_1167 == 0)
{
lean_inc_ref(x_1141);
lean_inc_ref(x_1140);
lean_dec_ref(x_1071);
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1066);
lean_dec(x_1061);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1156 = lean_box(0);
goto block_1166;
}
else
{
if (x_122 == 0)
{
x_1115 = x_3;
x_1116 = x_5;
x_1117 = x_6;
x_1118 = x_7;
x_1119 = x_8;
x_1120 = lean_box(0);
goto block_1136;
}
else
{
lean_inc_ref(x_1141);
lean_inc_ref(x_1140);
lean_dec_ref(x_1071);
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1066);
lean_dec(x_1061);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1156 = lean_box(0);
goto block_1166;
}
}
}
}
else
{
lean_object* x_1179; lean_object* x_1180; 
lean_inc_ref(x_1139);
lean_dec_ref(x_1071);
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1066);
lean_dec(x_1061);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1179 = lean_ctor_get(x_1139, 0);
lean_inc_ref(x_1179);
lean_dec_ref(x_1139);
if (lean_is_scalar(x_1049)) {
 x_1180 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1180 = x_1049;
}
lean_ctor_set(x_1180, 0, x_1179);
return x_1180;
}
}
block_1081:
{
lean_object* x_1074; 
x_1074 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1072);
lean_dec(x_1072);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 x_1075 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1075 = lean_box(0);
}
if (lean_is_scalar(x_1061)) {
 x_1076 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1076 = x_1061;
 lean_ctor_set_tag(x_1076, 6);
}
lean_ctor_set(x_1076, 0, x_1071);
if (lean_is_scalar(x_1075)) {
 x_1077 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1077 = x_1075;
}
lean_ctor_set(x_1077, 0, x_1076);
return x_1077;
}
else
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
lean_dec_ref(x_1071);
lean_dec(x_1061);
x_1078 = lean_ctor_get(x_1074, 0);
lean_inc(x_1078);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 x_1079 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1079 = lean_box(0);
}
if (lean_is_scalar(x_1079)) {
 x_1080 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1080 = x_1079;
}
lean_ctor_set(x_1080, 0, x_1078);
return x_1080;
}
}
block_1087:
{
if (lean_obj_tag(x_1083) == 0)
{
lean_dec_ref(x_1083);
x_1072 = x_1082;
x_1073 = lean_box(0);
goto block_1081;
}
else
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
lean_dec(x_1082);
lean_dec_ref(x_1071);
lean_dec(x_1061);
x_1084 = lean_ctor_get(x_1083, 0);
lean_inc(x_1084);
if (lean_is_exclusive(x_1083)) {
 lean_ctor_release(x_1083, 0);
 x_1085 = x_1083;
} else {
 lean_dec_ref(x_1083);
 x_1085 = lean_box(0);
}
if (lean_is_scalar(x_1085)) {
 x_1086 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1086 = x_1085;
}
lean_ctor_set(x_1086, 0, x_1084);
return x_1086;
}
}
block_1104:
{
uint8_t x_1095; 
x_1095 = lean_nat_dec_lt(x_1063, x_1094);
if (x_1095 == 0)
{
lean_dec(x_1094);
lean_dec_ref(x_1093);
lean_dec(x_1090);
lean_dec_ref(x_1089);
lean_dec(x_1088);
lean_dec(x_1068);
x_1072 = x_1092;
x_1073 = lean_box(0);
goto block_1081;
}
else
{
lean_object* x_1096; uint8_t x_1097; 
x_1096 = lean_box(0);
x_1097 = lean_nat_dec_le(x_1094, x_1094);
if (x_1097 == 0)
{
if (x_1095 == 0)
{
lean_dec(x_1094);
lean_dec_ref(x_1093);
lean_dec(x_1090);
lean_dec_ref(x_1089);
lean_dec(x_1088);
lean_dec(x_1068);
x_1072 = x_1092;
x_1073 = lean_box(0);
goto block_1081;
}
else
{
size_t x_1098; size_t x_1099; lean_object* x_1100; 
x_1098 = 0;
x_1099 = lean_usize_of_nat(x_1094);
lean_dec(x_1094);
x_1100 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1063, x_1068, x_1098, x_1099, x_1096, x_1089, x_1088, x_1093, x_1090);
lean_dec(x_1090);
lean_dec_ref(x_1093);
lean_dec(x_1088);
lean_dec_ref(x_1089);
lean_dec(x_1068);
x_1082 = x_1092;
x_1083 = x_1100;
goto block_1087;
}
}
else
{
size_t x_1101; size_t x_1102; lean_object* x_1103; 
x_1101 = 0;
x_1102 = lean_usize_of_nat(x_1094);
lean_dec(x_1094);
x_1103 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1063, x_1068, x_1101, x_1102, x_1096, x_1089, x_1088, x_1093, x_1090);
lean_dec(x_1090);
lean_dec_ref(x_1093);
lean_dec(x_1088);
lean_dec_ref(x_1089);
lean_dec(x_1068);
x_1082 = x_1092;
x_1083 = x_1103;
goto block_1087;
}
}
}
block_1109:
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
if (lean_is_scalar(x_1056)) {
 x_1106 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1106 = x_1056;
}
lean_ctor_set(x_1106, 0, x_1052);
lean_ctor_set(x_1106, 1, x_1071);
lean_ctor_set(x_1106, 2, x_1060);
lean_ctor_set(x_1106, 3, x_1068);
x_1107 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1107, 0, x_1106);
if (lean_is_scalar(x_1069)) {
 x_1108 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1108 = x_1069;
}
lean_ctor_set(x_1108, 0, x_1107);
return x_1108;
}
block_1114:
{
if (x_1111 == 0)
{
lean_dec(x_1066);
lean_dec(x_1054);
lean_dec_ref(x_1);
x_1105 = lean_box(0);
goto block_1109;
}
else
{
uint8_t x_1112; 
x_1112 = l_Lean_instBEqFVarId_beq(x_1054, x_1060);
lean_dec(x_1054);
if (x_1112 == 0)
{
lean_dec(x_1066);
lean_dec_ref(x_1);
x_1105 = lean_box(0);
goto block_1109;
}
else
{
lean_object* x_1113; 
lean_dec_ref(x_1071);
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec(x_1052);
if (lean_is_scalar(x_1066)) {
 x_1113 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1113 = x_1066;
}
lean_ctor_set(x_1113, 0, x_1);
return x_1113;
}
}
}
block_1136:
{
lean_object* x_1121; uint8_t x_1122; 
x_1121 = lean_array_get_size(x_1068);
x_1122 = lean_nat_dec_lt(x_1063, x_1121);
if (x_1122 == 0)
{
lean_dec(x_1069);
lean_dec(x_1066);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec_ref(x_1);
x_1088 = x_1117;
x_1089 = x_1116;
x_1090 = x_1119;
x_1091 = lean_box(0);
x_1092 = x_1115;
x_1093 = x_1118;
x_1094 = x_1121;
goto block_1104;
}
else
{
if (x_1122 == 0)
{
lean_dec(x_1069);
lean_dec(x_1066);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec_ref(x_1);
x_1088 = x_1117;
x_1089 = x_1116;
x_1090 = x_1119;
x_1091 = lean_box(0);
x_1092 = x_1115;
x_1093 = x_1118;
x_1094 = x_1121;
goto block_1104;
}
else
{
size_t x_1123; size_t x_1124; uint8_t x_1125; 
x_1123 = 0;
x_1124 = lean_usize_of_nat(x_1121);
x_1125 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_122, x_1068, x_1123, x_1124);
if (x_1125 == 0)
{
lean_dec(x_1069);
lean_dec(x_1066);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec_ref(x_1);
x_1088 = x_1117;
x_1089 = x_1116;
x_1090 = x_1119;
x_1091 = lean_box(0);
x_1092 = x_1115;
x_1093 = x_1118;
x_1094 = x_1121;
goto block_1104;
}
else
{
if (x_122 == 0)
{
lean_object* x_1126; 
lean_dec(x_1119);
lean_dec_ref(x_1118);
lean_dec(x_1117);
lean_dec_ref(x_1116);
lean_dec(x_1061);
lean_inc(x_1060);
x_1126 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1060, x_1115);
lean_dec(x_1115);
if (lean_obj_tag(x_1126) == 0)
{
size_t x_1127; size_t x_1128; uint8_t x_1129; 
lean_dec_ref(x_1126);
x_1127 = lean_ptr_addr(x_1055);
lean_dec_ref(x_1055);
x_1128 = lean_ptr_addr(x_1068);
x_1129 = lean_usize_dec_eq(x_1127, x_1128);
if (x_1129 == 0)
{
lean_dec_ref(x_1053);
x_1110 = lean_box(0);
x_1111 = x_1129;
goto block_1114;
}
else
{
size_t x_1130; size_t x_1131; uint8_t x_1132; 
x_1130 = lean_ptr_addr(x_1053);
lean_dec_ref(x_1053);
x_1131 = lean_ptr_addr(x_1071);
x_1132 = lean_usize_dec_eq(x_1130, x_1131);
x_1110 = lean_box(0);
x_1111 = x_1132;
goto block_1114;
}
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
lean_dec_ref(x_1071);
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1066);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec_ref(x_1);
x_1133 = lean_ctor_get(x_1126, 0);
lean_inc(x_1133);
if (lean_is_exclusive(x_1126)) {
 lean_ctor_release(x_1126, 0);
 x_1134 = x_1126;
} else {
 lean_dec_ref(x_1126);
 x_1134 = lean_box(0);
}
if (lean_is_scalar(x_1134)) {
 x_1135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1135 = x_1134;
}
lean_ctor_set(x_1135, 0, x_1133);
return x_1135;
}
}
else
{
lean_dec(x_1069);
lean_dec(x_1066);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec_ref(x_1);
x_1088 = x_1117;
x_1089 = x_1116;
x_1090 = x_1119;
x_1091 = lean_box(0);
x_1092 = x_1115;
x_1093 = x_1118;
x_1094 = x_1121;
goto block_1104;
}
}
}
}
}
}
else
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
lean_dec(x_1066);
lean_dec(x_1062);
lean_dec(x_1061);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec(x_1049);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1181 = lean_ctor_get(x_1067, 0);
lean_inc(x_1181);
if (lean_is_exclusive(x_1067)) {
 lean_ctor_release(x_1067, 0);
 x_1182 = x_1067;
} else {
 lean_dec_ref(x_1067);
 x_1182 = lean_box(0);
}
if (lean_is_scalar(x_1182)) {
 x_1183 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1183 = x_1182;
}
lean_ctor_set(x_1183, 0, x_1181);
return x_1183;
}
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
lean_dec(x_1062);
lean_dec(x_1061);
lean_dec(x_1060);
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec(x_1049);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1184 = lean_ctor_get(x_1064, 0);
lean_inc(x_1184);
if (lean_is_exclusive(x_1064)) {
 lean_ctor_release(x_1064, 0);
 x_1185 = x_1064;
} else {
 lean_dec_ref(x_1064);
 x_1185 = lean_box(0);
}
if (lean_is_scalar(x_1185)) {
 x_1186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1186 = x_1185;
}
lean_ctor_set(x_1186, 0, x_1184);
return x_1186;
}
}
else
{
lean_object* x_1187; 
lean_dec(x_1056);
lean_dec_ref(x_1055);
lean_dec(x_1054);
lean_dec_ref(x_1053);
lean_dec(x_1052);
lean_dec(x_1049);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1187 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1187;
}
}
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
lean_dec_ref(x_1046);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1188 = lean_ctor_get(x_1047, 0);
lean_inc(x_1188);
if (lean_is_exclusive(x_1047)) {
 lean_ctor_release(x_1047, 0);
 x_1189 = x_1047;
} else {
 lean_dec_ref(x_1047);
 x_1189 = lean_box(0);
}
if (lean_is_scalar(x_1189)) {
 x_1190 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1190 = x_1189;
}
lean_ctor_set(x_1190, 0, x_1188);
return x_1190;
}
}
case 5:
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1191 = lean_ctor_get(x_1, 0);
x_1192 = lean_st_ref_get(x_3);
x_1193 = lean_ctor_get(x_1192, 0);
lean_inc_ref(x_1193);
lean_dec(x_1192);
lean_inc(x_1191);
x_1194 = l_Lean_Compiler_LCNF_normFVarImp(x_1193, x_1191, x_122);
lean_dec_ref(x_1193);
if (lean_obj_tag(x_1194) == 0)
{
lean_object* x_1195; lean_object* x_1196; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1195 = lean_ctor_get(x_1194, 0);
lean_inc(x_1195);
lean_dec_ref(x_1194);
lean_inc(x_1195);
x_1196 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1195, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1196) == 0)
{
lean_object* x_1197; uint8_t x_1198; 
if (lean_is_exclusive(x_1196)) {
 lean_ctor_release(x_1196, 0);
 x_1197 = x_1196;
} else {
 lean_dec_ref(x_1196);
 x_1197 = lean_box(0);
}
x_1198 = l_Lean_instBEqFVarId_beq(x_1191, x_1195);
if (x_1198 == 0)
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1199 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1199 = lean_box(0);
}
if (lean_is_scalar(x_1199)) {
 x_1200 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1200 = x_1199;
}
lean_ctor_set(x_1200, 0, x_1195);
if (lean_is_scalar(x_1197)) {
 x_1201 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1201 = x_1197;
}
lean_ctor_set(x_1201, 0, x_1200);
return x_1201;
}
else
{
lean_object* x_1202; 
lean_dec(x_1195);
if (lean_is_scalar(x_1197)) {
 x_1202 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1202 = x_1197;
}
lean_ctor_set(x_1202, 0, x_1);
return x_1202;
}
}
else
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
lean_dec(x_1195);
lean_dec_ref(x_1);
x_1203 = lean_ctor_get(x_1196, 0);
lean_inc(x_1203);
if (lean_is_exclusive(x_1196)) {
 lean_ctor_release(x_1196, 0);
 x_1204 = x_1196;
} else {
 lean_dec_ref(x_1196);
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
else
{
lean_object* x_1206; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1206 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1206;
}
}
case 6:
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; size_t x_1211; size_t x_1212; uint8_t x_1213; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1207 = lean_ctor_get(x_1, 0);
x_1208 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_1209 = lean_ctor_get(x_1208, 0);
lean_inc_ref(x_1209);
lean_dec(x_1208);
lean_inc_ref(x_1207);
x_1210 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1209, x_122, x_1207);
lean_dec_ref(x_1209);
x_1211 = lean_ptr_addr(x_1207);
x_1212 = lean_ptr_addr(x_1210);
x_1213 = lean_usize_dec_eq(x_1211, x_1212);
if (x_1213 == 0)
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1214 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1214 = lean_box(0);
}
if (lean_is_scalar(x_1214)) {
 x_1215 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1215 = x_1214;
}
lean_ctor_set(x_1215, 0, x_1210);
x_1216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1216, 0, x_1215);
return x_1216;
}
else
{
lean_object* x_1217; 
lean_dec_ref(x_1210);
x_1217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1217, 0, x_1);
return x_1217;
}
}
default: 
{
lean_object* x_1218; lean_object* x_1219; 
x_1218 = lean_ctor_get(x_1, 0);
x_1219 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1219);
lean_inc_ref(x_1218);
x_762 = x_1218;
x_763 = x_1219;
x_764 = x_2;
x_765 = x_3;
x_766 = x_4;
x_767 = x_5;
x_768 = x_6;
x_769 = x_7;
x_770 = x_8;
goto block_809;
}
}
block_809:
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_771 = lean_ctor_get(x_762, 0);
x_772 = lean_ctor_get(x_762, 2);
x_773 = lean_ctor_get(x_762, 3);
x_774 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_771, x_765);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; uint8_t x_776; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
lean_dec_ref(x_774);
x_776 = lean_unbox(x_775);
if (x_776 == 0)
{
uint8_t x_777; 
x_777 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
if (x_777 == 0)
{
uint8_t x_778; 
x_778 = lean_unbox(x_775);
lean_dec(x_775);
x_81 = x_778;
x_82 = x_763;
x_83 = x_762;
x_84 = x_764;
x_85 = x_765;
x_86 = x_766;
x_87 = x_767;
x_88 = x_768;
x_89 = x_769;
x_90 = x_770;
x_91 = lean_box(0);
goto block_97;
}
else
{
uint8_t x_779; 
lean_inc_ref(x_773);
x_779 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_773, x_772);
if (x_779 == 0)
{
uint8_t x_780; 
x_780 = lean_unbox(x_775);
lean_dec(x_775);
x_81 = x_780;
x_82 = x_763;
x_83 = x_762;
x_84 = x_764;
x_85 = x_765;
x_86 = x_766;
x_87 = x_767;
x_88 = x_768;
x_89 = x_769;
x_90 = x_770;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_781 = lean_st_ref_get(x_765);
x_782 = lean_ctor_get(x_781, 0);
lean_inc_ref(x_782);
lean_dec(x_781);
x_783 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_762, x_782, x_767, x_768, x_769, x_770);
lean_dec_ref(x_782);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; lean_object* x_785; 
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
lean_dec_ref(x_783);
lean_inc(x_770);
lean_inc_ref(x_769);
lean_inc(x_768);
lean_inc_ref(x_767);
x_785 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_784, x_767, x_768, x_769, x_770);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; lean_object* x_787; 
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
lean_dec_ref(x_785);
x_787 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_765);
if (lean_obj_tag(x_787) == 0)
{
uint8_t x_788; 
lean_dec_ref(x_787);
x_788 = lean_unbox(x_775);
lean_dec(x_775);
x_81 = x_788;
x_82 = x_763;
x_83 = x_786;
x_84 = x_764;
x_85 = x_765;
x_86 = x_766;
x_87 = x_767;
x_88 = x_768;
x_89 = x_769;
x_90 = x_770;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
lean_dec(x_786);
lean_dec(x_775);
lean_dec(x_770);
lean_dec_ref(x_769);
lean_dec(x_768);
lean_dec_ref(x_767);
lean_dec_ref(x_766);
lean_dec(x_765);
lean_dec_ref(x_764);
lean_dec_ref(x_763);
lean_dec_ref(x_1);
x_789 = lean_ctor_get(x_787, 0);
lean_inc(x_789);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 x_790 = x_787;
} else {
 lean_dec_ref(x_787);
 x_790 = lean_box(0);
}
if (lean_is_scalar(x_790)) {
 x_791 = lean_alloc_ctor(1, 1, 0);
} else {
 x_791 = x_790;
}
lean_ctor_set(x_791, 0, x_789);
return x_791;
}
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_775);
lean_dec(x_770);
lean_dec_ref(x_769);
lean_dec(x_768);
lean_dec_ref(x_767);
lean_dec_ref(x_766);
lean_dec(x_765);
lean_dec_ref(x_764);
lean_dec_ref(x_763);
lean_dec_ref(x_1);
x_792 = lean_ctor_get(x_785, 0);
lean_inc(x_792);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 x_793 = x_785;
} else {
 lean_dec_ref(x_785);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 1, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_792);
return x_794;
}
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; 
lean_dec(x_775);
lean_dec(x_770);
lean_dec_ref(x_769);
lean_dec(x_768);
lean_dec_ref(x_767);
lean_dec_ref(x_766);
lean_dec(x_765);
lean_dec_ref(x_764);
lean_dec_ref(x_763);
lean_dec_ref(x_1);
x_795 = lean_ctor_get(x_783, 0);
lean_inc(x_795);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 x_796 = x_783;
} else {
 lean_dec_ref(x_783);
 x_796 = lean_box(0);
}
if (lean_is_scalar(x_796)) {
 x_797 = lean_alloc_ctor(1, 1, 0);
} else {
 x_797 = x_796;
}
lean_ctor_set(x_797, 0, x_795);
return x_797;
}
}
}
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; 
x_798 = lean_st_ref_get(x_765);
x_799 = lean_ctor_get(x_798, 0);
lean_inc_ref(x_799);
lean_dec(x_798);
x_800 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_762, x_799, x_767, x_768, x_769, x_770);
lean_dec_ref(x_799);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_801; uint8_t x_802; 
x_801 = lean_ctor_get(x_800, 0);
lean_inc(x_801);
lean_dec_ref(x_800);
x_802 = lean_unbox(x_775);
lean_dec(x_775);
x_49 = x_802;
x_50 = x_763;
x_51 = x_801;
x_52 = x_764;
x_53 = x_765;
x_54 = x_766;
x_55 = x_767;
x_56 = x_768;
x_57 = x_769;
x_58 = x_770;
x_59 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_775);
lean_dec(x_770);
lean_dec_ref(x_769);
lean_dec(x_768);
lean_dec_ref(x_767);
lean_dec_ref(x_766);
lean_dec(x_765);
lean_dec_ref(x_764);
lean_dec_ref(x_763);
lean_dec_ref(x_1);
x_803 = lean_ctor_get(x_800, 0);
lean_inc(x_803);
if (lean_is_exclusive(x_800)) {
 lean_ctor_release(x_800, 0);
 x_804 = x_800;
} else {
 lean_dec_ref(x_800);
 x_804 = lean_box(0);
}
if (lean_is_scalar(x_804)) {
 x_805 = lean_alloc_ctor(1, 1, 0);
} else {
 x_805 = x_804;
}
lean_ctor_set(x_805, 0, x_803);
return x_805;
}
}
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
lean_dec(x_770);
lean_dec_ref(x_769);
lean_dec(x_768);
lean_dec_ref(x_767);
lean_dec_ref(x_766);
lean_dec(x_765);
lean_dec_ref(x_764);
lean_dec_ref(x_763);
lean_dec_ref(x_762);
lean_dec_ref(x_1);
x_806 = lean_ctor_get(x_774, 0);
lean_inc(x_806);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_807 = x_774;
} else {
 lean_dec_ref(x_774);
 x_807 = lean_box(0);
}
if (lean_is_scalar(x_807)) {
 x_808 = lean_alloc_ctor(1, 1, 0);
} else {
 x_808 = x_807;
}
lean_ctor_set(x_808, 0, x_806);
return x_808;
}
}
}
}
else
{
uint8_t x_1220; 
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
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1220 = !lean_is_exclusive(x_138);
if (x_1220 == 0)
{
return x_138;
}
else
{
lean_object* x_1221; lean_object* x_1222; 
x_1221 = lean_ctor_get(x_138, 0);
lean_inc(x_1221);
lean_dec(x_138);
x_1222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1222, 0, x_1221);
return x_1222;
}
}
}
else
{
lean_object* x_1223; 
lean_dec(x_7);
x_1223 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3);
if (lean_obj_tag(x_1223) == 0)
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; 
if (lean_is_exclusive(x_1223)) {
 lean_ctor_release(x_1223, 0);
 x_1224 = x_1223;
} else {
 lean_dec_ref(x_1223);
 x_1224 = lean_box(0);
}
x_1273 = lean_unsigned_to_nat(1u);
x_1274 = lean_nat_add(x_109, x_1273);
lean_dec(x_109);
x_1275 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_1275, 0, x_106);
lean_ctor_set(x_1275, 1, x_107);
lean_ctor_set(x_1275, 2, x_108);
lean_ctor_set(x_1275, 3, x_1274);
lean_ctor_set(x_1275, 4, x_110);
lean_ctor_set(x_1275, 5, x_111);
lean_ctor_set(x_1275, 6, x_112);
lean_ctor_set(x_1275, 7, x_113);
lean_ctor_set(x_1275, 8, x_114);
lean_ctor_set(x_1275, 9, x_115);
lean_ctor_set(x_1275, 10, x_116);
lean_ctor_set(x_1275, 11, x_117);
lean_ctor_set(x_1275, 12, x_119);
lean_ctor_set(x_1275, 13, x_121);
lean_ctor_set_uint8(x_1275, sizeof(void*)*14, x_118);
lean_ctor_set_uint8(x_1275, sizeof(void*)*14 + 1, x_120);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; uint8_t x_1287; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1418; 
lean_dec(x_1224);
x_1276 = lean_ctor_get(x_1, 0);
x_1277 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1276);
x_1418 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_122, x_1276, x_3, x_6);
if (lean_obj_tag(x_1418) == 0)
{
lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; uint8_t x_1453; 
x_1419 = lean_ctor_get(x_1418, 0);
lean_inc(x_1419);
lean_dec_ref(x_1418);
x_1453 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_1276, x_1419);
if (x_1453 == 0)
{
goto block_1452;
}
else
{
if (x_122 == 0)
{
x_1420 = x_2;
x_1421 = x_3;
x_1422 = x_4;
x_1423 = x_5;
x_1424 = x_6;
x_1425 = x_1275;
x_1426 = x_8;
x_1427 = lean_box(0);
goto block_1447;
}
else
{
goto block_1452;
}
}
block_1447:
{
lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
x_1428 = lean_ctor_get(x_1419, 2);
x_1429 = lean_ctor_get(x_1419, 3);
lean_inc(x_1426);
lean_inc_ref(x_1425);
lean_inc(x_1424);
lean_inc_ref(x_1423);
lean_inc_ref(x_1422);
lean_inc(x_1429);
x_1430 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_1429, x_1420, x_1422, x_1423, x_1424, x_1425, x_1426);
if (lean_obj_tag(x_1430) == 0)
{
lean_object* x_1431; 
x_1431 = lean_ctor_get(x_1430, 0);
lean_inc(x_1431);
lean_dec_ref(x_1430);
if (lean_obj_tag(x_1431) == 1)
{
lean_object* x_1432; lean_object* x_1433; 
x_1432 = lean_ctor_get(x_1431, 0);
lean_inc(x_1432);
lean_dec_ref(x_1431);
x_1433 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1421);
if (lean_obj_tag(x_1433) == 0)
{
lean_object* x_1434; 
lean_dec_ref(x_1433);
x_1434 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_1419, x_1432, x_1424);
if (lean_obj_tag(x_1434) == 0)
{
lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; 
x_1435 = lean_ctor_get(x_1434, 0);
lean_inc(x_1435);
lean_dec_ref(x_1434);
x_1436 = lean_ctor_get(x_1435, 2);
lean_inc_ref(x_1436);
x_1437 = lean_ctor_get(x_1435, 3);
lean_inc(x_1437);
x_1403 = x_1435;
x_1404 = x_1436;
x_1405 = x_1437;
x_1406 = x_1420;
x_1407 = x_1421;
x_1408 = x_1422;
x_1409 = x_1423;
x_1410 = x_1424;
x_1411 = x_1425;
x_1412 = x_1426;
x_1413 = lean_box(0);
goto block_1417;
}
else
{
lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
lean_dec(x_1426);
lean_dec_ref(x_1425);
lean_dec(x_1424);
lean_dec_ref(x_1423);
lean_dec_ref(x_1422);
lean_dec(x_1421);
lean_dec_ref(x_1420);
lean_dec_ref(x_1);
x_1438 = lean_ctor_get(x_1434, 0);
lean_inc(x_1438);
if (lean_is_exclusive(x_1434)) {
 lean_ctor_release(x_1434, 0);
 x_1439 = x_1434;
} else {
 lean_dec_ref(x_1434);
 x_1439 = lean_box(0);
}
if (lean_is_scalar(x_1439)) {
 x_1440 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1440 = x_1439;
}
lean_ctor_set(x_1440, 0, x_1438);
return x_1440;
}
}
else
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; 
lean_dec(x_1432);
lean_dec(x_1426);
lean_dec_ref(x_1425);
lean_dec(x_1424);
lean_dec_ref(x_1423);
lean_dec_ref(x_1422);
lean_dec(x_1421);
lean_dec_ref(x_1420);
lean_dec(x_1419);
lean_dec_ref(x_1);
x_1441 = lean_ctor_get(x_1433, 0);
lean_inc(x_1441);
if (lean_is_exclusive(x_1433)) {
 lean_ctor_release(x_1433, 0);
 x_1442 = x_1433;
} else {
 lean_dec_ref(x_1433);
 x_1442 = lean_box(0);
}
if (lean_is_scalar(x_1442)) {
 x_1443 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1443 = x_1442;
}
lean_ctor_set(x_1443, 0, x_1441);
return x_1443;
}
}
else
{
lean_dec(x_1431);
lean_inc(x_1429);
lean_inc_ref(x_1428);
x_1403 = x_1419;
x_1404 = x_1428;
x_1405 = x_1429;
x_1406 = x_1420;
x_1407 = x_1421;
x_1408 = x_1422;
x_1409 = x_1423;
x_1410 = x_1424;
x_1411 = x_1425;
x_1412 = x_1426;
x_1413 = lean_box(0);
goto block_1417;
}
}
else
{
lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; 
lean_dec(x_1426);
lean_dec_ref(x_1425);
lean_dec(x_1424);
lean_dec_ref(x_1423);
lean_dec_ref(x_1422);
lean_dec(x_1421);
lean_dec_ref(x_1420);
lean_dec(x_1419);
lean_dec_ref(x_1);
x_1444 = lean_ctor_get(x_1430, 0);
lean_inc(x_1444);
if (lean_is_exclusive(x_1430)) {
 lean_ctor_release(x_1430, 0);
 x_1445 = x_1430;
} else {
 lean_dec_ref(x_1430);
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
block_1452:
{
lean_object* x_1448; 
x_1448 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_1448) == 0)
{
lean_dec_ref(x_1448);
x_1420 = x_2;
x_1421 = x_3;
x_1422 = x_4;
x_1423 = x_5;
x_1424 = x_6;
x_1425 = x_1275;
x_1426 = x_8;
x_1427 = lean_box(0);
goto block_1447;
}
else
{
lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
lean_dec(x_1419);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1449 = lean_ctor_get(x_1448, 0);
lean_inc(x_1449);
if (lean_is_exclusive(x_1448)) {
 lean_ctor_release(x_1448, 0);
 x_1450 = x_1448;
} else {
 lean_dec_ref(x_1448);
 x_1450 = lean_box(0);
}
if (lean_is_scalar(x_1450)) {
 x_1451 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1451 = x_1450;
}
lean_ctor_set(x_1451, 0, x_1449);
return x_1451;
}
}
}
else
{
lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; 
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1454 = lean_ctor_get(x_1418, 0);
lean_inc(x_1454);
if (lean_is_exclusive(x_1418)) {
 lean_ctor_release(x_1418, 0);
 x_1455 = x_1418;
} else {
 lean_dec_ref(x_1418);
 x_1455 = lean_box(0);
}
if (lean_is_scalar(x_1455)) {
 x_1456 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1456 = x_1455;
}
lean_ctor_set(x_1456, 0, x_1454);
return x_1456;
}
block_1402:
{
if (x_1287 == 0)
{
lean_object* x_1288; 
lean_inc(x_1286);
lean_inc_ref(x_1278);
lean_inc(x_1284);
lean_inc_ref(x_1281);
lean_inc_ref(x_1285);
x_1288 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_1285, x_1281, x_1284, x_1278, x_1286);
if (lean_obj_tag(x_1288) == 0)
{
lean_object* x_1289; 
x_1289 = lean_ctor_get(x_1288, 0);
lean_inc(x_1289);
lean_dec_ref(x_1288);
if (lean_obj_tag(x_1289) == 1)
{
lean_object* x_1290; lean_object* x_1291; 
lean_dec_ref(x_1285);
lean_inc_ref(x_1277);
lean_dec_ref(x_1);
x_1290 = lean_ctor_get(x_1289, 0);
lean_inc(x_1290);
lean_dec_ref(x_1289);
x_1291 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1280);
if (lean_obj_tag(x_1291) == 0)
{
lean_object* x_1292; 
lean_dec_ref(x_1291);
lean_inc(x_1286);
lean_inc_ref(x_1278);
lean_inc(x_1284);
lean_inc_ref(x_1281);
lean_inc_ref(x_1283);
lean_inc(x_1280);
lean_inc_ref(x_1279);
x_1292 = l_Lean_Compiler_LCNF_Simp_simp(x_1277, x_1279, x_1280, x_1283, x_1281, x_1284, x_1278, x_1286);
if (lean_obj_tag(x_1292) == 0)
{
lean_object* x_1293; lean_object* x_1294; 
x_1293 = lean_ctor_get(x_1292, 0);
lean_inc(x_1293);
lean_dec_ref(x_1292);
x_1294 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1290, x_1293, x_1279, x_1280, x_1283, x_1281, x_1284, x_1278, x_1286);
lean_dec(x_1286);
lean_dec_ref(x_1278);
lean_dec(x_1284);
lean_dec_ref(x_1281);
lean_dec_ref(x_1283);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec(x_1290);
return x_1294;
}
else
{
lean_dec(x_1290);
lean_dec(x_1286);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
return x_1292;
}
}
else
{
lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
lean_dec(x_1290);
lean_dec(x_1286);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1277);
x_1295 = lean_ctor_get(x_1291, 0);
lean_inc(x_1295);
if (lean_is_exclusive(x_1291)) {
 lean_ctor_release(x_1291, 0);
 x_1296 = x_1291;
} else {
 lean_dec_ref(x_1291);
 x_1296 = lean_box(0);
}
if (lean_is_scalar(x_1296)) {
 x_1297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1297 = x_1296;
}
lean_ctor_set(x_1297, 0, x_1295);
return x_1297;
}
}
else
{
lean_object* x_1298; 
lean_dec(x_1289);
lean_inc(x_1286);
lean_inc_ref(x_1278);
lean_inc(x_1284);
lean_inc_ref(x_1281);
lean_inc_ref(x_1285);
x_1298 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1285, x_1279, x_1280, x_1281, x_1284, x_1278, x_1286);
if (lean_obj_tag(x_1298) == 0)
{
lean_object* x_1299; 
x_1299 = lean_ctor_get(x_1298, 0);
lean_inc(x_1299);
lean_dec_ref(x_1298);
if (lean_obj_tag(x_1299) == 1)
{
lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
lean_dec_ref(x_1285);
lean_inc_ref(x_1277);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1300 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1300 = lean_box(0);
}
x_1301 = lean_ctor_get(x_1299, 0);
lean_inc(x_1301);
lean_dec_ref(x_1299);
if (lean_is_scalar(x_1300)) {
 x_1302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1302 = x_1300;
 lean_ctor_set_tag(x_1302, 1);
}
lean_ctor_set(x_1302, 0, x_1301);
lean_ctor_set(x_1302, 1, x_1277);
x_1 = x_1302;
x_2 = x_1279;
x_3 = x_1280;
x_4 = x_1283;
x_5 = x_1281;
x_6 = x_1284;
x_7 = x_1278;
x_8 = x_1286;
goto _start;
}
else
{
lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
lean_dec(x_1299);
x_1304 = lean_ctor_get(x_1285, 0);
x_1305 = lean_ctor_get(x_1285, 3);
x_1306 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1305);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; 
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
lean_dec_ref(x_1306);
if (lean_obj_tag(x_1307) == 1)
{
lean_object* x_1308; lean_object* x_1309; 
lean_inc_ref(x_1277);
lean_dec_ref(x_1);
x_1308 = lean_ctor_get(x_1307, 0);
lean_inc(x_1308);
lean_dec_ref(x_1307);
lean_inc(x_1304);
x_1309 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1304, x_1308, x_1280, x_1284, x_1278, x_1286);
if (lean_obj_tag(x_1309) == 0)
{
lean_object* x_1310; 
lean_dec_ref(x_1309);
x_1310 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1285, x_1280, x_1284);
lean_dec_ref(x_1285);
if (lean_obj_tag(x_1310) == 0)
{
lean_dec_ref(x_1310);
x_1 = x_1277;
x_2 = x_1279;
x_3 = x_1280;
x_4 = x_1283;
x_5 = x_1281;
x_6 = x_1284;
x_7 = x_1278;
x_8 = x_1286;
goto _start;
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
lean_dec(x_1286);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1277);
x_1312 = lean_ctor_get(x_1310, 0);
lean_inc(x_1312);
if (lean_is_exclusive(x_1310)) {
 lean_ctor_release(x_1310, 0);
 x_1313 = x_1310;
} else {
 lean_dec_ref(x_1310);
 x_1313 = lean_box(0);
}
if (lean_is_scalar(x_1313)) {
 x_1314 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1314 = x_1313;
}
lean_ctor_set(x_1314, 0, x_1312);
return x_1314;
}
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; 
lean_dec(x_1286);
lean_dec_ref(x_1285);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1277);
x_1315 = lean_ctor_get(x_1309, 0);
lean_inc(x_1315);
if (lean_is_exclusive(x_1309)) {
 lean_ctor_release(x_1309, 0);
 x_1316 = x_1309;
} else {
 lean_dec_ref(x_1309);
 x_1316 = lean_box(0);
}
if (lean_is_scalar(x_1316)) {
 x_1317 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1317 = x_1316;
}
lean_ctor_set(x_1317, 0, x_1315);
return x_1317;
}
}
else
{
lean_object* x_1318; 
lean_dec(x_1307);
lean_inc(x_1286);
lean_inc_ref(x_1278);
lean_inc(x_1284);
lean_inc_ref(x_1281);
lean_inc_ref(x_1283);
lean_inc(x_1280);
lean_inc_ref(x_1279);
lean_inc_ref(x_1277);
lean_inc_ref(x_1285);
x_1318 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1285, x_1277, x_1279, x_1280, x_1283, x_1281, x_1284, x_1278, x_1286);
if (lean_obj_tag(x_1318) == 0)
{
lean_object* x_1319; 
x_1319 = lean_ctor_get(x_1318, 0);
lean_inc(x_1319);
lean_dec_ref(x_1318);
if (lean_obj_tag(x_1319) == 1)
{
lean_object* x_1320; lean_object* x_1321; 
lean_dec(x_1286);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1);
x_1320 = lean_ctor_get(x_1319, 0);
lean_inc(x_1320);
lean_dec_ref(x_1319);
x_1321 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1285, x_1280, x_1284);
lean_dec(x_1284);
lean_dec(x_1280);
lean_dec_ref(x_1285);
if (lean_obj_tag(x_1321) == 0)
{
lean_object* x_1322; lean_object* x_1323; 
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 x_1322 = x_1321;
} else {
 lean_dec_ref(x_1321);
 x_1322 = lean_box(0);
}
if (lean_is_scalar(x_1322)) {
 x_1323 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1323 = x_1322;
}
lean_ctor_set(x_1323, 0, x_1320);
return x_1323;
}
else
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
lean_dec(x_1320);
x_1324 = lean_ctor_get(x_1321, 0);
lean_inc(x_1324);
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 x_1325 = x_1321;
} else {
 lean_dec_ref(x_1321);
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
else
{
lean_object* x_1327; 
lean_dec(x_1319);
lean_inc(x_1286);
lean_inc_ref(x_1278);
lean_inc(x_1284);
lean_inc_ref(x_1281);
lean_inc_ref(x_1283);
lean_inc(x_1280);
lean_inc_ref(x_1279);
lean_inc(x_1305);
x_1327 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_1305, x_1279, x_1280, x_1283, x_1281, x_1284, x_1278, x_1286);
if (lean_obj_tag(x_1327) == 0)
{
lean_object* x_1328; 
x_1328 = lean_ctor_get(x_1327, 0);
lean_inc(x_1328);
lean_dec_ref(x_1327);
if (lean_obj_tag(x_1328) == 1)
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; 
lean_inc_ref(x_1277);
lean_dec_ref(x_1);
x_1329 = lean_ctor_get(x_1328, 0);
lean_inc(x_1329);
lean_dec_ref(x_1328);
x_1330 = lean_ctor_get(x_1329, 0);
lean_inc(x_1330);
x_1331 = lean_ctor_get(x_1329, 1);
lean_inc(x_1331);
lean_dec(x_1329);
lean_inc(x_1304);
x_1332 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1304, x_1331, x_1280, x_1284, x_1278, x_1286);
if (lean_obj_tag(x_1332) == 0)
{
lean_object* x_1333; 
lean_dec_ref(x_1332);
x_1333 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1285, x_1280, x_1284);
lean_dec_ref(x_1285);
if (lean_obj_tag(x_1333) == 0)
{
lean_object* x_1334; 
lean_dec_ref(x_1333);
lean_inc(x_1286);
lean_inc_ref(x_1278);
lean_inc(x_1284);
lean_inc_ref(x_1281);
lean_inc_ref(x_1283);
lean_inc(x_1280);
lean_inc_ref(x_1279);
x_1334 = l_Lean_Compiler_LCNF_Simp_simp(x_1277, x_1279, x_1280, x_1283, x_1281, x_1284, x_1278, x_1286);
if (lean_obj_tag(x_1334) == 0)
{
lean_object* x_1335; lean_object* x_1336; 
x_1335 = lean_ctor_get(x_1334, 0);
lean_inc(x_1335);
lean_dec_ref(x_1334);
x_1336 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1330, x_1335, x_1279, x_1280, x_1283, x_1281, x_1284, x_1278, x_1286);
lean_dec(x_1286);
lean_dec_ref(x_1278);
lean_dec(x_1284);
lean_dec_ref(x_1281);
lean_dec_ref(x_1283);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec(x_1330);
return x_1336;
}
else
{
lean_dec(x_1330);
lean_dec(x_1286);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
return x_1334;
}
}
else
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; 
lean_dec(x_1330);
lean_dec(x_1286);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1277);
x_1337 = lean_ctor_get(x_1333, 0);
lean_inc(x_1337);
if (lean_is_exclusive(x_1333)) {
 lean_ctor_release(x_1333, 0);
 x_1338 = x_1333;
} else {
 lean_dec_ref(x_1333);
 x_1338 = lean_box(0);
}
if (lean_is_scalar(x_1338)) {
 x_1339 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1339 = x_1338;
}
lean_ctor_set(x_1339, 0, x_1337);
return x_1339;
}
}
else
{
lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; 
lean_dec(x_1330);
lean_dec(x_1286);
lean_dec_ref(x_1285);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1277);
x_1340 = lean_ctor_get(x_1332, 0);
lean_inc(x_1340);
if (lean_is_exclusive(x_1332)) {
 lean_ctor_release(x_1332, 0);
 x_1341 = x_1332;
} else {
 lean_dec_ref(x_1332);
 x_1341 = lean_box(0);
}
if (lean_is_scalar(x_1341)) {
 x_1342 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1342 = x_1341;
}
lean_ctor_set(x_1342, 0, x_1340);
return x_1342;
}
}
else
{
lean_object* x_1343; 
lean_dec(x_1328);
lean_inc(x_1286);
lean_inc_ref(x_1278);
lean_inc(x_1284);
lean_inc_ref(x_1281);
lean_inc_ref(x_1283);
lean_inc(x_1280);
lean_inc_ref(x_1279);
lean_inc_ref(x_1277);
x_1343 = l_Lean_Compiler_LCNF_Simp_simp(x_1277, x_1279, x_1280, x_1283, x_1281, x_1284, x_1278, x_1286);
if (lean_obj_tag(x_1343) == 0)
{
lean_object* x_1344; lean_object* x_1345; 
x_1344 = lean_ctor_get(x_1343, 0);
lean_inc(x_1344);
lean_dec_ref(x_1343);
x_1345 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_1304, x_1280);
if (lean_obj_tag(x_1345) == 0)
{
lean_object* x_1346; uint8_t x_1347; 
x_1346 = lean_ctor_get(x_1345, 0);
lean_inc(x_1346);
lean_dec_ref(x_1345);
x_1347 = lean_unbox(x_1346);
lean_dec(x_1346);
if (x_1347 == 0)
{
lean_object* x_1348; 
lean_dec(x_1286);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1);
x_1348 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1285, x_1280, x_1284);
lean_dec(x_1284);
lean_dec(x_1280);
lean_dec_ref(x_1285);
if (lean_obj_tag(x_1348) == 0)
{
lean_object* x_1349; lean_object* x_1350; 
if (lean_is_exclusive(x_1348)) {
 lean_ctor_release(x_1348, 0);
 x_1349 = x_1348;
} else {
 lean_dec_ref(x_1348);
 x_1349 = lean_box(0);
}
if (lean_is_scalar(x_1349)) {
 x_1350 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1350 = x_1349;
}
lean_ctor_set(x_1350, 0, x_1344);
return x_1350;
}
else
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; 
lean_dec(x_1344);
x_1351 = lean_ctor_get(x_1348, 0);
lean_inc(x_1351);
if (lean_is_exclusive(x_1348)) {
 lean_ctor_release(x_1348, 0);
 x_1352 = x_1348;
} else {
 lean_dec_ref(x_1348);
 x_1352 = lean_box(0);
}
if (lean_is_scalar(x_1352)) {
 x_1353 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1353 = x_1352;
}
lean_ctor_set(x_1353, 0, x_1351);
return x_1353;
}
}
else
{
lean_object* x_1354; 
lean_inc_ref(x_1285);
x_1354 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_1285, x_1279, x_1280, x_1283, x_1281, x_1284, x_1278, x_1286);
lean_dec(x_1286);
lean_dec_ref(x_1278);
lean_dec(x_1284);
lean_dec_ref(x_1281);
lean_dec_ref(x_1283);
lean_dec(x_1280);
lean_dec_ref(x_1279);
if (lean_obj_tag(x_1354) == 0)
{
size_t x_1355; size_t x_1356; uint8_t x_1357; 
lean_dec_ref(x_1354);
x_1355 = lean_ptr_addr(x_1277);
x_1356 = lean_ptr_addr(x_1344);
x_1357 = lean_usize_dec_eq(x_1355, x_1356);
if (x_1357 == 0)
{
x_98 = x_1344;
x_99 = lean_box(0);
x_100 = x_1285;
x_101 = x_1357;
goto block_105;
}
else
{
size_t x_1358; size_t x_1359; uint8_t x_1360; 
x_1358 = lean_ptr_addr(x_1276);
x_1359 = lean_ptr_addr(x_1285);
x_1360 = lean_usize_dec_eq(x_1358, x_1359);
x_98 = x_1344;
x_99 = lean_box(0);
x_100 = x_1285;
x_101 = x_1360;
goto block_105;
}
}
else
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
lean_dec(x_1344);
lean_dec_ref(x_1285);
lean_dec_ref(x_1);
x_1361 = lean_ctor_get(x_1354, 0);
lean_inc(x_1361);
if (lean_is_exclusive(x_1354)) {
 lean_ctor_release(x_1354, 0);
 x_1362 = x_1354;
} else {
 lean_dec_ref(x_1354);
 x_1362 = lean_box(0);
}
if (lean_is_scalar(x_1362)) {
 x_1363 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1363 = x_1362;
}
lean_ctor_set(x_1363, 0, x_1361);
return x_1363;
}
}
}
else
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
lean_dec(x_1344);
lean_dec(x_1286);
lean_dec_ref(x_1285);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1);
x_1364 = lean_ctor_get(x_1345, 0);
lean_inc(x_1364);
if (lean_is_exclusive(x_1345)) {
 lean_ctor_release(x_1345, 0);
 x_1365 = x_1345;
} else {
 lean_dec_ref(x_1345);
 x_1365 = lean_box(0);
}
if (lean_is_scalar(x_1365)) {
 x_1366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1366 = x_1365;
}
lean_ctor_set(x_1366, 0, x_1364);
return x_1366;
}
}
else
{
lean_dec(x_1286);
lean_dec_ref(x_1285);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1);
return x_1343;
}
}
}
else
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
lean_dec(x_1286);
lean_dec_ref(x_1285);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1);
x_1367 = lean_ctor_get(x_1327, 0);
lean_inc(x_1367);
if (lean_is_exclusive(x_1327)) {
 lean_ctor_release(x_1327, 0);
 x_1368 = x_1327;
} else {
 lean_dec_ref(x_1327);
 x_1368 = lean_box(0);
}
if (lean_is_scalar(x_1368)) {
 x_1369 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1369 = x_1368;
}
lean_ctor_set(x_1369, 0, x_1367);
return x_1369;
}
}
}
else
{
lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; 
lean_dec(x_1286);
lean_dec_ref(x_1285);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1);
x_1370 = lean_ctor_get(x_1318, 0);
lean_inc(x_1370);
if (lean_is_exclusive(x_1318)) {
 lean_ctor_release(x_1318, 0);
 x_1371 = x_1318;
} else {
 lean_dec_ref(x_1318);
 x_1371 = lean_box(0);
}
if (lean_is_scalar(x_1371)) {
 x_1372 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1372 = x_1371;
}
lean_ctor_set(x_1372, 0, x_1370);
return x_1372;
}
}
}
else
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
lean_dec(x_1286);
lean_dec_ref(x_1285);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1);
x_1373 = lean_ctor_get(x_1306, 0);
lean_inc(x_1373);
if (lean_is_exclusive(x_1306)) {
 lean_ctor_release(x_1306, 0);
 x_1374 = x_1306;
} else {
 lean_dec_ref(x_1306);
 x_1374 = lean_box(0);
}
if (lean_is_scalar(x_1374)) {
 x_1375 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1375 = x_1374;
}
lean_ctor_set(x_1375, 0, x_1373);
return x_1375;
}
}
}
else
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
lean_dec(x_1286);
lean_dec_ref(x_1285);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1);
x_1376 = lean_ctor_get(x_1298, 0);
lean_inc(x_1376);
if (lean_is_exclusive(x_1298)) {
 lean_ctor_release(x_1298, 0);
 x_1377 = x_1298;
} else {
 lean_dec_ref(x_1298);
 x_1377 = lean_box(0);
}
if (lean_is_scalar(x_1377)) {
 x_1378 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1378 = x_1377;
}
lean_ctor_set(x_1378, 0, x_1376);
return x_1378;
}
}
}
else
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
lean_dec(x_1286);
lean_dec_ref(x_1285);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1);
x_1379 = lean_ctor_get(x_1288, 0);
lean_inc(x_1379);
if (lean_is_exclusive(x_1288)) {
 lean_ctor_release(x_1288, 0);
 x_1380 = x_1288;
} else {
 lean_dec_ref(x_1288);
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
else
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; uint8_t x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; 
lean_inc_ref(x_1277);
lean_dec_ref(x_1);
x_1382 = lean_st_ref_take(x_1280);
x_1383 = lean_ctor_get(x_1285, 0);
x_1384 = lean_ctor_get(x_1382, 0);
lean_inc_ref(x_1384);
x_1385 = lean_ctor_get(x_1382, 1);
lean_inc_ref(x_1385);
x_1386 = lean_ctor_get(x_1382, 2);
lean_inc(x_1386);
x_1387 = lean_ctor_get(x_1382, 3);
lean_inc_ref(x_1387);
x_1388 = lean_ctor_get_uint8(x_1382, sizeof(void*)*7);
x_1389 = lean_ctor_get(x_1382, 4);
lean_inc(x_1389);
x_1390 = lean_ctor_get(x_1382, 5);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1382, 6);
lean_inc(x_1391);
if (lean_is_exclusive(x_1382)) {
 lean_ctor_release(x_1382, 0);
 lean_ctor_release(x_1382, 1);
 lean_ctor_release(x_1382, 2);
 lean_ctor_release(x_1382, 3);
 lean_ctor_release(x_1382, 4);
 lean_ctor_release(x_1382, 5);
 lean_ctor_release(x_1382, 6);
 x_1392 = x_1382;
} else {
 lean_dec_ref(x_1382);
 x_1392 = lean_box(0);
}
x_1393 = lean_box(0);
lean_inc(x_1383);
x_1394 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1384, x_1383, x_1393);
if (lean_is_scalar(x_1392)) {
 x_1395 = lean_alloc_ctor(0, 7, 1);
} else {
 x_1395 = x_1392;
}
lean_ctor_set(x_1395, 0, x_1394);
lean_ctor_set(x_1395, 1, x_1385);
lean_ctor_set(x_1395, 2, x_1386);
lean_ctor_set(x_1395, 3, x_1387);
lean_ctor_set(x_1395, 4, x_1389);
lean_ctor_set(x_1395, 5, x_1390);
lean_ctor_set(x_1395, 6, x_1391);
lean_ctor_set_uint8(x_1395, sizeof(void*)*7, x_1388);
x_1396 = lean_st_ref_set(x_1280, x_1395);
x_1397 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1285, x_1280, x_1284);
lean_dec_ref(x_1285);
if (lean_obj_tag(x_1397) == 0)
{
lean_dec_ref(x_1397);
x_1 = x_1277;
x_2 = x_1279;
x_3 = x_1280;
x_4 = x_1283;
x_5 = x_1281;
x_6 = x_1284;
x_7 = x_1278;
x_8 = x_1286;
goto _start;
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_1286);
lean_dec(x_1284);
lean_dec_ref(x_1283);
lean_dec_ref(x_1281);
lean_dec(x_1280);
lean_dec_ref(x_1279);
lean_dec_ref(x_1278);
lean_dec_ref(x_1277);
x_1399 = lean_ctor_get(x_1397, 0);
lean_inc(x_1399);
if (lean_is_exclusive(x_1397)) {
 lean_ctor_release(x_1397, 0);
 x_1400 = x_1397;
} else {
 lean_dec_ref(x_1397);
 x_1400 = lean_box(0);
}
if (lean_is_scalar(x_1400)) {
 x_1401 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1401 = x_1400;
}
lean_ctor_set(x_1401, 0, x_1399);
return x_1401;
}
}
}
block_1417:
{
uint8_t x_1414; 
x_1414 = l_Lean_Expr_isErased(x_1404);
lean_dec_ref(x_1404);
if (x_1414 == 0)
{
lean_dec(x_1405);
x_1278 = x_1411;
x_1279 = x_1406;
x_1280 = x_1407;
x_1281 = x_1409;
x_1282 = lean_box(0);
x_1283 = x_1408;
x_1284 = x_1410;
x_1285 = x_1403;
x_1286 = x_1412;
x_1287 = x_122;
goto block_1402;
}
else
{
lean_object* x_1415; uint8_t x_1416; 
x_1415 = lean_box(1);
x_1416 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_1405, x_1415);
lean_dec(x_1405);
if (x_1416 == 0)
{
x_1278 = x_1411;
x_1279 = x_1406;
x_1280 = x_1407;
x_1281 = x_1409;
x_1282 = lean_box(0);
x_1283 = x_1408;
x_1284 = x_1410;
x_1285 = x_1403;
x_1286 = x_1412;
x_1287 = x_1414;
goto block_1402;
}
else
{
x_1278 = x_1411;
x_1279 = x_1406;
x_1280 = x_1407;
x_1281 = x_1409;
x_1282 = lean_box(0);
x_1283 = x_1408;
x_1284 = x_1410;
x_1285 = x_1403;
x_1286 = x_1412;
x_1287 = x_122;
goto block_1402;
}
}
}
}
case 3:
{
lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; 
lean_dec(x_1224);
x_1457 = lean_ctor_get(x_1, 0);
x_1458 = lean_ctor_get(x_1, 1);
x_1459 = lean_st_ref_get(x_3);
x_1460 = lean_ctor_get(x_1459, 0);
lean_inc_ref(x_1460);
lean_dec(x_1459);
lean_inc(x_1457);
x_1461 = l_Lean_Compiler_LCNF_normFVarImp(x_1460, x_1457, x_122);
lean_dec_ref(x_1460);
if (lean_obj_tag(x_1461) == 0)
{
lean_object* x_1462; lean_object* x_1463; 
x_1462 = lean_ctor_get(x_1461, 0);
lean_inc(x_1462);
lean_dec_ref(x_1461);
lean_inc_ref(x_1458);
x_1463 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_122, x_1458, x_3);
if (lean_obj_tag(x_1463) == 0)
{
lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; uint8_t x_1467; lean_object* x_1473; lean_object* x_1479; lean_object* x_1484; 
x_1464 = lean_ctor_get(x_1463, 0);
lean_inc(x_1464);
if (lean_is_exclusive(x_1463)) {
 lean_ctor_release(x_1463, 0);
 x_1465 = x_1463;
} else {
 lean_dec_ref(x_1463);
 x_1465 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_1275);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1464);
x_1484 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1462, x_1464, x_2, x_3, x_4, x_5, x_6, x_1275, x_8);
if (lean_obj_tag(x_1484) == 0)
{
lean_object* x_1485; 
x_1485 = lean_ctor_get(x_1484, 0);
lean_inc(x_1485);
lean_dec_ref(x_1484);
if (lean_obj_tag(x_1485) == 1)
{
lean_object* x_1486; 
lean_dec(x_1465);
lean_dec(x_1464);
lean_dec(x_1462);
lean_dec_ref(x_1);
x_1486 = lean_ctor_get(x_1485, 0);
lean_inc(x_1486);
lean_dec_ref(x_1485);
x_1 = x_1486;
x_7 = x_1275;
goto _start;
}
else
{
lean_object* x_1488; 
lean_dec(x_1485);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_1462);
x_1488 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1462, x_3);
if (lean_obj_tag(x_1488) == 0)
{
lean_object* x_1489; lean_object* x_1490; uint8_t x_1491; 
lean_dec_ref(x_1488);
x_1489 = lean_unsigned_to_nat(0u);
x_1490 = lean_array_get_size(x_1464);
x_1491 = lean_nat_dec_lt(x_1489, x_1490);
if (x_1491 == 0)
{
lean_dec(x_3);
x_1473 = lean_box(0);
goto block_1478;
}
else
{
lean_object* x_1492; uint8_t x_1493; 
x_1492 = lean_box(0);
x_1493 = lean_nat_dec_le(x_1490, x_1490);
if (x_1493 == 0)
{
if (x_1491 == 0)
{
lean_dec(x_3);
x_1473 = lean_box(0);
goto block_1478;
}
else
{
size_t x_1494; size_t x_1495; lean_object* x_1496; 
x_1494 = 0;
x_1495 = lean_usize_of_nat(x_1490);
x_1496 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1464, x_1494, x_1495, x_1492, x_3);
lean_dec(x_3);
x_1479 = x_1496;
goto block_1483;
}
}
else
{
size_t x_1497; size_t x_1498; lean_object* x_1499; 
x_1497 = 0;
x_1498 = lean_usize_of_nat(x_1490);
x_1499 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1464, x_1497, x_1498, x_1492, x_3);
lean_dec(x_3);
x_1479 = x_1499;
goto block_1483;
}
}
}
else
{
lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; 
lean_dec(x_1465);
lean_dec(x_1464);
lean_dec(x_1462);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1500 = lean_ctor_get(x_1488, 0);
lean_inc(x_1500);
if (lean_is_exclusive(x_1488)) {
 lean_ctor_release(x_1488, 0);
 x_1501 = x_1488;
} else {
 lean_dec_ref(x_1488);
 x_1501 = lean_box(0);
}
if (lean_is_scalar(x_1501)) {
 x_1502 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1502 = x_1501;
}
lean_ctor_set(x_1502, 0, x_1500);
return x_1502;
}
}
}
else
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; 
lean_dec(x_1465);
lean_dec(x_1464);
lean_dec(x_1462);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1503 = lean_ctor_get(x_1484, 0);
lean_inc(x_1503);
if (lean_is_exclusive(x_1484)) {
 lean_ctor_release(x_1484, 0);
 x_1504 = x_1484;
} else {
 lean_dec_ref(x_1484);
 x_1504 = lean_box(0);
}
if (lean_is_scalar(x_1504)) {
 x_1505 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1505 = x_1504;
}
lean_ctor_set(x_1505, 0, x_1503);
return x_1505;
}
block_1472:
{
if (x_1467 == 0)
{
lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1468 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1468 = lean_box(0);
}
if (lean_is_scalar(x_1468)) {
 x_1469 = lean_alloc_ctor(3, 2, 0);
} else {
 x_1469 = x_1468;
}
lean_ctor_set(x_1469, 0, x_1462);
lean_ctor_set(x_1469, 1, x_1464);
if (lean_is_scalar(x_1465)) {
 x_1470 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1470 = x_1465;
}
lean_ctor_set(x_1470, 0, x_1469);
return x_1470;
}
else
{
lean_object* x_1471; 
lean_dec(x_1464);
lean_dec(x_1462);
if (lean_is_scalar(x_1465)) {
 x_1471 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1471 = x_1465;
}
lean_ctor_set(x_1471, 0, x_1);
return x_1471;
}
}
block_1478:
{
uint8_t x_1474; 
x_1474 = l_Lean_instBEqFVarId_beq(x_1457, x_1462);
if (x_1474 == 0)
{
x_1466 = lean_box(0);
x_1467 = x_1474;
goto block_1472;
}
else
{
size_t x_1475; size_t x_1476; uint8_t x_1477; 
x_1475 = lean_ptr_addr(x_1458);
x_1476 = lean_ptr_addr(x_1464);
x_1477 = lean_usize_dec_eq(x_1475, x_1476);
x_1466 = lean_box(0);
x_1467 = x_1477;
goto block_1472;
}
}
block_1483:
{
if (lean_obj_tag(x_1479) == 0)
{
lean_dec_ref(x_1479);
x_1473 = lean_box(0);
goto block_1478;
}
else
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; 
lean_dec(x_1465);
lean_dec(x_1464);
lean_dec(x_1462);
lean_dec_ref(x_1);
x_1480 = lean_ctor_get(x_1479, 0);
lean_inc(x_1480);
if (lean_is_exclusive(x_1479)) {
 lean_ctor_release(x_1479, 0);
 x_1481 = x_1479;
} else {
 lean_dec_ref(x_1479);
 x_1481 = lean_box(0);
}
if (lean_is_scalar(x_1481)) {
 x_1482 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1482 = x_1481;
}
lean_ctor_set(x_1482, 0, x_1480);
return x_1482;
}
}
}
else
{
lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; 
lean_dec(x_1462);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1506 = lean_ctor_get(x_1463, 0);
lean_inc(x_1506);
if (lean_is_exclusive(x_1463)) {
 lean_ctor_release(x_1463, 0);
 x_1507 = x_1463;
} else {
 lean_dec_ref(x_1463);
 x_1507 = lean_box(0);
}
if (lean_is_scalar(x_1507)) {
 x_1508 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1508 = x_1507;
}
lean_ctor_set(x_1508, 0, x_1506);
return x_1508;
}
}
else
{
lean_object* x_1509; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1509 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1275, x_8);
lean_dec(x_8);
lean_dec_ref(x_1275);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1509;
}
}
case 4:
{
lean_object* x_1510; lean_object* x_1511; 
lean_dec(x_1224);
x_1510 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1510);
lean_inc(x_8);
lean_inc_ref(x_1275);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1510);
x_1511 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1510, x_2, x_3, x_4, x_5, x_6, x_1275, x_8);
if (lean_obj_tag(x_1511) == 0)
{
lean_object* x_1512; lean_object* x_1513; 
x_1512 = lean_ctor_get(x_1511, 0);
lean_inc(x_1512);
if (lean_is_exclusive(x_1511)) {
 lean_ctor_release(x_1511, 0);
 x_1513 = x_1511;
} else {
 lean_dec_ref(x_1511);
 x_1513 = lean_box(0);
}
if (lean_obj_tag(x_1512) == 1)
{
lean_object* x_1514; lean_object* x_1515; 
lean_dec_ref(x_1510);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1514 = lean_ctor_get(x_1512, 0);
lean_inc(x_1514);
lean_dec_ref(x_1512);
if (lean_is_scalar(x_1513)) {
 x_1515 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1515 = x_1513;
}
lean_ctor_set(x_1515, 0, x_1514);
return x_1515;
}
else
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; 
lean_dec(x_1512);
x_1516 = lean_ctor_get(x_1510, 0);
lean_inc(x_1516);
x_1517 = lean_ctor_get(x_1510, 1);
lean_inc_ref(x_1517);
x_1518 = lean_ctor_get(x_1510, 2);
lean_inc(x_1518);
x_1519 = lean_ctor_get(x_1510, 3);
lean_inc_ref(x_1519);
if (lean_is_exclusive(x_1510)) {
 lean_ctor_release(x_1510, 0);
 lean_ctor_release(x_1510, 1);
 lean_ctor_release(x_1510, 2);
 lean_ctor_release(x_1510, 3);
 x_1520 = x_1510;
} else {
 lean_dec_ref(x_1510);
 x_1520 = lean_box(0);
}
x_1521 = lean_st_ref_get(x_3);
x_1522 = lean_ctor_get(x_1521, 0);
lean_inc_ref(x_1522);
lean_dec(x_1521);
lean_inc(x_1518);
x_1523 = l_Lean_Compiler_LCNF_normFVarImp(x_1522, x_1518, x_122);
lean_dec_ref(x_1522);
if (lean_obj_tag(x_1523) == 0)
{
lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; 
x_1524 = lean_ctor_get(x_1523, 0);
lean_inc(x_1524);
if (lean_is_exclusive(x_1523)) {
 lean_ctor_release(x_1523, 0);
 x_1525 = x_1523;
} else {
 lean_dec_ref(x_1523);
 x_1525 = lean_box(0);
}
x_1526 = lean_st_ref_get(x_3);
x_1527 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_1275);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1519);
lean_inc(x_1524);
x_1528 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_1524, x_122, x_1527, x_1519, x_2, x_3, x_4, x_5, x_6, x_1275, x_8);
if (lean_obj_tag(x_1528) == 0)
{
lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; 
x_1529 = lean_ctor_get(x_1528, 0);
lean_inc(x_1529);
if (lean_is_exclusive(x_1528)) {
 lean_ctor_release(x_1528, 0);
 x_1530 = x_1528;
} else {
 lean_dec_ref(x_1528);
 x_1530 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_1275);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_1531 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1529, x_2, x_3, x_4, x_5, x_6, x_1275, x_8);
if (lean_obj_tag(x_1531) == 0)
{
lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1546; lean_object* x_1547; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1569; lean_object* x_1574; uint8_t x_1575; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1601; uint8_t x_1602; 
x_1532 = lean_ctor_get(x_1531, 0);
lean_inc(x_1532);
if (lean_is_exclusive(x_1531)) {
 lean_ctor_release(x_1531, 0);
 x_1533 = x_1531;
} else {
 lean_dec_ref(x_1531);
 x_1533 = lean_box(0);
}
x_1534 = lean_ctor_get(x_1526, 0);
lean_inc_ref(x_1534);
lean_dec(x_1526);
lean_inc_ref(x_1517);
x_1535 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1534, x_122, x_1517);
lean_dec_ref(x_1534);
x_1601 = lean_array_get_size(x_1532);
x_1602 = lean_nat_dec_eq(x_1601, x_1273);
if (x_1602 == 0)
{
lean_dec(x_1513);
x_1579 = x_3;
x_1580 = x_5;
x_1581 = x_6;
x_1582 = x_1275;
x_1583 = x_8;
x_1584 = lean_box(0);
goto block_1600;
}
else
{
lean_object* x_1603; 
x_1603 = lean_array_fget_borrowed(x_1532, x_1527);
if (lean_obj_tag(x_1603) == 0)
{
lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1614; lean_object* x_1619; lean_object* x_1620; uint8_t x_1631; lean_object* x_1632; uint8_t x_1634; 
lean_dec(x_1513);
x_1604 = lean_ctor_get(x_1603, 1);
x_1605 = lean_ctor_get(x_1603, 2);
x_1619 = lean_array_get_size(x_1604);
x_1634 = lean_nat_dec_lt(x_1527, x_1619);
if (x_1634 == 0)
{
x_1631 = x_122;
x_1632 = lean_box(0);
goto block_1633;
}
else
{
if (x_1634 == 0)
{
x_1631 = x_122;
x_1632 = lean_box(0);
goto block_1633;
}
else
{
size_t x_1635; size_t x_1636; lean_object* x_1637; 
x_1635 = 0;
x_1636 = lean_usize_of_nat(x_1619);
x_1637 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_1604, x_1635, x_1636, x_3);
if (lean_obj_tag(x_1637) == 0)
{
lean_object* x_1638; uint8_t x_1639; 
x_1638 = lean_ctor_get(x_1637, 0);
lean_inc(x_1638);
lean_dec_ref(x_1637);
x_1639 = lean_unbox(x_1638);
lean_dec(x_1638);
x_1631 = x_1639;
x_1632 = lean_box(0);
goto block_1633;
}
else
{
lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; 
lean_dec_ref(x_1535);
lean_dec(x_1533);
lean_dec(x_1532);
lean_dec(x_1530);
lean_dec(x_1525);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1640 = lean_ctor_get(x_1637, 0);
lean_inc(x_1640);
if (lean_is_exclusive(x_1637)) {
 lean_ctor_release(x_1637, 0);
 x_1641 = x_1637;
} else {
 lean_dec_ref(x_1637);
 x_1641 = lean_box(0);
}
if (lean_is_scalar(x_1641)) {
 x_1642 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1642 = x_1641;
}
lean_ctor_set(x_1642, 0, x_1640);
return x_1642;
}
}
}
block_1613:
{
lean_object* x_1607; 
x_1607 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1607) == 0)
{
lean_object* x_1608; lean_object* x_1609; 
if (lean_is_exclusive(x_1607)) {
 lean_ctor_release(x_1607, 0);
 x_1608 = x_1607;
} else {
 lean_dec_ref(x_1607);
 x_1608 = lean_box(0);
}
if (lean_is_scalar(x_1608)) {
 x_1609 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1609 = x_1608;
}
lean_ctor_set(x_1609, 0, x_1605);
return x_1609;
}
else
{
lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; 
lean_dec_ref(x_1605);
x_1610 = lean_ctor_get(x_1607, 0);
lean_inc(x_1610);
if (lean_is_exclusive(x_1607)) {
 lean_ctor_release(x_1607, 0);
 x_1611 = x_1607;
} else {
 lean_dec_ref(x_1607);
 x_1611 = lean_box(0);
}
if (lean_is_scalar(x_1611)) {
 x_1612 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1612 = x_1611;
}
lean_ctor_set(x_1612, 0, x_1610);
return x_1612;
}
}
block_1618:
{
if (lean_obj_tag(x_1614) == 0)
{
lean_dec_ref(x_1614);
x_1606 = lean_box(0);
goto block_1613;
}
else
{
lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; 
lean_dec_ref(x_1605);
lean_dec(x_3);
x_1615 = lean_ctor_get(x_1614, 0);
lean_inc(x_1615);
if (lean_is_exclusive(x_1614)) {
 lean_ctor_release(x_1614, 0);
 x_1616 = x_1614;
} else {
 lean_dec_ref(x_1614);
 x_1616 = lean_box(0);
}
if (lean_is_scalar(x_1616)) {
 x_1617 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1617 = x_1616;
}
lean_ctor_set(x_1617, 0, x_1615);
return x_1617;
}
}
block_1630:
{
uint8_t x_1621; 
x_1621 = lean_nat_dec_lt(x_1527, x_1619);
if (x_1621 == 0)
{
lean_dec_ref(x_1604);
lean_dec(x_6);
x_1606 = lean_box(0);
goto block_1613;
}
else
{
lean_object* x_1622; uint8_t x_1623; 
x_1622 = lean_box(0);
x_1623 = lean_nat_dec_le(x_1619, x_1619);
if (x_1623 == 0)
{
if (x_1621 == 0)
{
lean_dec_ref(x_1604);
lean_dec(x_6);
x_1606 = lean_box(0);
goto block_1613;
}
else
{
size_t x_1624; size_t x_1625; lean_object* x_1626; 
x_1624 = 0;
x_1625 = lean_usize_of_nat(x_1619);
x_1626 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1604, x_1624, x_1625, x_1622, x_6);
lean_dec(x_6);
lean_dec_ref(x_1604);
x_1614 = x_1626;
goto block_1618;
}
}
else
{
size_t x_1627; size_t x_1628; lean_object* x_1629; 
x_1627 = 0;
x_1628 = lean_usize_of_nat(x_1619);
x_1629 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1604, x_1627, x_1628, x_1622, x_6);
lean_dec(x_6);
lean_dec_ref(x_1604);
x_1614 = x_1629;
goto block_1618;
}
}
}
block_1633:
{
if (x_1631 == 0)
{
lean_inc_ref(x_1605);
lean_inc_ref(x_1604);
lean_dec_ref(x_1535);
lean_dec(x_1533);
lean_dec(x_1532);
lean_dec(x_1530);
lean_dec(x_1525);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1620 = lean_box(0);
goto block_1630;
}
else
{
if (x_122 == 0)
{
x_1579 = x_3;
x_1580 = x_5;
x_1581 = x_6;
x_1582 = x_1275;
x_1583 = x_8;
x_1584 = lean_box(0);
goto block_1600;
}
else
{
lean_inc_ref(x_1605);
lean_inc_ref(x_1604);
lean_dec_ref(x_1535);
lean_dec(x_1533);
lean_dec(x_1532);
lean_dec(x_1530);
lean_dec(x_1525);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1620 = lean_box(0);
goto block_1630;
}
}
}
}
else
{
lean_object* x_1643; lean_object* x_1644; 
lean_inc_ref(x_1603);
lean_dec_ref(x_1535);
lean_dec(x_1533);
lean_dec(x_1532);
lean_dec(x_1530);
lean_dec(x_1525);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1643 = lean_ctor_get(x_1603, 0);
lean_inc_ref(x_1643);
lean_dec_ref(x_1603);
if (lean_is_scalar(x_1513)) {
 x_1644 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1644 = x_1513;
}
lean_ctor_set(x_1644, 0, x_1643);
return x_1644;
}
}
block_1545:
{
lean_object* x_1538; 
x_1538 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1536);
lean_dec(x_1536);
if (lean_obj_tag(x_1538) == 0)
{
lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; 
if (lean_is_exclusive(x_1538)) {
 lean_ctor_release(x_1538, 0);
 x_1539 = x_1538;
} else {
 lean_dec_ref(x_1538);
 x_1539 = lean_box(0);
}
if (lean_is_scalar(x_1525)) {
 x_1540 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1540 = x_1525;
 lean_ctor_set_tag(x_1540, 6);
}
lean_ctor_set(x_1540, 0, x_1535);
if (lean_is_scalar(x_1539)) {
 x_1541 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1541 = x_1539;
}
lean_ctor_set(x_1541, 0, x_1540);
return x_1541;
}
else
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; 
lean_dec_ref(x_1535);
lean_dec(x_1525);
x_1542 = lean_ctor_get(x_1538, 0);
lean_inc(x_1542);
if (lean_is_exclusive(x_1538)) {
 lean_ctor_release(x_1538, 0);
 x_1543 = x_1538;
} else {
 lean_dec_ref(x_1538);
 x_1543 = lean_box(0);
}
if (lean_is_scalar(x_1543)) {
 x_1544 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1544 = x_1543;
}
lean_ctor_set(x_1544, 0, x_1542);
return x_1544;
}
}
block_1551:
{
if (lean_obj_tag(x_1547) == 0)
{
lean_dec_ref(x_1547);
x_1536 = x_1546;
x_1537 = lean_box(0);
goto block_1545;
}
else
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; 
lean_dec(x_1546);
lean_dec_ref(x_1535);
lean_dec(x_1525);
x_1548 = lean_ctor_get(x_1547, 0);
lean_inc(x_1548);
if (lean_is_exclusive(x_1547)) {
 lean_ctor_release(x_1547, 0);
 x_1549 = x_1547;
} else {
 lean_dec_ref(x_1547);
 x_1549 = lean_box(0);
}
if (lean_is_scalar(x_1549)) {
 x_1550 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1550 = x_1549;
}
lean_ctor_set(x_1550, 0, x_1548);
return x_1550;
}
}
block_1568:
{
uint8_t x_1559; 
x_1559 = lean_nat_dec_lt(x_1527, x_1558);
if (x_1559 == 0)
{
lean_dec(x_1558);
lean_dec_ref(x_1557);
lean_dec(x_1554);
lean_dec_ref(x_1553);
lean_dec(x_1552);
lean_dec(x_1532);
x_1536 = x_1556;
x_1537 = lean_box(0);
goto block_1545;
}
else
{
lean_object* x_1560; uint8_t x_1561; 
x_1560 = lean_box(0);
x_1561 = lean_nat_dec_le(x_1558, x_1558);
if (x_1561 == 0)
{
if (x_1559 == 0)
{
lean_dec(x_1558);
lean_dec_ref(x_1557);
lean_dec(x_1554);
lean_dec_ref(x_1553);
lean_dec(x_1552);
lean_dec(x_1532);
x_1536 = x_1556;
x_1537 = lean_box(0);
goto block_1545;
}
else
{
size_t x_1562; size_t x_1563; lean_object* x_1564; 
x_1562 = 0;
x_1563 = lean_usize_of_nat(x_1558);
lean_dec(x_1558);
x_1564 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1527, x_1532, x_1562, x_1563, x_1560, x_1553, x_1552, x_1557, x_1554);
lean_dec(x_1554);
lean_dec_ref(x_1557);
lean_dec(x_1552);
lean_dec_ref(x_1553);
lean_dec(x_1532);
x_1546 = x_1556;
x_1547 = x_1564;
goto block_1551;
}
}
else
{
size_t x_1565; size_t x_1566; lean_object* x_1567; 
x_1565 = 0;
x_1566 = lean_usize_of_nat(x_1558);
lean_dec(x_1558);
x_1567 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1527, x_1532, x_1565, x_1566, x_1560, x_1553, x_1552, x_1557, x_1554);
lean_dec(x_1554);
lean_dec_ref(x_1557);
lean_dec(x_1552);
lean_dec_ref(x_1553);
lean_dec(x_1532);
x_1546 = x_1556;
x_1547 = x_1567;
goto block_1551;
}
}
}
block_1573:
{
lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; 
if (lean_is_scalar(x_1520)) {
 x_1570 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1570 = x_1520;
}
lean_ctor_set(x_1570, 0, x_1516);
lean_ctor_set(x_1570, 1, x_1535);
lean_ctor_set(x_1570, 2, x_1524);
lean_ctor_set(x_1570, 3, x_1532);
x_1571 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1571, 0, x_1570);
if (lean_is_scalar(x_1533)) {
 x_1572 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1572 = x_1533;
}
lean_ctor_set(x_1572, 0, x_1571);
return x_1572;
}
block_1578:
{
if (x_1575 == 0)
{
lean_dec(x_1530);
lean_dec(x_1518);
lean_dec_ref(x_1);
x_1569 = lean_box(0);
goto block_1573;
}
else
{
uint8_t x_1576; 
x_1576 = l_Lean_instBEqFVarId_beq(x_1518, x_1524);
lean_dec(x_1518);
if (x_1576 == 0)
{
lean_dec(x_1530);
lean_dec_ref(x_1);
x_1569 = lean_box(0);
goto block_1573;
}
else
{
lean_object* x_1577; 
lean_dec_ref(x_1535);
lean_dec(x_1533);
lean_dec(x_1532);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec(x_1516);
if (lean_is_scalar(x_1530)) {
 x_1577 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1577 = x_1530;
}
lean_ctor_set(x_1577, 0, x_1);
return x_1577;
}
}
}
block_1600:
{
lean_object* x_1585; uint8_t x_1586; 
x_1585 = lean_array_get_size(x_1532);
x_1586 = lean_nat_dec_lt(x_1527, x_1585);
if (x_1586 == 0)
{
lean_dec(x_1533);
lean_dec(x_1530);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec_ref(x_1);
x_1552 = x_1581;
x_1553 = x_1580;
x_1554 = x_1583;
x_1555 = lean_box(0);
x_1556 = x_1579;
x_1557 = x_1582;
x_1558 = x_1585;
goto block_1568;
}
else
{
if (x_1586 == 0)
{
lean_dec(x_1533);
lean_dec(x_1530);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec_ref(x_1);
x_1552 = x_1581;
x_1553 = x_1580;
x_1554 = x_1583;
x_1555 = lean_box(0);
x_1556 = x_1579;
x_1557 = x_1582;
x_1558 = x_1585;
goto block_1568;
}
else
{
size_t x_1587; size_t x_1588; uint8_t x_1589; 
x_1587 = 0;
x_1588 = lean_usize_of_nat(x_1585);
x_1589 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_122, x_1532, x_1587, x_1588);
if (x_1589 == 0)
{
lean_dec(x_1533);
lean_dec(x_1530);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec_ref(x_1);
x_1552 = x_1581;
x_1553 = x_1580;
x_1554 = x_1583;
x_1555 = lean_box(0);
x_1556 = x_1579;
x_1557 = x_1582;
x_1558 = x_1585;
goto block_1568;
}
else
{
if (x_122 == 0)
{
lean_object* x_1590; 
lean_dec(x_1583);
lean_dec_ref(x_1582);
lean_dec(x_1581);
lean_dec_ref(x_1580);
lean_dec(x_1525);
lean_inc(x_1524);
x_1590 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1524, x_1579);
lean_dec(x_1579);
if (lean_obj_tag(x_1590) == 0)
{
size_t x_1591; size_t x_1592; uint8_t x_1593; 
lean_dec_ref(x_1590);
x_1591 = lean_ptr_addr(x_1519);
lean_dec_ref(x_1519);
x_1592 = lean_ptr_addr(x_1532);
x_1593 = lean_usize_dec_eq(x_1591, x_1592);
if (x_1593 == 0)
{
lean_dec_ref(x_1517);
x_1574 = lean_box(0);
x_1575 = x_1593;
goto block_1578;
}
else
{
size_t x_1594; size_t x_1595; uint8_t x_1596; 
x_1594 = lean_ptr_addr(x_1517);
lean_dec_ref(x_1517);
x_1595 = lean_ptr_addr(x_1535);
x_1596 = lean_usize_dec_eq(x_1594, x_1595);
x_1574 = lean_box(0);
x_1575 = x_1596;
goto block_1578;
}
}
else
{
lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
lean_dec_ref(x_1535);
lean_dec(x_1533);
lean_dec(x_1532);
lean_dec(x_1530);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec_ref(x_1);
x_1597 = lean_ctor_get(x_1590, 0);
lean_inc(x_1597);
if (lean_is_exclusive(x_1590)) {
 lean_ctor_release(x_1590, 0);
 x_1598 = x_1590;
} else {
 lean_dec_ref(x_1590);
 x_1598 = lean_box(0);
}
if (lean_is_scalar(x_1598)) {
 x_1599 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1599 = x_1598;
}
lean_ctor_set(x_1599, 0, x_1597);
return x_1599;
}
}
else
{
lean_dec(x_1533);
lean_dec(x_1530);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec_ref(x_1);
x_1552 = x_1581;
x_1553 = x_1580;
x_1554 = x_1583;
x_1555 = lean_box(0);
x_1556 = x_1579;
x_1557 = x_1582;
x_1558 = x_1585;
goto block_1568;
}
}
}
}
}
}
else
{
lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; 
lean_dec(x_1530);
lean_dec(x_1526);
lean_dec(x_1525);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec(x_1513);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1645 = lean_ctor_get(x_1531, 0);
lean_inc(x_1645);
if (lean_is_exclusive(x_1531)) {
 lean_ctor_release(x_1531, 0);
 x_1646 = x_1531;
} else {
 lean_dec_ref(x_1531);
 x_1646 = lean_box(0);
}
if (lean_is_scalar(x_1646)) {
 x_1647 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1647 = x_1646;
}
lean_ctor_set(x_1647, 0, x_1645);
return x_1647;
}
}
else
{
lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; 
lean_dec(x_1526);
lean_dec(x_1525);
lean_dec(x_1524);
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec(x_1513);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1648 = lean_ctor_get(x_1528, 0);
lean_inc(x_1648);
if (lean_is_exclusive(x_1528)) {
 lean_ctor_release(x_1528, 0);
 x_1649 = x_1528;
} else {
 lean_dec_ref(x_1528);
 x_1649 = lean_box(0);
}
if (lean_is_scalar(x_1649)) {
 x_1650 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1650 = x_1649;
}
lean_ctor_set(x_1650, 0, x_1648);
return x_1650;
}
}
else
{
lean_object* x_1651; 
lean_dec(x_1520);
lean_dec_ref(x_1519);
lean_dec(x_1518);
lean_dec_ref(x_1517);
lean_dec(x_1516);
lean_dec(x_1513);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1651 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1275, x_8);
lean_dec(x_8);
lean_dec_ref(x_1275);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1651;
}
}
}
else
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; 
lean_dec_ref(x_1510);
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1652 = lean_ctor_get(x_1511, 0);
lean_inc(x_1652);
if (lean_is_exclusive(x_1511)) {
 lean_ctor_release(x_1511, 0);
 x_1653 = x_1511;
} else {
 lean_dec_ref(x_1511);
 x_1653 = lean_box(0);
}
if (lean_is_scalar(x_1653)) {
 x_1654 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1654 = x_1653;
}
lean_ctor_set(x_1654, 0, x_1652);
return x_1654;
}
}
case 5:
{
lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; 
lean_dec(x_1224);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1655 = lean_ctor_get(x_1, 0);
x_1656 = lean_st_ref_get(x_3);
x_1657 = lean_ctor_get(x_1656, 0);
lean_inc_ref(x_1657);
lean_dec(x_1656);
lean_inc(x_1655);
x_1658 = l_Lean_Compiler_LCNF_normFVarImp(x_1657, x_1655, x_122);
lean_dec_ref(x_1657);
if (lean_obj_tag(x_1658) == 0)
{
lean_object* x_1659; lean_object* x_1660; 
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1659 = lean_ctor_get(x_1658, 0);
lean_inc(x_1659);
lean_dec_ref(x_1658);
lean_inc(x_1659);
x_1660 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1659, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1660) == 0)
{
lean_object* x_1661; uint8_t x_1662; 
if (lean_is_exclusive(x_1660)) {
 lean_ctor_release(x_1660, 0);
 x_1661 = x_1660;
} else {
 lean_dec_ref(x_1660);
 x_1661 = lean_box(0);
}
x_1662 = l_Lean_instBEqFVarId_beq(x_1655, x_1659);
if (x_1662 == 0)
{
lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1663 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1663 = lean_box(0);
}
if (lean_is_scalar(x_1663)) {
 x_1664 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1664 = x_1663;
}
lean_ctor_set(x_1664, 0, x_1659);
if (lean_is_scalar(x_1661)) {
 x_1665 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1665 = x_1661;
}
lean_ctor_set(x_1665, 0, x_1664);
return x_1665;
}
else
{
lean_object* x_1666; 
lean_dec(x_1659);
if (lean_is_scalar(x_1661)) {
 x_1666 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1666 = x_1661;
}
lean_ctor_set(x_1666, 0, x_1);
return x_1666;
}
}
else
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; 
lean_dec(x_1659);
lean_dec_ref(x_1);
x_1667 = lean_ctor_get(x_1660, 0);
lean_inc(x_1667);
if (lean_is_exclusive(x_1660)) {
 lean_ctor_release(x_1660, 0);
 x_1668 = x_1660;
} else {
 lean_dec_ref(x_1660);
 x_1668 = lean_box(0);
}
if (lean_is_scalar(x_1668)) {
 x_1669 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1669 = x_1668;
}
lean_ctor_set(x_1669, 0, x_1667);
return x_1669;
}
}
else
{
lean_object* x_1670; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1670 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1275, x_8);
lean_dec(x_8);
lean_dec_ref(x_1275);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1670;
}
}
case 6:
{
lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; size_t x_1675; size_t x_1676; uint8_t x_1677; 
lean_dec_ref(x_1275);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1671 = lean_ctor_get(x_1, 0);
x_1672 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_1673 = lean_ctor_get(x_1672, 0);
lean_inc_ref(x_1673);
lean_dec(x_1672);
lean_inc_ref(x_1671);
x_1674 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1673, x_122, x_1671);
lean_dec_ref(x_1673);
x_1675 = lean_ptr_addr(x_1671);
x_1676 = lean_ptr_addr(x_1674);
x_1677 = lean_usize_dec_eq(x_1675, x_1676);
if (x_1677 == 0)
{
lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1678 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1678 = lean_box(0);
}
if (lean_is_scalar(x_1678)) {
 x_1679 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1679 = x_1678;
}
lean_ctor_set(x_1679, 0, x_1674);
if (lean_is_scalar(x_1224)) {
 x_1680 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1680 = x_1224;
}
lean_ctor_set(x_1680, 0, x_1679);
return x_1680;
}
else
{
lean_object* x_1681; 
lean_dec_ref(x_1674);
if (lean_is_scalar(x_1224)) {
 x_1681 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1681 = x_1224;
}
lean_ctor_set(x_1681, 0, x_1);
return x_1681;
}
}
default: 
{
lean_object* x_1682; lean_object* x_1683; 
lean_dec(x_1224);
x_1682 = lean_ctor_get(x_1, 0);
x_1683 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1683);
lean_inc_ref(x_1682);
x_1225 = x_1682;
x_1226 = x_1683;
x_1227 = x_2;
x_1228 = x_3;
x_1229 = x_4;
x_1230 = x_5;
x_1231 = x_6;
x_1232 = x_1275;
x_1233 = x_8;
goto block_1272;
}
}
block_1272:
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; 
x_1234 = lean_ctor_get(x_1225, 0);
x_1235 = lean_ctor_get(x_1225, 2);
x_1236 = lean_ctor_get(x_1225, 3);
x_1237 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_1234, x_1228);
if (lean_obj_tag(x_1237) == 0)
{
lean_object* x_1238; uint8_t x_1239; 
x_1238 = lean_ctor_get(x_1237, 0);
lean_inc(x_1238);
lean_dec_ref(x_1237);
x_1239 = lean_unbox(x_1238);
if (x_1239 == 0)
{
uint8_t x_1240; 
x_1240 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
if (x_1240 == 0)
{
uint8_t x_1241; 
x_1241 = lean_unbox(x_1238);
lean_dec(x_1238);
x_81 = x_1241;
x_82 = x_1226;
x_83 = x_1225;
x_84 = x_1227;
x_85 = x_1228;
x_86 = x_1229;
x_87 = x_1230;
x_88 = x_1231;
x_89 = x_1232;
x_90 = x_1233;
x_91 = lean_box(0);
goto block_97;
}
else
{
uint8_t x_1242; 
lean_inc_ref(x_1236);
x_1242 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_1236, x_1235);
if (x_1242 == 0)
{
uint8_t x_1243; 
x_1243 = lean_unbox(x_1238);
lean_dec(x_1238);
x_81 = x_1243;
x_82 = x_1226;
x_83 = x_1225;
x_84 = x_1227;
x_85 = x_1228;
x_86 = x_1229;
x_87 = x_1230;
x_88 = x_1231;
x_89 = x_1232;
x_90 = x_1233;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; 
x_1244 = lean_st_ref_get(x_1228);
x_1245 = lean_ctor_get(x_1244, 0);
lean_inc_ref(x_1245);
lean_dec(x_1244);
x_1246 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_1225, x_1245, x_1230, x_1231, x_1232, x_1233);
lean_dec_ref(x_1245);
if (lean_obj_tag(x_1246) == 0)
{
lean_object* x_1247; lean_object* x_1248; 
x_1247 = lean_ctor_get(x_1246, 0);
lean_inc(x_1247);
lean_dec_ref(x_1246);
lean_inc(x_1233);
lean_inc_ref(x_1232);
lean_inc(x_1231);
lean_inc_ref(x_1230);
x_1248 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_1247, x_1230, x_1231, x_1232, x_1233);
if (lean_obj_tag(x_1248) == 0)
{
lean_object* x_1249; lean_object* x_1250; 
x_1249 = lean_ctor_get(x_1248, 0);
lean_inc(x_1249);
lean_dec_ref(x_1248);
x_1250 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1228);
if (lean_obj_tag(x_1250) == 0)
{
uint8_t x_1251; 
lean_dec_ref(x_1250);
x_1251 = lean_unbox(x_1238);
lean_dec(x_1238);
x_81 = x_1251;
x_82 = x_1226;
x_83 = x_1249;
x_84 = x_1227;
x_85 = x_1228;
x_86 = x_1229;
x_87 = x_1230;
x_88 = x_1231;
x_89 = x_1232;
x_90 = x_1233;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; 
lean_dec(x_1249);
lean_dec(x_1238);
lean_dec(x_1233);
lean_dec_ref(x_1232);
lean_dec(x_1231);
lean_dec_ref(x_1230);
lean_dec_ref(x_1229);
lean_dec(x_1228);
lean_dec_ref(x_1227);
lean_dec_ref(x_1226);
lean_dec_ref(x_1);
x_1252 = lean_ctor_get(x_1250, 0);
lean_inc(x_1252);
if (lean_is_exclusive(x_1250)) {
 lean_ctor_release(x_1250, 0);
 x_1253 = x_1250;
} else {
 lean_dec_ref(x_1250);
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
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
lean_dec(x_1238);
lean_dec(x_1233);
lean_dec_ref(x_1232);
lean_dec(x_1231);
lean_dec_ref(x_1230);
lean_dec_ref(x_1229);
lean_dec(x_1228);
lean_dec_ref(x_1227);
lean_dec_ref(x_1226);
lean_dec_ref(x_1);
x_1255 = lean_ctor_get(x_1248, 0);
lean_inc(x_1255);
if (lean_is_exclusive(x_1248)) {
 lean_ctor_release(x_1248, 0);
 x_1256 = x_1248;
} else {
 lean_dec_ref(x_1248);
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
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
lean_dec(x_1238);
lean_dec(x_1233);
lean_dec_ref(x_1232);
lean_dec(x_1231);
lean_dec_ref(x_1230);
lean_dec_ref(x_1229);
lean_dec(x_1228);
lean_dec_ref(x_1227);
lean_dec_ref(x_1226);
lean_dec_ref(x_1);
x_1258 = lean_ctor_get(x_1246, 0);
lean_inc(x_1258);
if (lean_is_exclusive(x_1246)) {
 lean_ctor_release(x_1246, 0);
 x_1259 = x_1246;
} else {
 lean_dec_ref(x_1246);
 x_1259 = lean_box(0);
}
if (lean_is_scalar(x_1259)) {
 x_1260 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1260 = x_1259;
}
lean_ctor_set(x_1260, 0, x_1258);
return x_1260;
}
}
}
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
x_1261 = lean_st_ref_get(x_1228);
x_1262 = lean_ctor_get(x_1261, 0);
lean_inc_ref(x_1262);
lean_dec(x_1261);
x_1263 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_1225, x_1262, x_1230, x_1231, x_1232, x_1233);
lean_dec_ref(x_1262);
if (lean_obj_tag(x_1263) == 0)
{
lean_object* x_1264; uint8_t x_1265; 
x_1264 = lean_ctor_get(x_1263, 0);
lean_inc(x_1264);
lean_dec_ref(x_1263);
x_1265 = lean_unbox(x_1238);
lean_dec(x_1238);
x_49 = x_1265;
x_50 = x_1226;
x_51 = x_1264;
x_52 = x_1227;
x_53 = x_1228;
x_54 = x_1229;
x_55 = x_1230;
x_56 = x_1231;
x_57 = x_1232;
x_58 = x_1233;
x_59 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
lean_dec(x_1238);
lean_dec(x_1233);
lean_dec_ref(x_1232);
lean_dec(x_1231);
lean_dec_ref(x_1230);
lean_dec_ref(x_1229);
lean_dec(x_1228);
lean_dec_ref(x_1227);
lean_dec_ref(x_1226);
lean_dec_ref(x_1);
x_1266 = lean_ctor_get(x_1263, 0);
lean_inc(x_1266);
if (lean_is_exclusive(x_1263)) {
 lean_ctor_release(x_1263, 0);
 x_1267 = x_1263;
} else {
 lean_dec_ref(x_1263);
 x_1267 = lean_box(0);
}
if (lean_is_scalar(x_1267)) {
 x_1268 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1268 = x_1267;
}
lean_ctor_set(x_1268, 0, x_1266);
return x_1268;
}
}
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; 
lean_dec(x_1233);
lean_dec_ref(x_1232);
lean_dec(x_1231);
lean_dec_ref(x_1230);
lean_dec_ref(x_1229);
lean_dec(x_1228);
lean_dec_ref(x_1227);
lean_dec_ref(x_1226);
lean_dec_ref(x_1225);
lean_dec_ref(x_1);
x_1269 = lean_ctor_get(x_1237, 0);
lean_inc(x_1269);
if (lean_is_exclusive(x_1237)) {
 lean_ctor_release(x_1237, 0);
 x_1270 = x_1237;
} else {
 lean_dec_ref(x_1237);
 x_1270 = lean_box(0);
}
if (lean_is_scalar(x_1270)) {
 x_1271 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1271 = x_1270;
}
lean_ctor_set(x_1271, 0, x_1269);
return x_1271;
}
}
}
else
{
lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; 
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
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1684 = lean_ctor_get(x_1223, 0);
lean_inc(x_1684);
if (lean_is_exclusive(x_1223)) {
 lean_ctor_release(x_1223, 0);
 x_1685 = x_1223;
} else {
 lean_dec_ref(x_1223);
 x_1685 = lean_box(0);
}
if (lean_is_scalar(x_1685)) {
 x_1686 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1686 = x_1685;
}
lean_ctor_set(x_1686, 0, x_1684);
return x_1686;
}
}
}
else
{
lean_object* x_1687; 
lean_dec_ref(x_1);
x_1687 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1687;
}
block_17:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_11);
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
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_20);
lean_dec_ref(x_19);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
}
block_48:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ptr_addr(x_30);
x_32 = lean_ptr_addr(x_26);
x_33 = lean_usize_dec_eq(x_31, x_32);
if (x_33 == 0)
{
x_10 = lean_box(0);
x_11 = x_26;
x_12 = x_27;
x_13 = x_33;
goto block_17;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_29);
x_35 = lean_ptr_addr(x_27);
x_36 = lean_usize_dec_eq(x_34, x_35);
x_10 = lean_box(0);
x_11 = x_26;
x_12 = x_27;
x_13 = x_36;
goto block_17;
}
}
case 2:
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ptr_addr(x_38);
x_40 = lean_ptr_addr(x_26);
x_41 = lean_usize_dec_eq(x_39, x_40);
if (x_41 == 0)
{
x_18 = lean_box(0);
x_19 = x_26;
x_20 = x_27;
x_21 = x_41;
goto block_25;
}
else
{
size_t x_42; size_t x_43; uint8_t x_44; 
x_42 = lean_ptr_addr(x_37);
x_43 = lean_ptr_addr(x_27);
x_44 = lean_usize_dec_eq(x_42, x_43);
x_18 = lean_box(0);
x_19 = x_26;
x_20 = x_27;
x_21 = x_44;
goto block_25;
}
}
default: 
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
x_45 = l_Lean_Compiler_LCNF_Simp_simp___closed__3;
x_46 = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2(x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
block_80:
{
lean_object* x_60; 
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc_ref(x_54);
lean_inc(x_53);
lean_inc_ref(x_52);
x_60 = l_Lean_Compiler_LCNF_Simp_simp(x_50, x_52, x_53, x_54, x_55, x_56, x_57, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_ctor_get(x_51, 0);
x_63 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_62, x_53);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec_ref(x_1);
x_66 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(x_51, x_53, x_56);
lean_dec(x_56);
lean_dec(x_53);
lean_dec_ref(x_51);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_61);
return x_66;
}
else
{
lean_object* x_69; 
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_61);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_61);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
if (x_49 == 0)
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
x_26 = x_61;
x_27 = x_51;
x_28 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_73; 
lean_inc_ref(x_51);
x_73 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
if (lean_obj_tag(x_73) == 0)
{
lean_dec_ref(x_73);
x_26 = x_61;
x_27 = x_51;
x_28 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_74; 
lean_dec(x_61);
lean_dec_ref(x_51);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
return x_73;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_63);
if (x_77 == 0)
{
return x_63;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_63, 0);
lean_inc(x_78);
lean_dec(x_63);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_1);
return x_60;
}
}
block_97:
{
lean_object* x_92; 
lean_inc(x_90);
lean_inc_ref(x_89);
lean_inc(x_88);
lean_inc_ref(x_87);
lean_inc_ref(x_86);
lean_inc(x_85);
lean_inc_ref(x_84);
x_92 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_49 = x_81;
x_50 = x_82;
x_51 = x_93;
x_52 = x_84;
x_53 = x_85;
x_54 = x_86;
x_55 = x_87;
x_56 = x_88;
x_57 = x_89;
x_58 = x_90;
x_59 = lean_box(0);
goto block_80;
}
else
{
uint8_t x_94; 
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_82);
lean_dec_ref(x_1);
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
block_105:
{
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_1);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_98);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
else
{
lean_object* x_104; 
lean_dec_ref(x_100);
lean_dec_ref(x_98);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_1);
return x_104;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_st_ref_get(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = 0;
lean_inc_ref(x_11);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_14, x_15, x_11);
lean_dec_ref(x_14);
lean_inc_ref(x_10);
x_17 = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16(x_15, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_6);
lean_inc_ref(x_12);
x_19 = l_Lean_Compiler_LCNF_Simp_simp(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_16, x_18, x_20, x_6);
lean_dec(x_6);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec_ref(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7_spec__8(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1, x_2, x_4, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_2, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1, x_2, x_3, x_4, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_1, x_2, x_3, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_2, x_3, x_4, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1, x_2, x_3, x_4, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_1, x_2, x_3, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_1, x_2, x_3, x_4, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18___redArg(x_1, x_2, x_3, x_5, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__18(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18___redArg(x_2, x_3, x_4, x_5);
return x_6;
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
l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0);
l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2);
l_Lean_Compiler_LCNF_Simp_simp___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__2);
l_Lean_Compiler_LCNF_Simp_simp___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__1);
l_Lean_Compiler_LCNF_Simp_simp___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__0);
l_Lean_Compiler_LCNF_Simp_simp___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__3);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
