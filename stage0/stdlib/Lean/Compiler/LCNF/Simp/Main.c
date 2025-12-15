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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(uint8_t, lean_object*, size_t, size_t);
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
lean_object* l_Lean_Compiler_LCNF_Alt_getParams(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqLetValue_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getCode(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0;
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_object* l_Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_5, x_6, x_11, x_12, x_13, x_14);
return x_16;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_3, x_4, x_5, x_6);
return x_15;
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
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_10, x_18, x_19, x_17);
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
x_29 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_27, x_28, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1, x_2, x_4);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_1, x_2, x_4, x_7);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2, x_3);
return x_5;
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1, x_2, x_3, x_5);
return x_12;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_2, x_3, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_1, x_2, x_3, x_4, x_9);
return x_13;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1, x_2, x_3, x_4, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_3, x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_array_uget(x_2, x_3);
x_19 = l_Lean_Compiler_LCNF_Alt_getParams(x_18);
lean_dec(x_18);
x_20 = lean_array_get_size(x_19);
x_21 = lean_box(0);
x_22 = lean_nat_dec_lt(x_1, x_20);
if (x_22 == 0)
{
lean_dec_ref(x_19);
x_11 = x_21;
x_12 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_20, x_20);
if (x_23 == 0)
{
lean_dec_ref(x_19);
x_11 = x_21;
x_12 = lean_box(0);
goto block_16;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_20);
x_26 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_19, x_24, x_25, x_21, x_7);
lean_dec_ref(x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_11 = x_27;
x_12 = lean_box(0);
goto block_16;
}
else
{
return x_26;
}
}
}
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_5);
return x_28;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12);
return x_14;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_1, x_2, x_3, x_5, x_8);
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_1, x_11, x_2, x_4, x_7);
return x_12;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
x_3 = lean_unsigned_to_nat(316u);
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
lean_inc(x_29);
lean_inc_ref(x_27);
lean_inc(x_36);
lean_inc_ref(x_37);
lean_inc_ref(x_34);
lean_inc(x_33);
lean_inc_ref(x_31);
x_39 = l_Lean_Compiler_LCNF_Simp_simp(x_35, x_31, x_33, x_34, x_37, x_36, x_27, x_29);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_33);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec_ref(x_41);
lean_inc(x_40);
x_42 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec_ref(x_28);
x_43 = l_Lean_Compiler_LCNF_inferAppType(x_20, x_30, x_37, x_36, x_27, x_29);
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
lean_dec(x_32);
x_47 = l_Lean_Compiler_LCNF_mkAuxParam(x_44, x_26, x_37, x_36, x_27, x_29);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_29);
lean_inc_ref(x_27);
lean_inc(x_36);
lean_inc_ref(x_37);
lean_inc(x_49);
x_50 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_24, x_23, x_11, x_2, x_21, x_49, x_31, x_33, x_34, x_37, x_36, x_27, x_29);
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
x_56 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_54, x_51, x_55, x_37, x_36, x_27, x_29);
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
x_59 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_58, x_37, x_36, x_27, x_29);
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
lean_dec(x_36);
lean_dec(x_29);
lean_dec_ref(x_27);
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
lean_dec(x_36);
lean_dec(x_29);
lean_dec_ref(x_27);
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
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_29);
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
x_80 = lean_mk_empty_array_with_capacity(x_32);
lean_dec(x_32);
x_81 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_82 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_80, x_40, x_81, x_37, x_36, x_27, x_29);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc(x_29);
lean_inc_ref(x_27);
lean_inc(x_36);
lean_inc_ref(x_37);
x_84 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_83, x_37, x_36, x_27, x_29);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_29);
lean_inc_ref(x_27);
lean_inc(x_36);
lean_inc_ref(x_37);
lean_inc_ref(x_34);
lean_inc(x_33);
lean_inc_ref(x_31);
lean_inc(x_86);
x_87 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_24, x_23, x_11, x_2, x_21, x_86, x_31, x_33, x_34, x_37, x_36, x_27, x_29);
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
x_92 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_91, x_88, x_31, x_33, x_34, x_37, x_36, x_27, x_29);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec(x_36);
lean_dec_ref(x_37);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
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
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_29);
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
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_29);
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
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_29);
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
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_29);
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
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_11);
lean_dec_ref(x_2);
x_114 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_28, x_37, x_36, x_27, x_29);
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
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
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
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
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
x_27 = x_136;
x_28 = x_144;
x_29 = x_137;
x_30 = x_141;
x_31 = x_131;
x_32 = x_139;
x_33 = x_132;
x_34 = x_133;
x_35 = x_143;
x_36 = x_135;
x_37 = x_134;
x_38 = lean_box(0);
goto block_130;
}
else
{
uint8_t x_146; 
x_146 = lean_nat_dec_eq(x_23, x_24);
if (x_146 == 0)
{
x_27 = x_136;
x_28 = x_144;
x_29 = x_137;
x_30 = x_141;
x_31 = x_131;
x_32 = x_139;
x_33 = x_132;
x_34 = x_133;
x_35 = x_143;
x_36 = x_135;
x_37 = x_134;
x_38 = lean_box(0);
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
lean_inc(x_223);
lean_inc_ref(x_221);
lean_inc(x_230);
lean_inc_ref(x_231);
lean_inc_ref(x_228);
lean_inc(x_227);
lean_inc_ref(x_225);
x_233 = l_Lean_Compiler_LCNF_Simp_simp(x_229, x_225, x_227, x_228, x_231, x_230, x_221, x_223);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
lean_dec_ref(x_233);
x_235 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_227);
if (lean_obj_tag(x_235) == 0)
{
uint8_t x_236; 
lean_dec_ref(x_235);
lean_inc(x_234);
x_236 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_234);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec_ref(x_222);
x_237 = l_Lean_Compiler_LCNF_inferAppType(x_214, x_224, x_231, x_230, x_221, x_223);
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
lean_dec(x_226);
x_241 = l_Lean_Compiler_LCNF_mkAuxParam(x_238, x_220, x_231, x_230, x_221, x_223);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
lean_dec_ref(x_241);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_223);
lean_inc_ref(x_221);
lean_inc(x_230);
lean_inc_ref(x_231);
lean_inc(x_243);
x_244 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_218, x_217, x_11, x_2, x_215, x_243, x_225, x_227, x_228, x_231, x_230, x_221, x_223);
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
x_250 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_248, x_245, x_249, x_231, x_230, x_221, x_223);
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
x_253 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_234, x_252, x_231, x_230, x_221, x_223);
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
lean_dec(x_230);
lean_dec(x_223);
lean_dec_ref(x_221);
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
lean_dec(x_230);
lean_dec(x_223);
lean_dec_ref(x_221);
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
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_223);
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
x_271 = lean_mk_empty_array_with_capacity(x_226);
lean_dec(x_226);
x_272 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_273 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_271, x_234, x_272, x_231, x_230, x_221, x_223);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
lean_dec_ref(x_273);
lean_inc(x_223);
lean_inc_ref(x_221);
lean_inc(x_230);
lean_inc_ref(x_231);
x_275 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_274, x_231, x_230, x_221, x_223);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec_ref(x_275);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_223);
lean_inc_ref(x_221);
lean_inc(x_230);
lean_inc_ref(x_231);
lean_inc_ref(x_228);
lean_inc(x_227);
lean_inc_ref(x_225);
lean_inc(x_277);
x_278 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_218, x_217, x_11, x_2, x_215, x_277, x_225, x_227, x_228, x_231, x_230, x_221, x_223);
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
x_283 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_282, x_279, x_225, x_227, x_228, x_231, x_230, x_221, x_223);
lean_dec(x_223);
lean_dec_ref(x_221);
lean_dec(x_230);
lean_dec_ref(x_231);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_225);
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
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_223);
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
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_223);
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
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_223);
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
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_223);
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
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec(x_218);
lean_dec_ref(x_215);
lean_dec_ref(x_214);
lean_dec(x_11);
lean_dec_ref(x_2);
x_303 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_234, x_222, x_231, x_230, x_221, x_223);
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
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
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
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
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
x_221 = x_323;
x_222 = x_331;
x_223 = x_324;
x_224 = x_328;
x_225 = x_318;
x_226 = x_326;
x_227 = x_319;
x_228 = x_320;
x_229 = x_330;
x_230 = x_322;
x_231 = x_321;
x_232 = lean_box(0);
goto block_317;
}
else
{
uint8_t x_333; 
x_333 = lean_nat_dec_eq(x_217, x_218);
if (x_333 == 0)
{
x_221 = x_323;
x_222 = x_331;
x_223 = x_324;
x_224 = x_328;
x_225 = x_318;
x_226 = x_326;
x_227 = x_319;
x_228 = x_320;
x_229 = x_330;
x_230 = x_322;
x_231 = x_321;
x_232 = lean_box(0);
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
lean_dec(x_10);
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
x_38 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_29, x_36, x_37, x_35, x_3);
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
x_83 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
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
x_126 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
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
x_179 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_170, x_177, x_178, x_176, x_3);
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
x_221 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
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
x_280 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_271, x_278, x_279, x_277, x_3);
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
x_322 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
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
x_389 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_380, x_387, x_388, x_386, x_3);
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
x_431 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; uint8_t x_122; 
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
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_349; 
lean_free_object(x_138);
x_191 = lean_ctor_get(x_1, 0);
x_192 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_191);
x_349 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_122, x_191, x_3, x_6);
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
lean_inc(x_198);
lean_inc_ref(x_193);
lean_inc(x_201);
lean_inc_ref(x_199);
lean_inc_ref(x_200);
x_203 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_200, x_199, x_201, x_193, x_198);
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
x_206 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_194);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
lean_dec_ref(x_206);
lean_inc(x_198);
lean_inc_ref(x_193);
lean_inc(x_201);
lean_inc_ref(x_199);
lean_inc_ref(x_196);
lean_inc(x_194);
lean_inc_ref(x_197);
x_207 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_197, x_194, x_196, x_199, x_201, x_193, x_198);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_205, x_208, x_197, x_194, x_196, x_199, x_201, x_193, x_198);
lean_dec(x_198);
lean_dec_ref(x_193);
lean_dec(x_201);
lean_dec_ref(x_199);
lean_dec_ref(x_196);
lean_dec(x_194);
lean_dec_ref(x_197);
lean_dec(x_205);
return x_209;
}
else
{
lean_dec(x_205);
lean_dec(x_201);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
lean_dec_ref(x_193);
return x_207;
}
}
else
{
uint8_t x_210; 
lean_dec(x_205);
lean_dec(x_201);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
lean_inc(x_198);
lean_inc_ref(x_193);
lean_inc(x_201);
lean_inc_ref(x_199);
lean_inc_ref(x_200);
x_213 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_200, x_197, x_194, x_199, x_201, x_193, x_198);
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
x_2 = x_197;
x_3 = x_194;
x_4 = x_196;
x_5 = x_199;
x_6 = x_201;
x_7 = x_193;
x_8 = x_198;
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
x_2 = x_197;
x_3 = x_194;
x_4 = x_196;
x_5 = x_199;
x_6 = x_201;
x_7 = x_193;
x_8 = x_198;
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
x_228 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_223, x_227, x_194, x_201, x_193, x_198);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
lean_dec_ref(x_228);
x_229 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_194, x_201);
lean_dec_ref(x_200);
if (lean_obj_tag(x_229) == 0)
{
lean_dec_ref(x_229);
x_1 = x_192;
x_2 = x_197;
x_3 = x_194;
x_4 = x_196;
x_5 = x_199;
x_6 = x_201;
x_7 = x_193;
x_8 = x_198;
goto _start;
}
else
{
uint8_t x_231; 
lean_dec(x_201);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
lean_inc(x_198);
lean_inc_ref(x_193);
lean_inc(x_201);
lean_inc_ref(x_199);
lean_inc_ref(x_196);
lean_inc(x_194);
lean_inc_ref(x_197);
lean_inc_ref(x_192);
lean_inc_ref(x_200);
x_237 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_200, x_192, x_197, x_194, x_196, x_199, x_201, x_193, x_198);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
if (lean_obj_tag(x_238) == 1)
{
lean_object* x_239; lean_object* x_240; 
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_194, x_201);
lean_dec(x_201);
lean_dec(x_194);
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
lean_inc(x_198);
lean_inc_ref(x_193);
lean_inc(x_201);
lean_inc_ref(x_199);
lean_inc_ref(x_196);
lean_inc(x_194);
lean_inc_ref(x_197);
lean_inc(x_224);
x_247 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_224, x_197, x_194, x_196, x_199, x_201, x_193, x_198);
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
x_252 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_223, x_251, x_194, x_201, x_193, x_198);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; 
lean_dec_ref(x_252);
x_253 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_194, x_201);
lean_dec_ref(x_200);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; 
lean_dec_ref(x_253);
lean_inc(x_198);
lean_inc_ref(x_193);
lean_inc(x_201);
lean_inc_ref(x_199);
lean_inc_ref(x_196);
lean_inc(x_194);
lean_inc_ref(x_197);
x_254 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_197, x_194, x_196, x_199, x_201, x_193, x_198);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_250, x_255, x_197, x_194, x_196, x_199, x_201, x_193, x_198);
lean_dec(x_198);
lean_dec_ref(x_193);
lean_dec(x_201);
lean_dec_ref(x_199);
lean_dec_ref(x_196);
lean_dec(x_194);
lean_dec_ref(x_197);
lean_dec(x_250);
return x_256;
}
else
{
lean_dec(x_250);
lean_dec(x_201);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
lean_dec_ref(x_193);
return x_254;
}
}
else
{
uint8_t x_257; 
lean_dec(x_250);
lean_dec(x_201);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
lean_inc(x_198);
lean_inc_ref(x_193);
lean_inc(x_201);
lean_inc_ref(x_199);
lean_inc_ref(x_196);
lean_inc(x_194);
lean_inc_ref(x_197);
lean_inc_ref(x_192);
x_263 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_197, x_194, x_196, x_199, x_201, x_193, x_198);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
x_265 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_223, x_194);
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
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_193);
lean_dec_ref(x_1);
x_268 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_194, x_201);
lean_dec(x_201);
lean_dec(x_194);
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
x_275 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_200, x_197, x_194, x_196, x_199, x_201, x_193, x_198);
lean_dec(x_198);
lean_dec_ref(x_193);
lean_dec(x_201);
lean_dec_ref(x_199);
lean_dec_ref(x_196);
lean_dec(x_194);
lean_dec_ref(x_197);
if (lean_obj_tag(x_275) == 0)
{
size_t x_276; size_t x_277; uint8_t x_278; 
lean_dec_ref(x_275);
x_276 = lean_ptr_addr(x_192);
x_277 = lean_ptr_addr(x_264);
x_278 = lean_usize_dec_eq(x_276, x_277);
if (x_278 == 0)
{
x_98 = x_200;
x_99 = lean_box(0);
x_100 = x_264;
x_101 = x_278;
goto block_105;
}
else
{
size_t x_279; size_t x_280; uint8_t x_281; 
x_279 = lean_ptr_addr(x_191);
x_280 = lean_ptr_addr(x_200);
x_281 = lean_usize_dec_eq(x_279, x_280);
x_98 = x_200;
x_99 = lean_box(0);
x_100 = x_264;
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
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
x_303 = lean_st_ref_take(x_194);
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
x_309 = lean_st_ref_set(x_194, x_303);
x_310 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_194, x_201);
lean_dec_ref(x_200);
if (lean_obj_tag(x_310) == 0)
{
lean_dec_ref(x_310);
x_1 = x_192;
x_2 = x_197;
x_3 = x_194;
x_4 = x_196;
x_5 = x_199;
x_6 = x_201;
x_7 = x_193;
x_8 = x_198;
goto _start;
}
else
{
uint8_t x_312; 
lean_dec(x_201);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
x_327 = lean_st_ref_set(x_194, x_326);
x_328 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_200, x_194, x_201);
lean_dec_ref(x_200);
if (lean_obj_tag(x_328) == 0)
{
lean_dec_ref(x_328);
x_1 = x_192;
x_2 = x_197;
x_3 = x_194;
x_4 = x_196;
x_5 = x_199;
x_6 = x_201;
x_7 = x_193;
x_8 = x_198;
goto _start;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_201);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec(x_194);
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
x_194 = x_338;
x_195 = lean_box(0);
x_196 = x_339;
x_197 = x_337;
x_198 = x_343;
x_199 = x_340;
x_200 = x_334;
x_201 = x_341;
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
x_194 = x_338;
x_195 = lean_box(0);
x_196 = x_339;
x_197 = x_337;
x_198 = x_343;
x_199 = x_340;
x_200 = x_334;
x_201 = x_341;
x_202 = x_345;
goto block_333;
}
else
{
x_193 = x_342;
x_194 = x_338;
x_195 = lean_box(0);
x_196 = x_339;
x_197 = x_337;
x_198 = x_343;
x_199 = x_340;
x_200 = x_334;
x_201 = x_341;
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
x_394 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_122, x_389, x_3);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_407; lean_object* x_413; 
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
x_413 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_393, x_395, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
lean_dec_ref(x_413);
if (lean_obj_tag(x_414) == 1)
{
lean_object* x_415; 
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_393);
lean_dec_ref(x_1);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
lean_dec_ref(x_414);
x_1 = x_415;
goto _start;
}
else
{
lean_object* x_417; 
lean_dec(x_414);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_393);
x_417 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_393, x_3);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; uint8_t x_420; 
lean_dec_ref(x_417);
x_418 = lean_unsigned_to_nat(0u);
x_419 = lean_array_get_size(x_395);
x_420 = lean_nat_dec_lt(x_418, x_419);
if (x_420 == 0)
{
lean_dec(x_3);
x_407 = lean_box(0);
goto block_412;
}
else
{
uint8_t x_421; 
x_421 = lean_nat_dec_le(x_419, x_419);
if (x_421 == 0)
{
lean_dec(x_3);
x_407 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_422; size_t x_423; size_t x_424; lean_object* x_425; 
x_422 = lean_box(0);
x_423 = 0;
x_424 = lean_usize_of_nat(x_419);
x_425 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_395, x_423, x_424, x_422, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_425) == 0)
{
lean_dec_ref(x_425);
x_407 = lean_box(0);
goto block_412;
}
else
{
uint8_t x_426; 
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_393);
lean_dec_ref(x_1);
x_426 = !lean_is_exclusive(x_425);
if (x_426 == 0)
{
return x_425;
}
else
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_425, 0);
lean_inc(x_427);
lean_dec(x_425);
x_428 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_428, 0, x_427);
return x_428;
}
}
}
}
}
else
{
uint8_t x_429; 
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_393);
lean_dec(x_3);
lean_dec_ref(x_1);
x_429 = !lean_is_exclusive(x_417);
if (x_429 == 0)
{
return x_417;
}
else
{
lean_object* x_430; lean_object* x_431; 
x_430 = lean_ctor_get(x_417, 0);
lean_inc(x_430);
lean_dec(x_417);
x_431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_431, 0, x_430);
return x_431;
}
}
}
}
else
{
uint8_t x_432; 
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
x_432 = !lean_is_exclusive(x_413);
if (x_432 == 0)
{
return x_413;
}
else
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_ctor_get(x_413, 0);
lean_inc(x_433);
lean_dec(x_413);
x_434 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_434, 0, x_433);
return x_434;
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
}
else
{
uint8_t x_435; 
lean_dec(x_393);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_435 = !lean_is_exclusive(x_394);
if (x_435 == 0)
{
return x_394;
}
else
{
lean_object* x_436; lean_object* x_437; 
x_436 = lean_ctor_get(x_394, 0);
lean_inc(x_436);
lean_dec(x_394);
x_437 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_437, 0, x_436);
return x_437;
}
}
}
else
{
lean_object* x_438; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_438 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_438;
}
}
case 4:
{
lean_object* x_439; lean_object* x_440; 
lean_free_object(x_138);
x_439 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_439);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_439);
x_440 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_439, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_440) == 0)
{
uint8_t x_441; 
x_441 = !lean_is_exclusive(x_440);
if (x_441 == 0)
{
lean_object* x_442; 
x_442 = lean_ctor_get(x_440, 0);
if (lean_obj_tag(x_442) == 1)
{
lean_object* x_443; 
lean_dec_ref(x_439);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
lean_dec_ref(x_442);
lean_ctor_set(x_440, 0, x_443);
return x_440;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_442);
x_444 = lean_st_ref_get(x_3);
x_445 = lean_ctor_get(x_439, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_439, 1);
lean_inc_ref(x_446);
x_447 = lean_ctor_get(x_439, 2);
lean_inc(x_447);
x_448 = lean_ctor_get(x_439, 3);
lean_inc_ref(x_448);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 lean_ctor_release(x_439, 2);
 lean_ctor_release(x_439, 3);
 x_449 = x_439;
} else {
 lean_dec_ref(x_439);
 x_449 = lean_box(0);
}
x_450 = lean_ctor_get(x_444, 0);
lean_inc_ref(x_450);
lean_dec(x_444);
lean_inc(x_447);
x_451 = l_Lean_Compiler_LCNF_normFVarImp(x_450, x_447, x_122);
lean_dec_ref(x_450);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 x_453 = x_451;
} else {
 lean_dec_ref(x_451);
 x_453 = lean_box(0);
}
x_454 = lean_st_ref_get(x_3);
x_455 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_448);
lean_inc(x_452);
x_456 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_452, x_122, x_455, x_448, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 x_458 = x_456;
} else {
 lean_dec_ref(x_456);
 x_458 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_459 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_457, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_493; lean_object* x_498; uint8_t x_499; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_525; uint8_t x_526; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 x_461 = x_459;
} else {
 lean_dec_ref(x_459);
 x_461 = lean_box(0);
}
x_462 = lean_ctor_get(x_454, 0);
lean_inc_ref(x_462);
lean_dec(x_454);
lean_inc_ref(x_446);
x_463 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_462, x_122, x_446);
lean_dec_ref(x_462);
x_525 = lean_array_get_size(x_460);
x_526 = lean_nat_dec_eq(x_525, x_189);
if (x_526 == 0)
{
lean_free_object(x_440);
x_503 = x_3;
x_504 = x_5;
x_505 = x_6;
x_506 = x_7;
x_507 = x_8;
x_508 = lean_box(0);
goto block_524;
}
else
{
lean_object* x_527; 
x_527 = lean_array_fget_borrowed(x_460, x_455);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_539; lean_object* x_540; uint8_t x_551; lean_object* x_552; uint8_t x_554; 
lean_free_object(x_440);
x_528 = lean_ctor_get(x_527, 1);
x_529 = lean_ctor_get(x_527, 2);
x_539 = lean_array_get_size(x_528);
x_554 = lean_nat_dec_lt(x_455, x_539);
if (x_554 == 0)
{
x_551 = x_122;
x_552 = lean_box(0);
goto block_553;
}
else
{
if (x_554 == 0)
{
x_551 = x_122;
x_552 = lean_box(0);
goto block_553;
}
else
{
size_t x_555; size_t x_556; lean_object* x_557; 
x_555 = 0;
x_556 = lean_usize_of_nat(x_539);
x_557 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_528, x_555, x_556, x_3);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; uint8_t x_559; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
lean_dec_ref(x_557);
x_559 = lean_unbox(x_558);
lean_dec(x_558);
x_551 = x_559;
x_552 = lean_box(0);
goto block_553;
}
else
{
uint8_t x_560; 
lean_dec_ref(x_463);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_458);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_560 = !lean_is_exclusive(x_557);
if (x_560 == 0)
{
return x_557;
}
else
{
lean_object* x_561; lean_object* x_562; 
x_561 = lean_ctor_get(x_557, 0);
lean_inc(x_561);
lean_dec(x_557);
x_562 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_562, 0, x_561);
return x_562;
}
}
}
}
block_538:
{
lean_object* x_531; 
x_531 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_531) == 0)
{
uint8_t x_532; 
x_532 = !lean_is_exclusive(x_531);
if (x_532 == 0)
{
lean_object* x_533; 
x_533 = lean_ctor_get(x_531, 0);
lean_dec(x_533);
lean_ctor_set(x_531, 0, x_529);
return x_531;
}
else
{
lean_object* x_534; 
lean_dec(x_531);
x_534 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_534, 0, x_529);
return x_534;
}
}
else
{
uint8_t x_535; 
lean_dec_ref(x_529);
x_535 = !lean_is_exclusive(x_531);
if (x_535 == 0)
{
return x_531;
}
else
{
lean_object* x_536; lean_object* x_537; 
x_536 = lean_ctor_get(x_531, 0);
lean_inc(x_536);
lean_dec(x_531);
x_537 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_537, 0, x_536);
return x_537;
}
}
}
block_550:
{
uint8_t x_541; 
x_541 = lean_nat_dec_lt(x_455, x_539);
if (x_541 == 0)
{
lean_dec_ref(x_528);
lean_dec(x_6);
x_530 = lean_box(0);
goto block_538;
}
else
{
uint8_t x_542; 
x_542 = lean_nat_dec_le(x_539, x_539);
if (x_542 == 0)
{
lean_dec_ref(x_528);
lean_dec(x_6);
x_530 = lean_box(0);
goto block_538;
}
else
{
lean_object* x_543; size_t x_544; size_t x_545; lean_object* x_546; 
x_543 = lean_box(0);
x_544 = 0;
x_545 = lean_usize_of_nat(x_539);
x_546 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_528, x_544, x_545, x_543, x_6);
lean_dec(x_6);
lean_dec_ref(x_528);
if (lean_obj_tag(x_546) == 0)
{
lean_dec_ref(x_546);
x_530 = lean_box(0);
goto block_538;
}
else
{
uint8_t x_547; 
lean_dec_ref(x_529);
lean_dec(x_3);
x_547 = !lean_is_exclusive(x_546);
if (x_547 == 0)
{
return x_546;
}
else
{
lean_object* x_548; lean_object* x_549; 
x_548 = lean_ctor_get(x_546, 0);
lean_inc(x_548);
lean_dec(x_546);
x_549 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_549, 0, x_548);
return x_549;
}
}
}
}
}
block_553:
{
if (x_551 == 0)
{
lean_inc_ref(x_529);
lean_inc_ref(x_528);
lean_dec_ref(x_463);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_458);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_540 = lean_box(0);
goto block_550;
}
else
{
if (x_122 == 0)
{
x_503 = x_3;
x_504 = x_5;
x_505 = x_6;
x_506 = x_7;
x_507 = x_8;
x_508 = lean_box(0);
goto block_524;
}
else
{
lean_inc_ref(x_529);
lean_inc_ref(x_528);
lean_dec_ref(x_463);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_458);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_540 = lean_box(0);
goto block_550;
}
}
}
}
else
{
lean_object* x_563; 
lean_inc_ref(x_527);
lean_dec_ref(x_463);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_458);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_563 = lean_ctor_get(x_527, 0);
lean_inc_ref(x_563);
lean_dec_ref(x_527);
lean_ctor_set(x_440, 0, x_563);
return x_440;
}
}
block_475:
{
lean_object* x_466; 
x_466 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_464);
lean_dec(x_464);
if (lean_obj_tag(x_466) == 0)
{
uint8_t x_467; 
x_467 = !lean_is_exclusive(x_466);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; 
x_468 = lean_ctor_get(x_466, 0);
lean_dec(x_468);
if (lean_is_scalar(x_453)) {
 x_469 = lean_alloc_ctor(6, 1, 0);
} else {
 x_469 = x_453;
 lean_ctor_set_tag(x_469, 6);
}
lean_ctor_set(x_469, 0, x_463);
lean_ctor_set(x_466, 0, x_469);
return x_466;
}
else
{
lean_object* x_470; lean_object* x_471; 
lean_dec(x_466);
if (lean_is_scalar(x_453)) {
 x_470 = lean_alloc_ctor(6, 1, 0);
} else {
 x_470 = x_453;
 lean_ctor_set_tag(x_470, 6);
}
lean_ctor_set(x_470, 0, x_463);
x_471 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_471, 0, x_470);
return x_471;
}
}
else
{
uint8_t x_472; 
lean_dec_ref(x_463);
lean_dec(x_453);
x_472 = !lean_is_exclusive(x_466);
if (x_472 == 0)
{
return x_466;
}
else
{
lean_object* x_473; lean_object* x_474; 
x_473 = lean_ctor_get(x_466, 0);
lean_inc(x_473);
lean_dec(x_466);
x_474 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_474, 0, x_473);
return x_474;
}
}
}
block_492:
{
uint8_t x_483; 
x_483 = lean_nat_dec_lt(x_455, x_476);
if (x_483 == 0)
{
lean_dec_ref(x_481);
lean_dec(x_479);
lean_dec(x_478);
lean_dec_ref(x_477);
lean_dec(x_476);
lean_dec(x_460);
x_464 = x_480;
x_465 = lean_box(0);
goto block_475;
}
else
{
uint8_t x_484; 
x_484 = lean_nat_dec_le(x_476, x_476);
if (x_484 == 0)
{
lean_dec_ref(x_481);
lean_dec(x_479);
lean_dec(x_478);
lean_dec_ref(x_477);
lean_dec(x_476);
lean_dec(x_460);
x_464 = x_480;
x_465 = lean_box(0);
goto block_475;
}
else
{
lean_object* x_485; size_t x_486; size_t x_487; lean_object* x_488; 
x_485 = lean_box(0);
x_486 = 0;
x_487 = lean_usize_of_nat(x_476);
lean_dec(x_476);
x_488 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_455, x_460, x_486, x_487, x_485, x_477, x_478, x_481, x_479);
lean_dec(x_479);
lean_dec_ref(x_481);
lean_dec(x_478);
lean_dec_ref(x_477);
lean_dec(x_460);
if (lean_obj_tag(x_488) == 0)
{
lean_dec_ref(x_488);
x_464 = x_480;
x_465 = lean_box(0);
goto block_475;
}
else
{
uint8_t x_489; 
lean_dec(x_480);
lean_dec_ref(x_463);
lean_dec(x_453);
x_489 = !lean_is_exclusive(x_488);
if (x_489 == 0)
{
return x_488;
}
else
{
lean_object* x_490; lean_object* x_491; 
x_490 = lean_ctor_get(x_488, 0);
lean_inc(x_490);
lean_dec(x_488);
x_491 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_491, 0, x_490);
return x_491;
}
}
}
}
}
block_497:
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
if (lean_is_scalar(x_449)) {
 x_494 = lean_alloc_ctor(0, 4, 0);
} else {
 x_494 = x_449;
}
lean_ctor_set(x_494, 0, x_445);
lean_ctor_set(x_494, 1, x_463);
lean_ctor_set(x_494, 2, x_452);
lean_ctor_set(x_494, 3, x_460);
x_495 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_495, 0, x_494);
if (lean_is_scalar(x_461)) {
 x_496 = lean_alloc_ctor(0, 1, 0);
} else {
 x_496 = x_461;
}
lean_ctor_set(x_496, 0, x_495);
return x_496;
}
block_502:
{
if (x_499 == 0)
{
lean_dec(x_458);
lean_dec(x_447);
lean_dec_ref(x_1);
x_493 = lean_box(0);
goto block_497;
}
else
{
uint8_t x_500; 
x_500 = l_Lean_instBEqFVarId_beq(x_447, x_452);
lean_dec(x_447);
if (x_500 == 0)
{
lean_dec(x_458);
lean_dec_ref(x_1);
x_493 = lean_box(0);
goto block_497;
}
else
{
lean_object* x_501; 
lean_dec_ref(x_463);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_452);
lean_dec(x_449);
lean_dec(x_445);
if (lean_is_scalar(x_458)) {
 x_501 = lean_alloc_ctor(0, 1, 0);
} else {
 x_501 = x_458;
}
lean_ctor_set(x_501, 0, x_1);
return x_501;
}
}
}
block_524:
{
lean_object* x_509; uint8_t x_510; 
x_509 = lean_array_get_size(x_460);
x_510 = lean_nat_dec_lt(x_455, x_509);
if (x_510 == 0)
{
lean_dec(x_461);
lean_dec(x_458);
lean_dec(x_452);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_1);
x_476 = x_509;
x_477 = x_504;
x_478 = x_505;
x_479 = x_507;
x_480 = x_503;
x_481 = x_506;
x_482 = lean_box(0);
goto block_492;
}
else
{
if (x_510 == 0)
{
lean_dec(x_461);
lean_dec(x_458);
lean_dec(x_452);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_1);
x_476 = x_509;
x_477 = x_504;
x_478 = x_505;
x_479 = x_507;
x_480 = x_503;
x_481 = x_506;
x_482 = lean_box(0);
goto block_492;
}
else
{
size_t x_511; size_t x_512; uint8_t x_513; 
x_511 = 0;
x_512 = lean_usize_of_nat(x_509);
x_513 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(x_122, x_460, x_511, x_512);
if (x_513 == 0)
{
lean_dec(x_461);
lean_dec(x_458);
lean_dec(x_452);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_1);
x_476 = x_509;
x_477 = x_504;
x_478 = x_505;
x_479 = x_507;
x_480 = x_503;
x_481 = x_506;
x_482 = lean_box(0);
goto block_492;
}
else
{
if (x_122 == 0)
{
lean_object* x_514; 
lean_dec(x_507);
lean_dec_ref(x_506);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_453);
lean_inc(x_452);
x_514 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_452, x_503);
lean_dec(x_503);
if (lean_obj_tag(x_514) == 0)
{
size_t x_515; size_t x_516; uint8_t x_517; 
lean_dec_ref(x_514);
x_515 = lean_ptr_addr(x_448);
lean_dec_ref(x_448);
x_516 = lean_ptr_addr(x_460);
x_517 = lean_usize_dec_eq(x_515, x_516);
if (x_517 == 0)
{
lean_dec_ref(x_446);
x_498 = lean_box(0);
x_499 = x_517;
goto block_502;
}
else
{
size_t x_518; size_t x_519; uint8_t x_520; 
x_518 = lean_ptr_addr(x_446);
lean_dec_ref(x_446);
x_519 = lean_ptr_addr(x_463);
x_520 = lean_usize_dec_eq(x_518, x_519);
x_498 = lean_box(0);
x_499 = x_520;
goto block_502;
}
}
else
{
uint8_t x_521; 
lean_dec_ref(x_463);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_458);
lean_dec(x_452);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_1);
x_521 = !lean_is_exclusive(x_514);
if (x_521 == 0)
{
return x_514;
}
else
{
lean_object* x_522; lean_object* x_523; 
x_522 = lean_ctor_get(x_514, 0);
lean_inc(x_522);
lean_dec(x_514);
x_523 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_523, 0, x_522);
return x_523;
}
}
}
else
{
lean_dec(x_461);
lean_dec(x_458);
lean_dec(x_452);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_1);
x_476 = x_509;
x_477 = x_504;
x_478 = x_505;
x_479 = x_507;
x_480 = x_503;
x_481 = x_506;
x_482 = lean_box(0);
goto block_492;
}
}
}
}
}
}
else
{
uint8_t x_564; 
lean_dec(x_458);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_free_object(x_440);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_564 = !lean_is_exclusive(x_459);
if (x_564 == 0)
{
return x_459;
}
else
{
lean_object* x_565; lean_object* x_566; 
x_565 = lean_ctor_get(x_459, 0);
lean_inc(x_565);
lean_dec(x_459);
x_566 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_566, 0, x_565);
return x_566;
}
}
}
else
{
uint8_t x_567; 
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_free_object(x_440);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_567 = !lean_is_exclusive(x_456);
if (x_567 == 0)
{
return x_456;
}
else
{
lean_object* x_568; lean_object* x_569; 
x_568 = lean_ctor_get(x_456, 0);
lean_inc(x_568);
lean_dec(x_456);
x_569 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_569, 0, x_568);
return x_569;
}
}
}
else
{
lean_object* x_570; 
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_free_object(x_440);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_570 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_570;
}
}
}
else
{
lean_object* x_571; 
x_571 = lean_ctor_get(x_440, 0);
lean_inc(x_571);
lean_dec(x_440);
if (lean_obj_tag(x_571) == 1)
{
lean_object* x_572; lean_object* x_573; 
lean_dec_ref(x_439);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec_ref(x_571);
x_573 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_573, 0, x_572);
return x_573;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec(x_571);
x_574 = lean_st_ref_get(x_3);
x_575 = lean_ctor_get(x_439, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_439, 1);
lean_inc_ref(x_576);
x_577 = lean_ctor_get(x_439, 2);
lean_inc(x_577);
x_578 = lean_ctor_get(x_439, 3);
lean_inc_ref(x_578);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 lean_ctor_release(x_439, 2);
 lean_ctor_release(x_439, 3);
 x_579 = x_439;
} else {
 lean_dec_ref(x_439);
 x_579 = lean_box(0);
}
x_580 = lean_ctor_get(x_574, 0);
lean_inc_ref(x_580);
lean_dec(x_574);
lean_inc(x_577);
x_581 = l_Lean_Compiler_LCNF_normFVarImp(x_580, x_577, x_122);
lean_dec_ref(x_580);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 x_583 = x_581;
} else {
 lean_dec_ref(x_581);
 x_583 = lean_box(0);
}
x_584 = lean_st_ref_get(x_3);
x_585 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_578);
lean_inc(x_582);
x_586 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_582, x_122, x_585, x_578, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 x_588 = x_586;
} else {
 lean_dec_ref(x_586);
 x_588 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_589 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_587, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_621; lean_object* x_626; uint8_t x_627; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_653; uint8_t x_654; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 x_591 = x_589;
} else {
 lean_dec_ref(x_589);
 x_591 = lean_box(0);
}
x_592 = lean_ctor_get(x_584, 0);
lean_inc_ref(x_592);
lean_dec(x_584);
lean_inc_ref(x_576);
x_593 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_592, x_122, x_576);
lean_dec_ref(x_592);
x_653 = lean_array_get_size(x_590);
x_654 = lean_nat_dec_eq(x_653, x_189);
if (x_654 == 0)
{
x_631 = x_3;
x_632 = x_5;
x_633 = x_6;
x_634 = x_7;
x_635 = x_8;
x_636 = lean_box(0);
goto block_652;
}
else
{
lean_object* x_655; 
x_655 = lean_array_fget_borrowed(x_590, x_585);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_666; lean_object* x_667; uint8_t x_678; lean_object* x_679; uint8_t x_681; 
x_656 = lean_ctor_get(x_655, 1);
x_657 = lean_ctor_get(x_655, 2);
x_666 = lean_array_get_size(x_656);
x_681 = lean_nat_dec_lt(x_585, x_666);
if (x_681 == 0)
{
x_678 = x_122;
x_679 = lean_box(0);
goto block_680;
}
else
{
if (x_681 == 0)
{
x_678 = x_122;
x_679 = lean_box(0);
goto block_680;
}
else
{
size_t x_682; size_t x_683; lean_object* x_684; 
x_682 = 0;
x_683 = lean_usize_of_nat(x_666);
x_684 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_656, x_682, x_683, x_3);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; uint8_t x_686; 
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
lean_dec_ref(x_684);
x_686 = lean_unbox(x_685);
lean_dec(x_685);
x_678 = x_686;
x_679 = lean_box(0);
goto block_680;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec_ref(x_593);
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_588);
lean_dec(x_583);
lean_dec(x_582);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_687 = lean_ctor_get(x_684, 0);
lean_inc(x_687);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 x_688 = x_684;
} else {
 lean_dec_ref(x_684);
 x_688 = lean_box(0);
}
if (lean_is_scalar(x_688)) {
 x_689 = lean_alloc_ctor(1, 1, 0);
} else {
 x_689 = x_688;
}
lean_ctor_set(x_689, 0, x_687);
return x_689;
}
}
}
block_665:
{
lean_object* x_659; 
x_659 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_659) == 0)
{
lean_object* x_660; lean_object* x_661; 
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 x_660 = x_659;
} else {
 lean_dec_ref(x_659);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(0, 1, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_657);
return x_661;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec_ref(x_657);
x_662 = lean_ctor_get(x_659, 0);
lean_inc(x_662);
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 x_663 = x_659;
} else {
 lean_dec_ref(x_659);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 1, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_662);
return x_664;
}
}
block_677:
{
uint8_t x_668; 
x_668 = lean_nat_dec_lt(x_585, x_666);
if (x_668 == 0)
{
lean_dec_ref(x_656);
lean_dec(x_6);
x_658 = lean_box(0);
goto block_665;
}
else
{
uint8_t x_669; 
x_669 = lean_nat_dec_le(x_666, x_666);
if (x_669 == 0)
{
lean_dec_ref(x_656);
lean_dec(x_6);
x_658 = lean_box(0);
goto block_665;
}
else
{
lean_object* x_670; size_t x_671; size_t x_672; lean_object* x_673; 
x_670 = lean_box(0);
x_671 = 0;
x_672 = lean_usize_of_nat(x_666);
x_673 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_656, x_671, x_672, x_670, x_6);
lean_dec(x_6);
lean_dec_ref(x_656);
if (lean_obj_tag(x_673) == 0)
{
lean_dec_ref(x_673);
x_658 = lean_box(0);
goto block_665;
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec_ref(x_657);
lean_dec(x_3);
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 x_675 = x_673;
} else {
 lean_dec_ref(x_673);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(1, 1, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_674);
return x_676;
}
}
}
}
block_680:
{
if (x_678 == 0)
{
lean_inc_ref(x_657);
lean_inc_ref(x_656);
lean_dec_ref(x_593);
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_588);
lean_dec(x_583);
lean_dec(x_582);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_667 = lean_box(0);
goto block_677;
}
else
{
if (x_122 == 0)
{
x_631 = x_3;
x_632 = x_5;
x_633 = x_6;
x_634 = x_7;
x_635 = x_8;
x_636 = lean_box(0);
goto block_652;
}
else
{
lean_inc_ref(x_657);
lean_inc_ref(x_656);
lean_dec_ref(x_593);
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_588);
lean_dec(x_583);
lean_dec(x_582);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_667 = lean_box(0);
goto block_677;
}
}
}
}
else
{
lean_object* x_690; lean_object* x_691; 
lean_inc_ref(x_655);
lean_dec_ref(x_593);
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_588);
lean_dec(x_583);
lean_dec(x_582);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_690 = lean_ctor_get(x_655, 0);
lean_inc_ref(x_690);
lean_dec_ref(x_655);
x_691 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_691, 0, x_690);
return x_691;
}
}
block_603:
{
lean_object* x_596; 
x_596 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_594);
lean_dec(x_594);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 x_597 = x_596;
} else {
 lean_dec_ref(x_596);
 x_597 = lean_box(0);
}
if (lean_is_scalar(x_583)) {
 x_598 = lean_alloc_ctor(6, 1, 0);
} else {
 x_598 = x_583;
 lean_ctor_set_tag(x_598, 6);
}
lean_ctor_set(x_598, 0, x_593);
if (lean_is_scalar(x_597)) {
 x_599 = lean_alloc_ctor(0, 1, 0);
} else {
 x_599 = x_597;
}
lean_ctor_set(x_599, 0, x_598);
return x_599;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec_ref(x_593);
lean_dec(x_583);
x_600 = lean_ctor_get(x_596, 0);
lean_inc(x_600);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 x_601 = x_596;
} else {
 lean_dec_ref(x_596);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(1, 1, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_600);
return x_602;
}
}
block_620:
{
uint8_t x_611; 
x_611 = lean_nat_dec_lt(x_585, x_604);
if (x_611 == 0)
{
lean_dec_ref(x_609);
lean_dec(x_607);
lean_dec(x_606);
lean_dec_ref(x_605);
lean_dec(x_604);
lean_dec(x_590);
x_594 = x_608;
x_595 = lean_box(0);
goto block_603;
}
else
{
uint8_t x_612; 
x_612 = lean_nat_dec_le(x_604, x_604);
if (x_612 == 0)
{
lean_dec_ref(x_609);
lean_dec(x_607);
lean_dec(x_606);
lean_dec_ref(x_605);
lean_dec(x_604);
lean_dec(x_590);
x_594 = x_608;
x_595 = lean_box(0);
goto block_603;
}
else
{
lean_object* x_613; size_t x_614; size_t x_615; lean_object* x_616; 
x_613 = lean_box(0);
x_614 = 0;
x_615 = lean_usize_of_nat(x_604);
lean_dec(x_604);
x_616 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_585, x_590, x_614, x_615, x_613, x_605, x_606, x_609, x_607);
lean_dec(x_607);
lean_dec_ref(x_609);
lean_dec(x_606);
lean_dec_ref(x_605);
lean_dec(x_590);
if (lean_obj_tag(x_616) == 0)
{
lean_dec_ref(x_616);
x_594 = x_608;
x_595 = lean_box(0);
goto block_603;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
lean_dec(x_608);
lean_dec_ref(x_593);
lean_dec(x_583);
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 x_618 = x_616;
} else {
 lean_dec_ref(x_616);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(1, 1, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_617);
return x_619;
}
}
}
}
block_625:
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
if (lean_is_scalar(x_579)) {
 x_622 = lean_alloc_ctor(0, 4, 0);
} else {
 x_622 = x_579;
}
lean_ctor_set(x_622, 0, x_575);
lean_ctor_set(x_622, 1, x_593);
lean_ctor_set(x_622, 2, x_582);
lean_ctor_set(x_622, 3, x_590);
x_623 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_623, 0, x_622);
if (lean_is_scalar(x_591)) {
 x_624 = lean_alloc_ctor(0, 1, 0);
} else {
 x_624 = x_591;
}
lean_ctor_set(x_624, 0, x_623);
return x_624;
}
block_630:
{
if (x_627 == 0)
{
lean_dec(x_588);
lean_dec(x_577);
lean_dec_ref(x_1);
x_621 = lean_box(0);
goto block_625;
}
else
{
uint8_t x_628; 
x_628 = l_Lean_instBEqFVarId_beq(x_577, x_582);
lean_dec(x_577);
if (x_628 == 0)
{
lean_dec(x_588);
lean_dec_ref(x_1);
x_621 = lean_box(0);
goto block_625;
}
else
{
lean_object* x_629; 
lean_dec_ref(x_593);
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_582);
lean_dec(x_579);
lean_dec(x_575);
if (lean_is_scalar(x_588)) {
 x_629 = lean_alloc_ctor(0, 1, 0);
} else {
 x_629 = x_588;
}
lean_ctor_set(x_629, 0, x_1);
return x_629;
}
}
}
block_652:
{
lean_object* x_637; uint8_t x_638; 
x_637 = lean_array_get_size(x_590);
x_638 = lean_nat_dec_lt(x_585, x_637);
if (x_638 == 0)
{
lean_dec(x_591);
lean_dec(x_588);
lean_dec(x_582);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_1);
x_604 = x_637;
x_605 = x_632;
x_606 = x_633;
x_607 = x_635;
x_608 = x_631;
x_609 = x_634;
x_610 = lean_box(0);
goto block_620;
}
else
{
if (x_638 == 0)
{
lean_dec(x_591);
lean_dec(x_588);
lean_dec(x_582);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_1);
x_604 = x_637;
x_605 = x_632;
x_606 = x_633;
x_607 = x_635;
x_608 = x_631;
x_609 = x_634;
x_610 = lean_box(0);
goto block_620;
}
else
{
size_t x_639; size_t x_640; uint8_t x_641; 
x_639 = 0;
x_640 = lean_usize_of_nat(x_637);
x_641 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(x_122, x_590, x_639, x_640);
if (x_641 == 0)
{
lean_dec(x_591);
lean_dec(x_588);
lean_dec(x_582);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_1);
x_604 = x_637;
x_605 = x_632;
x_606 = x_633;
x_607 = x_635;
x_608 = x_631;
x_609 = x_634;
x_610 = lean_box(0);
goto block_620;
}
else
{
if (x_122 == 0)
{
lean_object* x_642; 
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_632);
lean_dec(x_583);
lean_inc(x_582);
x_642 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_582, x_631);
lean_dec(x_631);
if (lean_obj_tag(x_642) == 0)
{
size_t x_643; size_t x_644; uint8_t x_645; 
lean_dec_ref(x_642);
x_643 = lean_ptr_addr(x_578);
lean_dec_ref(x_578);
x_644 = lean_ptr_addr(x_590);
x_645 = lean_usize_dec_eq(x_643, x_644);
if (x_645 == 0)
{
lean_dec_ref(x_576);
x_626 = lean_box(0);
x_627 = x_645;
goto block_630;
}
else
{
size_t x_646; size_t x_647; uint8_t x_648; 
x_646 = lean_ptr_addr(x_576);
lean_dec_ref(x_576);
x_647 = lean_ptr_addr(x_593);
x_648 = lean_usize_dec_eq(x_646, x_647);
x_626 = lean_box(0);
x_627 = x_648;
goto block_630;
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec_ref(x_593);
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_588);
lean_dec(x_582);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_1);
x_649 = lean_ctor_get(x_642, 0);
lean_inc(x_649);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 x_650 = x_642;
} else {
 lean_dec_ref(x_642);
 x_650 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_651 = lean_alloc_ctor(1, 1, 0);
} else {
 x_651 = x_650;
}
lean_ctor_set(x_651, 0, x_649);
return x_651;
}
}
else
{
lean_dec(x_591);
lean_dec(x_588);
lean_dec(x_582);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_1);
x_604 = x_637;
x_605 = x_632;
x_606 = x_633;
x_607 = x_635;
x_608 = x_631;
x_609 = x_634;
x_610 = lean_box(0);
goto block_620;
}
}
}
}
}
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_588);
lean_dec(x_584);
lean_dec(x_583);
lean_dec(x_582);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_692 = lean_ctor_get(x_589, 0);
lean_inc(x_692);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 x_693 = x_589;
} else {
 lean_dec_ref(x_589);
 x_693 = lean_box(0);
}
if (lean_is_scalar(x_693)) {
 x_694 = lean_alloc_ctor(1, 1, 0);
} else {
 x_694 = x_693;
}
lean_ctor_set(x_694, 0, x_692);
return x_694;
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
lean_dec(x_584);
lean_dec(x_583);
lean_dec(x_582);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_695 = lean_ctor_get(x_586, 0);
lean_inc(x_695);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 x_696 = x_586;
} else {
 lean_dec_ref(x_586);
 x_696 = lean_box(0);
}
if (lean_is_scalar(x_696)) {
 x_697 = lean_alloc_ctor(1, 1, 0);
} else {
 x_697 = x_696;
}
lean_ctor_set(x_697, 0, x_695);
return x_697;
}
}
else
{
lean_object* x_698; 
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_698 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_698;
}
}
}
}
else
{
uint8_t x_699; 
lean_dec_ref(x_439);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_699 = !lean_is_exclusive(x_440);
if (x_699 == 0)
{
return x_440;
}
else
{
lean_object* x_700; lean_object* x_701; 
x_700 = lean_ctor_get(x_440, 0);
lean_inc(x_700);
lean_dec(x_440);
x_701 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_701, 0, x_700);
return x_701;
}
}
}
case 5:
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_free_object(x_138);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_702 = lean_ctor_get(x_1, 0);
x_703 = lean_st_ref_get(x_3);
x_704 = lean_ctor_get(x_703, 0);
lean_inc_ref(x_704);
lean_dec(x_703);
lean_inc(x_702);
x_705 = l_Lean_Compiler_LCNF_normFVarImp(x_704, x_702, x_122);
lean_dec_ref(x_704);
if (lean_obj_tag(x_705) == 0)
{
lean_object* x_706; lean_object* x_707; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_706 = lean_ctor_get(x_705, 0);
lean_inc(x_706);
lean_dec_ref(x_705);
lean_inc(x_706);
x_707 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_706, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_707) == 0)
{
uint8_t x_708; 
x_708 = !lean_is_exclusive(x_707);
if (x_708 == 0)
{
lean_object* x_709; uint8_t x_710; 
x_709 = lean_ctor_get(x_707, 0);
lean_dec(x_709);
x_710 = l_Lean_instBEqFVarId_beq(x_702, x_706);
if (x_710 == 0)
{
uint8_t x_711; 
x_711 = !lean_is_exclusive(x_1);
if (x_711 == 0)
{
lean_object* x_712; 
x_712 = lean_ctor_get(x_1, 0);
lean_dec(x_712);
lean_ctor_set(x_1, 0, x_706);
lean_ctor_set(x_707, 0, x_1);
return x_707;
}
else
{
lean_object* x_713; 
lean_dec(x_1);
x_713 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_713, 0, x_706);
lean_ctor_set(x_707, 0, x_713);
return x_707;
}
}
else
{
lean_dec(x_706);
lean_ctor_set(x_707, 0, x_1);
return x_707;
}
}
else
{
uint8_t x_714; 
lean_dec(x_707);
x_714 = l_Lean_instBEqFVarId_beq(x_702, x_706);
if (x_714 == 0)
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_715 = x_1;
} else {
 lean_dec_ref(x_1);
 x_715 = lean_box(0);
}
if (lean_is_scalar(x_715)) {
 x_716 = lean_alloc_ctor(5, 1, 0);
} else {
 x_716 = x_715;
}
lean_ctor_set(x_716, 0, x_706);
x_717 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_717, 0, x_716);
return x_717;
}
else
{
lean_object* x_718; 
lean_dec(x_706);
x_718 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_718, 0, x_1);
return x_718;
}
}
}
else
{
uint8_t x_719; 
lean_dec(x_706);
lean_dec_ref(x_1);
x_719 = !lean_is_exclusive(x_707);
if (x_719 == 0)
{
return x_707;
}
else
{
lean_object* x_720; lean_object* x_721; 
x_720 = lean_ctor_get(x_707, 0);
lean_inc(x_720);
lean_dec(x_707);
x_721 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_721, 0, x_720);
return x_721;
}
}
}
else
{
lean_object* x_722; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_722 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_722;
}
}
case 6:
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; size_t x_727; size_t x_728; uint8_t x_729; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_723 = lean_ctor_get(x_1, 0);
x_724 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_725 = lean_ctor_get(x_724, 0);
lean_inc_ref(x_725);
lean_dec(x_724);
lean_inc_ref(x_723);
x_726 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_725, x_122, x_723);
lean_dec_ref(x_725);
x_727 = lean_ptr_addr(x_723);
x_728 = lean_ptr_addr(x_726);
x_729 = lean_usize_dec_eq(x_727, x_728);
if (x_729 == 0)
{
uint8_t x_730; 
x_730 = !lean_is_exclusive(x_1);
if (x_730 == 0)
{
lean_object* x_731; 
x_731 = lean_ctor_get(x_1, 0);
lean_dec(x_731);
lean_ctor_set(x_1, 0, x_726);
lean_ctor_set(x_138, 0, x_1);
return x_138;
}
else
{
lean_object* x_732; 
lean_dec(x_1);
x_732 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_732, 0, x_726);
lean_ctor_set(x_138, 0, x_732);
return x_138;
}
}
else
{
lean_dec_ref(x_726);
lean_ctor_set(x_138, 0, x_1);
return x_138;
}
}
default: 
{
lean_object* x_733; lean_object* x_734; 
lean_free_object(x_138);
x_733 = lean_ctor_get(x_1, 0);
x_734 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_734);
lean_inc_ref(x_733);
x_141 = x_733;
x_142 = x_734;
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
x_81 = x_142;
x_82 = x_157;
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
x_81 = x_142;
x_82 = x_159;
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
x_81 = x_142;
x_82 = x_167;
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
x_49 = x_142;
x_50 = x_181;
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
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_783; lean_object* x_784; 
lean_dec(x_138);
x_783 = lean_unsigned_to_nat(1u);
x_784 = lean_nat_add(x_109, x_783);
lean_dec(x_109);
lean_ctor_set(x_7, 3, x_784);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; uint8_t x_796; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_927; 
x_785 = lean_ctor_get(x_1, 0);
x_786 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_785);
x_927 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_122, x_785, x_3, x_6);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; uint8_t x_962; 
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
lean_dec_ref(x_927);
x_962 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_785, x_928);
if (x_962 == 0)
{
goto block_961;
}
else
{
if (x_122 == 0)
{
x_929 = x_2;
x_930 = x_3;
x_931 = x_4;
x_932 = x_5;
x_933 = x_6;
x_934 = x_7;
x_935 = x_8;
x_936 = lean_box(0);
goto block_956;
}
else
{
goto block_961;
}
}
block_956:
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; 
x_937 = lean_ctor_get(x_928, 2);
x_938 = lean_ctor_get(x_928, 3);
lean_inc(x_935);
lean_inc_ref(x_934);
lean_inc(x_933);
lean_inc_ref(x_932);
lean_inc_ref(x_931);
lean_inc(x_938);
x_939 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_938, x_929, x_931, x_932, x_933, x_934, x_935);
if (lean_obj_tag(x_939) == 0)
{
lean_object* x_940; 
x_940 = lean_ctor_get(x_939, 0);
lean_inc(x_940);
lean_dec_ref(x_939);
if (lean_obj_tag(x_940) == 1)
{
lean_object* x_941; lean_object* x_942; 
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
lean_dec_ref(x_940);
x_942 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_930);
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_943; 
lean_dec_ref(x_942);
x_943 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_928, x_941, x_933);
if (lean_obj_tag(x_943) == 0)
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; 
x_944 = lean_ctor_get(x_943, 0);
lean_inc(x_944);
lean_dec_ref(x_943);
x_945 = lean_ctor_get(x_944, 2);
lean_inc_ref(x_945);
x_946 = lean_ctor_get(x_944, 3);
lean_inc(x_946);
x_912 = x_944;
x_913 = x_945;
x_914 = x_946;
x_915 = x_929;
x_916 = x_930;
x_917 = x_931;
x_918 = x_932;
x_919 = x_933;
x_920 = x_934;
x_921 = x_935;
x_922 = lean_box(0);
goto block_926;
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; 
lean_dec(x_935);
lean_dec_ref(x_934);
lean_dec(x_933);
lean_dec_ref(x_932);
lean_dec_ref(x_931);
lean_dec(x_930);
lean_dec_ref(x_929);
lean_dec_ref(x_1);
x_947 = lean_ctor_get(x_943, 0);
lean_inc(x_947);
if (lean_is_exclusive(x_943)) {
 lean_ctor_release(x_943, 0);
 x_948 = x_943;
} else {
 lean_dec_ref(x_943);
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
lean_object* x_950; lean_object* x_951; lean_object* x_952; 
lean_dec(x_941);
lean_dec(x_935);
lean_dec_ref(x_934);
lean_dec(x_933);
lean_dec_ref(x_932);
lean_dec_ref(x_931);
lean_dec(x_930);
lean_dec_ref(x_929);
lean_dec(x_928);
lean_dec_ref(x_1);
x_950 = lean_ctor_get(x_942, 0);
lean_inc(x_950);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 x_951 = x_942;
} else {
 lean_dec_ref(x_942);
 x_951 = lean_box(0);
}
if (lean_is_scalar(x_951)) {
 x_952 = lean_alloc_ctor(1, 1, 0);
} else {
 x_952 = x_951;
}
lean_ctor_set(x_952, 0, x_950);
return x_952;
}
}
else
{
lean_dec(x_940);
lean_inc(x_938);
lean_inc_ref(x_937);
x_912 = x_928;
x_913 = x_937;
x_914 = x_938;
x_915 = x_929;
x_916 = x_930;
x_917 = x_931;
x_918 = x_932;
x_919 = x_933;
x_920 = x_934;
x_921 = x_935;
x_922 = lean_box(0);
goto block_926;
}
}
else
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; 
lean_dec(x_935);
lean_dec_ref(x_934);
lean_dec(x_933);
lean_dec_ref(x_932);
lean_dec_ref(x_931);
lean_dec(x_930);
lean_dec_ref(x_929);
lean_dec(x_928);
lean_dec_ref(x_1);
x_953 = lean_ctor_get(x_939, 0);
lean_inc(x_953);
if (lean_is_exclusive(x_939)) {
 lean_ctor_release(x_939, 0);
 x_954 = x_939;
} else {
 lean_dec_ref(x_939);
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
block_961:
{
lean_object* x_957; 
x_957 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_957) == 0)
{
lean_dec_ref(x_957);
x_929 = x_2;
x_930 = x_3;
x_931 = x_4;
x_932 = x_5;
x_933 = x_6;
x_934 = x_7;
x_935 = x_8;
x_936 = lean_box(0);
goto block_956;
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; 
lean_dec(x_928);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_958 = lean_ctor_get(x_957, 0);
lean_inc(x_958);
if (lean_is_exclusive(x_957)) {
 lean_ctor_release(x_957, 0);
 x_959 = x_957;
} else {
 lean_dec_ref(x_957);
 x_959 = lean_box(0);
}
if (lean_is_scalar(x_959)) {
 x_960 = lean_alloc_ctor(1, 1, 0);
} else {
 x_960 = x_959;
}
lean_ctor_set(x_960, 0, x_958);
return x_960;
}
}
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_963 = lean_ctor_get(x_927, 0);
lean_inc(x_963);
if (lean_is_exclusive(x_927)) {
 lean_ctor_release(x_927, 0);
 x_964 = x_927;
} else {
 lean_dec_ref(x_927);
 x_964 = lean_box(0);
}
if (lean_is_scalar(x_964)) {
 x_965 = lean_alloc_ctor(1, 1, 0);
} else {
 x_965 = x_964;
}
lean_ctor_set(x_965, 0, x_963);
return x_965;
}
block_911:
{
if (x_796 == 0)
{
lean_object* x_797; 
lean_inc(x_792);
lean_inc_ref(x_787);
lean_inc(x_795);
lean_inc_ref(x_793);
lean_inc_ref(x_794);
x_797 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_794, x_793, x_795, x_787, x_792);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; 
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
lean_dec_ref(x_797);
if (lean_obj_tag(x_798) == 1)
{
lean_object* x_799; lean_object* x_800; 
lean_dec_ref(x_794);
lean_inc_ref(x_786);
lean_dec_ref(x_1);
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
lean_dec_ref(x_798);
x_800 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_788);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_801; 
lean_dec_ref(x_800);
lean_inc(x_792);
lean_inc_ref(x_787);
lean_inc(x_795);
lean_inc_ref(x_793);
lean_inc_ref(x_790);
lean_inc(x_788);
lean_inc_ref(x_791);
x_801 = l_Lean_Compiler_LCNF_Simp_simp(x_786, x_791, x_788, x_790, x_793, x_795, x_787, x_792);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
lean_dec_ref(x_801);
x_803 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_799, x_802, x_791, x_788, x_790, x_793, x_795, x_787, x_792);
lean_dec(x_792);
lean_dec_ref(x_787);
lean_dec(x_795);
lean_dec_ref(x_793);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_791);
lean_dec(x_799);
return x_803;
}
else
{
lean_dec(x_799);
lean_dec(x_795);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
return x_801;
}
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
lean_dec(x_799);
lean_dec(x_795);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
x_804 = lean_ctor_get(x_800, 0);
lean_inc(x_804);
if (lean_is_exclusive(x_800)) {
 lean_ctor_release(x_800, 0);
 x_805 = x_800;
} else {
 lean_dec_ref(x_800);
 x_805 = lean_box(0);
}
if (lean_is_scalar(x_805)) {
 x_806 = lean_alloc_ctor(1, 1, 0);
} else {
 x_806 = x_805;
}
lean_ctor_set(x_806, 0, x_804);
return x_806;
}
}
else
{
lean_object* x_807; 
lean_dec(x_798);
lean_inc(x_792);
lean_inc_ref(x_787);
lean_inc(x_795);
lean_inc_ref(x_793);
lean_inc_ref(x_794);
x_807 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_794, x_791, x_788, x_793, x_795, x_787, x_792);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; 
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
lean_dec_ref(x_807);
if (lean_obj_tag(x_808) == 1)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec_ref(x_794);
lean_inc_ref(x_786);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_809 = x_1;
} else {
 lean_dec_ref(x_1);
 x_809 = lean_box(0);
}
x_810 = lean_ctor_get(x_808, 0);
lean_inc(x_810);
lean_dec_ref(x_808);
if (lean_is_scalar(x_809)) {
 x_811 = lean_alloc_ctor(1, 2, 0);
} else {
 x_811 = x_809;
 lean_ctor_set_tag(x_811, 1);
}
lean_ctor_set(x_811, 0, x_810);
lean_ctor_set(x_811, 1, x_786);
x_1 = x_811;
x_2 = x_791;
x_3 = x_788;
x_4 = x_790;
x_5 = x_793;
x_6 = x_795;
x_7 = x_787;
x_8 = x_792;
goto _start;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
lean_dec(x_808);
x_813 = lean_ctor_get(x_794, 0);
x_814 = lean_ctor_get(x_794, 3);
x_815 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_814);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
lean_dec_ref(x_815);
if (lean_obj_tag(x_816) == 1)
{
lean_object* x_817; lean_object* x_818; 
lean_inc_ref(x_786);
lean_dec_ref(x_1);
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
lean_dec_ref(x_816);
lean_inc(x_813);
x_818 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_813, x_817, x_788, x_795, x_787, x_792);
if (lean_obj_tag(x_818) == 0)
{
lean_object* x_819; 
lean_dec_ref(x_818);
x_819 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_794, x_788, x_795);
lean_dec_ref(x_794);
if (lean_obj_tag(x_819) == 0)
{
lean_dec_ref(x_819);
x_1 = x_786;
x_2 = x_791;
x_3 = x_788;
x_4 = x_790;
x_5 = x_793;
x_6 = x_795;
x_7 = x_787;
x_8 = x_792;
goto _start;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_dec(x_795);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
x_821 = lean_ctor_get(x_819, 0);
lean_inc(x_821);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 x_822 = x_819;
} else {
 lean_dec_ref(x_819);
 x_822 = lean_box(0);
}
if (lean_is_scalar(x_822)) {
 x_823 = lean_alloc_ctor(1, 1, 0);
} else {
 x_823 = x_822;
}
lean_ctor_set(x_823, 0, x_821);
return x_823;
}
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; 
lean_dec(x_795);
lean_dec_ref(x_794);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
x_824 = lean_ctor_get(x_818, 0);
lean_inc(x_824);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 x_825 = x_818;
} else {
 lean_dec_ref(x_818);
 x_825 = lean_box(0);
}
if (lean_is_scalar(x_825)) {
 x_826 = lean_alloc_ctor(1, 1, 0);
} else {
 x_826 = x_825;
}
lean_ctor_set(x_826, 0, x_824);
return x_826;
}
}
else
{
lean_object* x_827; 
lean_dec(x_816);
lean_inc(x_792);
lean_inc_ref(x_787);
lean_inc(x_795);
lean_inc_ref(x_793);
lean_inc_ref(x_790);
lean_inc(x_788);
lean_inc_ref(x_791);
lean_inc_ref(x_786);
lean_inc_ref(x_794);
x_827 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_794, x_786, x_791, x_788, x_790, x_793, x_795, x_787, x_792);
if (lean_obj_tag(x_827) == 0)
{
lean_object* x_828; 
x_828 = lean_ctor_get(x_827, 0);
lean_inc(x_828);
lean_dec_ref(x_827);
if (lean_obj_tag(x_828) == 1)
{
lean_object* x_829; lean_object* x_830; 
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec_ref(x_787);
lean_dec_ref(x_1);
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
lean_dec_ref(x_828);
x_830 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_794, x_788, x_795);
lean_dec(x_795);
lean_dec(x_788);
lean_dec_ref(x_794);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; 
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 x_831 = x_830;
} else {
 lean_dec_ref(x_830);
 x_831 = lean_box(0);
}
if (lean_is_scalar(x_831)) {
 x_832 = lean_alloc_ctor(0, 1, 0);
} else {
 x_832 = x_831;
}
lean_ctor_set(x_832, 0, x_829);
return x_832;
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; 
lean_dec(x_829);
x_833 = lean_ctor_get(x_830, 0);
lean_inc(x_833);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 x_834 = x_830;
} else {
 lean_dec_ref(x_830);
 x_834 = lean_box(0);
}
if (lean_is_scalar(x_834)) {
 x_835 = lean_alloc_ctor(1, 1, 0);
} else {
 x_835 = x_834;
}
lean_ctor_set(x_835, 0, x_833);
return x_835;
}
}
else
{
lean_object* x_836; 
lean_dec(x_828);
lean_inc(x_792);
lean_inc_ref(x_787);
lean_inc(x_795);
lean_inc_ref(x_793);
lean_inc_ref(x_790);
lean_inc(x_788);
lean_inc_ref(x_791);
lean_inc(x_814);
x_836 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_814, x_791, x_788, x_790, x_793, x_795, x_787, x_792);
if (lean_obj_tag(x_836) == 0)
{
lean_object* x_837; 
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
lean_dec_ref(x_836);
if (lean_obj_tag(x_837) == 1)
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
lean_inc_ref(x_786);
lean_dec_ref(x_1);
x_838 = lean_ctor_get(x_837, 0);
lean_inc(x_838);
lean_dec_ref(x_837);
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_838, 1);
lean_inc(x_840);
lean_dec(x_838);
lean_inc(x_813);
x_841 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_813, x_840, x_788, x_795, x_787, x_792);
if (lean_obj_tag(x_841) == 0)
{
lean_object* x_842; 
lean_dec_ref(x_841);
x_842 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_794, x_788, x_795);
lean_dec_ref(x_794);
if (lean_obj_tag(x_842) == 0)
{
lean_object* x_843; 
lean_dec_ref(x_842);
lean_inc(x_792);
lean_inc_ref(x_787);
lean_inc(x_795);
lean_inc_ref(x_793);
lean_inc_ref(x_790);
lean_inc(x_788);
lean_inc_ref(x_791);
x_843 = l_Lean_Compiler_LCNF_Simp_simp(x_786, x_791, x_788, x_790, x_793, x_795, x_787, x_792);
if (lean_obj_tag(x_843) == 0)
{
lean_object* x_844; lean_object* x_845; 
x_844 = lean_ctor_get(x_843, 0);
lean_inc(x_844);
lean_dec_ref(x_843);
x_845 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_839, x_844, x_791, x_788, x_790, x_793, x_795, x_787, x_792);
lean_dec(x_792);
lean_dec_ref(x_787);
lean_dec(x_795);
lean_dec_ref(x_793);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_791);
lean_dec(x_839);
return x_845;
}
else
{
lean_dec(x_839);
lean_dec(x_795);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
return x_843;
}
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
lean_dec(x_839);
lean_dec(x_795);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
x_846 = lean_ctor_get(x_842, 0);
lean_inc(x_846);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 x_847 = x_842;
} else {
 lean_dec_ref(x_842);
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
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_839);
lean_dec(x_795);
lean_dec_ref(x_794);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
x_849 = lean_ctor_get(x_841, 0);
lean_inc(x_849);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 x_850 = x_841;
} else {
 lean_dec_ref(x_841);
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
lean_dec(x_837);
lean_inc(x_792);
lean_inc_ref(x_787);
lean_inc(x_795);
lean_inc_ref(x_793);
lean_inc_ref(x_790);
lean_inc(x_788);
lean_inc_ref(x_791);
lean_inc_ref(x_786);
x_852 = l_Lean_Compiler_LCNF_Simp_simp(x_786, x_791, x_788, x_790, x_793, x_795, x_787, x_792);
if (lean_obj_tag(x_852) == 0)
{
lean_object* x_853; lean_object* x_854; 
x_853 = lean_ctor_get(x_852, 0);
lean_inc(x_853);
lean_dec_ref(x_852);
x_854 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_813, x_788);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; uint8_t x_856; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
lean_dec_ref(x_854);
x_856 = lean_unbox(x_855);
lean_dec(x_855);
if (x_856 == 0)
{
lean_object* x_857; 
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec_ref(x_787);
lean_dec_ref(x_1);
x_857 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_794, x_788, x_795);
lean_dec(x_795);
lean_dec(x_788);
lean_dec_ref(x_794);
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
lean_ctor_set(x_859, 0, x_853);
return x_859;
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_853);
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
lean_inc_ref(x_794);
x_863 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_794, x_791, x_788, x_790, x_793, x_795, x_787, x_792);
lean_dec(x_792);
lean_dec_ref(x_787);
lean_dec(x_795);
lean_dec_ref(x_793);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_791);
if (lean_obj_tag(x_863) == 0)
{
size_t x_864; size_t x_865; uint8_t x_866; 
lean_dec_ref(x_863);
x_864 = lean_ptr_addr(x_786);
x_865 = lean_ptr_addr(x_853);
x_866 = lean_usize_dec_eq(x_864, x_865);
if (x_866 == 0)
{
x_98 = x_794;
x_99 = lean_box(0);
x_100 = x_853;
x_101 = x_866;
goto block_105;
}
else
{
size_t x_867; size_t x_868; uint8_t x_869; 
x_867 = lean_ptr_addr(x_785);
x_868 = lean_ptr_addr(x_794);
x_869 = lean_usize_dec_eq(x_867, x_868);
x_98 = x_794;
x_99 = lean_box(0);
x_100 = x_853;
x_101 = x_869;
goto block_105;
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; 
lean_dec(x_853);
lean_dec_ref(x_794);
lean_dec_ref(x_1);
x_870 = lean_ctor_get(x_863, 0);
lean_inc(x_870);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 x_871 = x_863;
} else {
 lean_dec_ref(x_863);
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
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_dec(x_853);
lean_dec(x_795);
lean_dec_ref(x_794);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_1);
x_873 = lean_ctor_get(x_854, 0);
lean_inc(x_873);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 x_874 = x_854;
} else {
 lean_dec_ref(x_854);
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
lean_dec(x_795);
lean_dec_ref(x_794);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_1);
return x_852;
}
}
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
lean_dec(x_795);
lean_dec_ref(x_794);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_1);
x_876 = lean_ctor_get(x_836, 0);
lean_inc(x_876);
if (lean_is_exclusive(x_836)) {
 lean_ctor_release(x_836, 0);
 x_877 = x_836;
} else {
 lean_dec_ref(x_836);
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
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; 
lean_dec(x_795);
lean_dec_ref(x_794);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_1);
x_879 = lean_ctor_get(x_827, 0);
lean_inc(x_879);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 x_880 = x_827;
} else {
 lean_dec_ref(x_827);
 x_880 = lean_box(0);
}
if (lean_is_scalar(x_880)) {
 x_881 = lean_alloc_ctor(1, 1, 0);
} else {
 x_881 = x_880;
}
lean_ctor_set(x_881, 0, x_879);
return x_881;
}
}
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; 
lean_dec(x_795);
lean_dec_ref(x_794);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_1);
x_882 = lean_ctor_get(x_815, 0);
lean_inc(x_882);
if (lean_is_exclusive(x_815)) {
 lean_ctor_release(x_815, 0);
 x_883 = x_815;
} else {
 lean_dec_ref(x_815);
 x_883 = lean_box(0);
}
if (lean_is_scalar(x_883)) {
 x_884 = lean_alloc_ctor(1, 1, 0);
} else {
 x_884 = x_883;
}
lean_ctor_set(x_884, 0, x_882);
return x_884;
}
}
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; 
lean_dec(x_795);
lean_dec_ref(x_794);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_1);
x_885 = lean_ctor_get(x_807, 0);
lean_inc(x_885);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 x_886 = x_807;
} else {
 lean_dec_ref(x_807);
 x_886 = lean_box(0);
}
if (lean_is_scalar(x_886)) {
 x_887 = lean_alloc_ctor(1, 1, 0);
} else {
 x_887 = x_886;
}
lean_ctor_set(x_887, 0, x_885);
return x_887;
}
}
}
else
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_795);
lean_dec_ref(x_794);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_1);
x_888 = lean_ctor_get(x_797, 0);
lean_inc(x_888);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 x_889 = x_797;
} else {
 lean_dec_ref(x_797);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(1, 1, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_888);
return x_890;
}
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; uint8_t x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
lean_inc_ref(x_786);
lean_dec_ref(x_1);
x_891 = lean_st_ref_take(x_788);
x_892 = lean_ctor_get(x_794, 0);
x_893 = lean_ctor_get(x_891, 0);
lean_inc_ref(x_893);
x_894 = lean_ctor_get(x_891, 1);
lean_inc_ref(x_894);
x_895 = lean_ctor_get(x_891, 2);
lean_inc(x_895);
x_896 = lean_ctor_get(x_891, 3);
lean_inc_ref(x_896);
x_897 = lean_ctor_get_uint8(x_891, sizeof(void*)*7);
x_898 = lean_ctor_get(x_891, 4);
lean_inc(x_898);
x_899 = lean_ctor_get(x_891, 5);
lean_inc(x_899);
x_900 = lean_ctor_get(x_891, 6);
lean_inc(x_900);
if (lean_is_exclusive(x_891)) {
 lean_ctor_release(x_891, 0);
 lean_ctor_release(x_891, 1);
 lean_ctor_release(x_891, 2);
 lean_ctor_release(x_891, 3);
 lean_ctor_release(x_891, 4);
 lean_ctor_release(x_891, 5);
 lean_ctor_release(x_891, 6);
 x_901 = x_891;
} else {
 lean_dec_ref(x_891);
 x_901 = lean_box(0);
}
x_902 = lean_box(0);
lean_inc(x_892);
x_903 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_893, x_892, x_902);
if (lean_is_scalar(x_901)) {
 x_904 = lean_alloc_ctor(0, 7, 1);
} else {
 x_904 = x_901;
}
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_894);
lean_ctor_set(x_904, 2, x_895);
lean_ctor_set(x_904, 3, x_896);
lean_ctor_set(x_904, 4, x_898);
lean_ctor_set(x_904, 5, x_899);
lean_ctor_set(x_904, 6, x_900);
lean_ctor_set_uint8(x_904, sizeof(void*)*7, x_897);
x_905 = lean_st_ref_set(x_788, x_904);
x_906 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_794, x_788, x_795);
lean_dec_ref(x_794);
if (lean_obj_tag(x_906) == 0)
{
lean_dec_ref(x_906);
x_1 = x_786;
x_2 = x_791;
x_3 = x_788;
x_4 = x_790;
x_5 = x_793;
x_6 = x_795;
x_7 = x_787;
x_8 = x_792;
goto _start;
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_795);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_790);
lean_dec(x_788);
lean_dec_ref(x_787);
lean_dec_ref(x_786);
x_908 = lean_ctor_get(x_906, 0);
lean_inc(x_908);
if (lean_is_exclusive(x_906)) {
 lean_ctor_release(x_906, 0);
 x_909 = x_906;
} else {
 lean_dec_ref(x_906);
 x_909 = lean_box(0);
}
if (lean_is_scalar(x_909)) {
 x_910 = lean_alloc_ctor(1, 1, 0);
} else {
 x_910 = x_909;
}
lean_ctor_set(x_910, 0, x_908);
return x_910;
}
}
}
block_926:
{
uint8_t x_923; 
x_923 = l_Lean_Expr_isErased(x_913);
lean_dec_ref(x_913);
if (x_923 == 0)
{
lean_dec(x_914);
x_787 = x_920;
x_788 = x_916;
x_789 = lean_box(0);
x_790 = x_917;
x_791 = x_915;
x_792 = x_921;
x_793 = x_918;
x_794 = x_912;
x_795 = x_919;
x_796 = x_122;
goto block_911;
}
else
{
lean_object* x_924; uint8_t x_925; 
x_924 = lean_box(1);
x_925 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_914, x_924);
lean_dec(x_914);
if (x_925 == 0)
{
x_787 = x_920;
x_788 = x_916;
x_789 = lean_box(0);
x_790 = x_917;
x_791 = x_915;
x_792 = x_921;
x_793 = x_918;
x_794 = x_912;
x_795 = x_919;
x_796 = x_923;
goto block_911;
}
else
{
x_787 = x_920;
x_788 = x_916;
x_789 = lean_box(0);
x_790 = x_917;
x_791 = x_915;
x_792 = x_921;
x_793 = x_918;
x_794 = x_912;
x_795 = x_919;
x_796 = x_122;
goto block_911;
}
}
}
}
case 3:
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_966 = lean_ctor_get(x_1, 0);
x_967 = lean_ctor_get(x_1, 1);
x_968 = lean_st_ref_get(x_3);
x_969 = lean_ctor_get(x_968, 0);
lean_inc_ref(x_969);
lean_dec(x_968);
lean_inc(x_966);
x_970 = l_Lean_Compiler_LCNF_normFVarImp(x_969, x_966, x_122);
lean_dec_ref(x_969);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; lean_object* x_972; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
lean_dec_ref(x_970);
lean_inc_ref(x_967);
x_972 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_122, x_967, x_3);
if (lean_obj_tag(x_972) == 0)
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; uint8_t x_976; lean_object* x_982; lean_object* x_988; 
x_973 = lean_ctor_get(x_972, 0);
lean_inc(x_973);
if (lean_is_exclusive(x_972)) {
 lean_ctor_release(x_972, 0);
 x_974 = x_972;
} else {
 lean_dec_ref(x_972);
 x_974 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_973);
x_988 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_971, x_973, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_988) == 0)
{
lean_object* x_989; 
x_989 = lean_ctor_get(x_988, 0);
lean_inc(x_989);
lean_dec_ref(x_988);
if (lean_obj_tag(x_989) == 1)
{
lean_object* x_990; 
lean_dec(x_974);
lean_dec(x_973);
lean_dec(x_971);
lean_dec_ref(x_1);
x_990 = lean_ctor_get(x_989, 0);
lean_inc(x_990);
lean_dec_ref(x_989);
x_1 = x_990;
goto _start;
}
else
{
lean_object* x_992; 
lean_dec(x_989);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_971);
x_992 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_971, x_3);
if (lean_obj_tag(x_992) == 0)
{
lean_object* x_993; lean_object* x_994; uint8_t x_995; 
lean_dec_ref(x_992);
x_993 = lean_unsigned_to_nat(0u);
x_994 = lean_array_get_size(x_973);
x_995 = lean_nat_dec_lt(x_993, x_994);
if (x_995 == 0)
{
lean_dec(x_3);
x_982 = lean_box(0);
goto block_987;
}
else
{
uint8_t x_996; 
x_996 = lean_nat_dec_le(x_994, x_994);
if (x_996 == 0)
{
lean_dec(x_3);
x_982 = lean_box(0);
goto block_987;
}
else
{
lean_object* x_997; size_t x_998; size_t x_999; lean_object* x_1000; 
x_997 = lean_box(0);
x_998 = 0;
x_999 = lean_usize_of_nat(x_994);
x_1000 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_973, x_998, x_999, x_997, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1000) == 0)
{
lean_dec_ref(x_1000);
x_982 = lean_box(0);
goto block_987;
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; 
lean_dec(x_974);
lean_dec(x_973);
lean_dec(x_971);
lean_dec_ref(x_1);
x_1001 = lean_ctor_get(x_1000, 0);
lean_inc(x_1001);
if (lean_is_exclusive(x_1000)) {
 lean_ctor_release(x_1000, 0);
 x_1002 = x_1000;
} else {
 lean_dec_ref(x_1000);
 x_1002 = lean_box(0);
}
if (lean_is_scalar(x_1002)) {
 x_1003 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1003 = x_1002;
}
lean_ctor_set(x_1003, 0, x_1001);
return x_1003;
}
}
}
}
else
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_974);
lean_dec(x_973);
lean_dec(x_971);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1004 = lean_ctor_get(x_992, 0);
lean_inc(x_1004);
if (lean_is_exclusive(x_992)) {
 lean_ctor_release(x_992, 0);
 x_1005 = x_992;
} else {
 lean_dec_ref(x_992);
 x_1005 = lean_box(0);
}
if (lean_is_scalar(x_1005)) {
 x_1006 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1006 = x_1005;
}
lean_ctor_set(x_1006, 0, x_1004);
return x_1006;
}
}
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
lean_dec(x_974);
lean_dec(x_973);
lean_dec(x_971);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1007 = lean_ctor_get(x_988, 0);
lean_inc(x_1007);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 x_1008 = x_988;
} else {
 lean_dec_ref(x_988);
 x_1008 = lean_box(0);
}
if (lean_is_scalar(x_1008)) {
 x_1009 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1009 = x_1008;
}
lean_ctor_set(x_1009, 0, x_1007);
return x_1009;
}
block_981:
{
if (x_976 == 0)
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_977 = x_1;
} else {
 lean_dec_ref(x_1);
 x_977 = lean_box(0);
}
if (lean_is_scalar(x_977)) {
 x_978 = lean_alloc_ctor(3, 2, 0);
} else {
 x_978 = x_977;
}
lean_ctor_set(x_978, 0, x_971);
lean_ctor_set(x_978, 1, x_973);
if (lean_is_scalar(x_974)) {
 x_979 = lean_alloc_ctor(0, 1, 0);
} else {
 x_979 = x_974;
}
lean_ctor_set(x_979, 0, x_978);
return x_979;
}
else
{
lean_object* x_980; 
lean_dec(x_973);
lean_dec(x_971);
if (lean_is_scalar(x_974)) {
 x_980 = lean_alloc_ctor(0, 1, 0);
} else {
 x_980 = x_974;
}
lean_ctor_set(x_980, 0, x_1);
return x_980;
}
}
block_987:
{
uint8_t x_983; 
x_983 = l_Lean_instBEqFVarId_beq(x_966, x_971);
if (x_983 == 0)
{
x_975 = lean_box(0);
x_976 = x_983;
goto block_981;
}
else
{
size_t x_984; size_t x_985; uint8_t x_986; 
x_984 = lean_ptr_addr(x_967);
x_985 = lean_ptr_addr(x_973);
x_986 = lean_usize_dec_eq(x_984, x_985);
x_975 = lean_box(0);
x_976 = x_986;
goto block_981;
}
}
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
lean_dec(x_971);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1010 = lean_ctor_get(x_972, 0);
lean_inc(x_1010);
if (lean_is_exclusive(x_972)) {
 lean_ctor_release(x_972, 0);
 x_1011 = x_972;
} else {
 lean_dec_ref(x_972);
 x_1011 = lean_box(0);
}
if (lean_is_scalar(x_1011)) {
 x_1012 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1012 = x_1011;
}
lean_ctor_set(x_1012, 0, x_1010);
return x_1012;
}
}
else
{
lean_object* x_1013; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1013 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1013;
}
}
case 4:
{
lean_object* x_1014; lean_object* x_1015; 
x_1014 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1014);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1014);
x_1015 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1014, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1015) == 0)
{
lean_object* x_1016; lean_object* x_1017; 
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
if (lean_is_exclusive(x_1015)) {
 lean_ctor_release(x_1015, 0);
 x_1017 = x_1015;
} else {
 lean_dec_ref(x_1015);
 x_1017 = lean_box(0);
}
if (lean_obj_tag(x_1016) == 1)
{
lean_object* x_1018; lean_object* x_1019; 
lean_dec_ref(x_1014);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1018 = lean_ctor_get(x_1016, 0);
lean_inc(x_1018);
lean_dec_ref(x_1016);
if (lean_is_scalar(x_1017)) {
 x_1019 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1019 = x_1017;
}
lean_ctor_set(x_1019, 0, x_1018);
return x_1019;
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_1016);
x_1020 = lean_st_ref_get(x_3);
x_1021 = lean_ctor_get(x_1014, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1014, 1);
lean_inc_ref(x_1022);
x_1023 = lean_ctor_get(x_1014, 2);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1014, 3);
lean_inc_ref(x_1024);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 lean_ctor_release(x_1014, 1);
 lean_ctor_release(x_1014, 2);
 lean_ctor_release(x_1014, 3);
 x_1025 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1025 = lean_box(0);
}
x_1026 = lean_ctor_get(x_1020, 0);
lean_inc_ref(x_1026);
lean_dec(x_1020);
lean_inc(x_1023);
x_1027 = l_Lean_Compiler_LCNF_normFVarImp(x_1026, x_1023, x_122);
lean_dec_ref(x_1026);
if (lean_obj_tag(x_1027) == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
if (lean_is_exclusive(x_1027)) {
 lean_ctor_release(x_1027, 0);
 x_1029 = x_1027;
} else {
 lean_dec_ref(x_1027);
 x_1029 = lean_box(0);
}
x_1030 = lean_st_ref_get(x_3);
x_1031 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1024);
lean_inc(x_1028);
x_1032 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_1028, x_122, x_1031, x_1024, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
if (lean_is_exclusive(x_1032)) {
 lean_ctor_release(x_1032, 0);
 x_1034 = x_1032;
} else {
 lean_dec_ref(x_1032);
 x_1034 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_1035 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1033, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1035) == 0)
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1067; lean_object* x_1072; uint8_t x_1073; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1099; uint8_t x_1100; 
x_1036 = lean_ctor_get(x_1035, 0);
lean_inc(x_1036);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 x_1037 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1037 = lean_box(0);
}
x_1038 = lean_ctor_get(x_1030, 0);
lean_inc_ref(x_1038);
lean_dec(x_1030);
lean_inc_ref(x_1022);
x_1039 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1038, x_122, x_1022);
lean_dec_ref(x_1038);
x_1099 = lean_array_get_size(x_1036);
x_1100 = lean_nat_dec_eq(x_1099, x_783);
if (x_1100 == 0)
{
lean_dec(x_1017);
x_1077 = x_3;
x_1078 = x_5;
x_1079 = x_6;
x_1080 = x_7;
x_1081 = x_8;
x_1082 = lean_box(0);
goto block_1098;
}
else
{
lean_object* x_1101; 
x_1101 = lean_array_fget_borrowed(x_1036, x_1031);
if (lean_obj_tag(x_1101) == 0)
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1112; lean_object* x_1113; uint8_t x_1124; lean_object* x_1125; uint8_t x_1127; 
lean_dec(x_1017);
x_1102 = lean_ctor_get(x_1101, 1);
x_1103 = lean_ctor_get(x_1101, 2);
x_1112 = lean_array_get_size(x_1102);
x_1127 = lean_nat_dec_lt(x_1031, x_1112);
if (x_1127 == 0)
{
x_1124 = x_122;
x_1125 = lean_box(0);
goto block_1126;
}
else
{
if (x_1127 == 0)
{
x_1124 = x_122;
x_1125 = lean_box(0);
goto block_1126;
}
else
{
size_t x_1128; size_t x_1129; lean_object* x_1130; 
x_1128 = 0;
x_1129 = lean_usize_of_nat(x_1112);
x_1130 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1102, x_1128, x_1129, x_3);
if (lean_obj_tag(x_1130) == 0)
{
lean_object* x_1131; uint8_t x_1132; 
x_1131 = lean_ctor_get(x_1130, 0);
lean_inc(x_1131);
lean_dec_ref(x_1130);
x_1132 = lean_unbox(x_1131);
lean_dec(x_1131);
x_1124 = x_1132;
x_1125 = lean_box(0);
goto block_1126;
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
lean_dec_ref(x_1039);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1034);
lean_dec(x_1029);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1133 = lean_ctor_get(x_1130, 0);
lean_inc(x_1133);
if (lean_is_exclusive(x_1130)) {
 lean_ctor_release(x_1130, 0);
 x_1134 = x_1130;
} else {
 lean_dec_ref(x_1130);
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
}
block_1111:
{
lean_object* x_1105; 
x_1105 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1105) == 0)
{
lean_object* x_1106; lean_object* x_1107; 
if (lean_is_exclusive(x_1105)) {
 lean_ctor_release(x_1105, 0);
 x_1106 = x_1105;
} else {
 lean_dec_ref(x_1105);
 x_1106 = lean_box(0);
}
if (lean_is_scalar(x_1106)) {
 x_1107 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1107 = x_1106;
}
lean_ctor_set(x_1107, 0, x_1103);
return x_1107;
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
lean_dec_ref(x_1103);
x_1108 = lean_ctor_get(x_1105, 0);
lean_inc(x_1108);
if (lean_is_exclusive(x_1105)) {
 lean_ctor_release(x_1105, 0);
 x_1109 = x_1105;
} else {
 lean_dec_ref(x_1105);
 x_1109 = lean_box(0);
}
if (lean_is_scalar(x_1109)) {
 x_1110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1110 = x_1109;
}
lean_ctor_set(x_1110, 0, x_1108);
return x_1110;
}
}
block_1123:
{
uint8_t x_1114; 
x_1114 = lean_nat_dec_lt(x_1031, x_1112);
if (x_1114 == 0)
{
lean_dec_ref(x_1102);
lean_dec(x_6);
x_1104 = lean_box(0);
goto block_1111;
}
else
{
uint8_t x_1115; 
x_1115 = lean_nat_dec_le(x_1112, x_1112);
if (x_1115 == 0)
{
lean_dec_ref(x_1102);
lean_dec(x_6);
x_1104 = lean_box(0);
goto block_1111;
}
else
{
lean_object* x_1116; size_t x_1117; size_t x_1118; lean_object* x_1119; 
x_1116 = lean_box(0);
x_1117 = 0;
x_1118 = lean_usize_of_nat(x_1112);
x_1119 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_1102, x_1117, x_1118, x_1116, x_6);
lean_dec(x_6);
lean_dec_ref(x_1102);
if (lean_obj_tag(x_1119) == 0)
{
lean_dec_ref(x_1119);
x_1104 = lean_box(0);
goto block_1111;
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
lean_dec_ref(x_1103);
lean_dec(x_3);
x_1120 = lean_ctor_get(x_1119, 0);
lean_inc(x_1120);
if (lean_is_exclusive(x_1119)) {
 lean_ctor_release(x_1119, 0);
 x_1121 = x_1119;
} else {
 lean_dec_ref(x_1119);
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
}
}
block_1126:
{
if (x_1124 == 0)
{
lean_inc_ref(x_1103);
lean_inc_ref(x_1102);
lean_dec_ref(x_1039);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1034);
lean_dec(x_1029);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1113 = lean_box(0);
goto block_1123;
}
else
{
if (x_122 == 0)
{
x_1077 = x_3;
x_1078 = x_5;
x_1079 = x_6;
x_1080 = x_7;
x_1081 = x_8;
x_1082 = lean_box(0);
goto block_1098;
}
else
{
lean_inc_ref(x_1103);
lean_inc_ref(x_1102);
lean_dec_ref(x_1039);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1034);
lean_dec(x_1029);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1113 = lean_box(0);
goto block_1123;
}
}
}
}
else
{
lean_object* x_1136; lean_object* x_1137; 
lean_inc_ref(x_1101);
lean_dec_ref(x_1039);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1034);
lean_dec(x_1029);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1136 = lean_ctor_get(x_1101, 0);
lean_inc_ref(x_1136);
lean_dec_ref(x_1101);
if (lean_is_scalar(x_1017)) {
 x_1137 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1137 = x_1017;
}
lean_ctor_set(x_1137, 0, x_1136);
return x_1137;
}
}
block_1049:
{
lean_object* x_1042; 
x_1042 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1040);
lean_dec(x_1040);
if (lean_obj_tag(x_1042) == 0)
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
if (lean_is_exclusive(x_1042)) {
 lean_ctor_release(x_1042, 0);
 x_1043 = x_1042;
} else {
 lean_dec_ref(x_1042);
 x_1043 = lean_box(0);
}
if (lean_is_scalar(x_1029)) {
 x_1044 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1044 = x_1029;
 lean_ctor_set_tag(x_1044, 6);
}
lean_ctor_set(x_1044, 0, x_1039);
if (lean_is_scalar(x_1043)) {
 x_1045 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1045 = x_1043;
}
lean_ctor_set(x_1045, 0, x_1044);
return x_1045;
}
else
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
lean_dec_ref(x_1039);
lean_dec(x_1029);
x_1046 = lean_ctor_get(x_1042, 0);
lean_inc(x_1046);
if (lean_is_exclusive(x_1042)) {
 lean_ctor_release(x_1042, 0);
 x_1047 = x_1042;
} else {
 lean_dec_ref(x_1042);
 x_1047 = lean_box(0);
}
if (lean_is_scalar(x_1047)) {
 x_1048 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1048 = x_1047;
}
lean_ctor_set(x_1048, 0, x_1046);
return x_1048;
}
}
block_1066:
{
uint8_t x_1057; 
x_1057 = lean_nat_dec_lt(x_1031, x_1050);
if (x_1057 == 0)
{
lean_dec_ref(x_1055);
lean_dec(x_1053);
lean_dec(x_1052);
lean_dec_ref(x_1051);
lean_dec(x_1050);
lean_dec(x_1036);
x_1040 = x_1054;
x_1041 = lean_box(0);
goto block_1049;
}
else
{
uint8_t x_1058; 
x_1058 = lean_nat_dec_le(x_1050, x_1050);
if (x_1058 == 0)
{
lean_dec_ref(x_1055);
lean_dec(x_1053);
lean_dec(x_1052);
lean_dec_ref(x_1051);
lean_dec(x_1050);
lean_dec(x_1036);
x_1040 = x_1054;
x_1041 = lean_box(0);
goto block_1049;
}
else
{
lean_object* x_1059; size_t x_1060; size_t x_1061; lean_object* x_1062; 
x_1059 = lean_box(0);
x_1060 = 0;
x_1061 = lean_usize_of_nat(x_1050);
lean_dec(x_1050);
x_1062 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1031, x_1036, x_1060, x_1061, x_1059, x_1051, x_1052, x_1055, x_1053);
lean_dec(x_1053);
lean_dec_ref(x_1055);
lean_dec(x_1052);
lean_dec_ref(x_1051);
lean_dec(x_1036);
if (lean_obj_tag(x_1062) == 0)
{
lean_dec_ref(x_1062);
x_1040 = x_1054;
x_1041 = lean_box(0);
goto block_1049;
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_1054);
lean_dec_ref(x_1039);
lean_dec(x_1029);
x_1063 = lean_ctor_get(x_1062, 0);
lean_inc(x_1063);
if (lean_is_exclusive(x_1062)) {
 lean_ctor_release(x_1062, 0);
 x_1064 = x_1062;
} else {
 lean_dec_ref(x_1062);
 x_1064 = lean_box(0);
}
if (lean_is_scalar(x_1064)) {
 x_1065 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1065 = x_1064;
}
lean_ctor_set(x_1065, 0, x_1063);
return x_1065;
}
}
}
}
block_1071:
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
if (lean_is_scalar(x_1025)) {
 x_1068 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1068 = x_1025;
}
lean_ctor_set(x_1068, 0, x_1021);
lean_ctor_set(x_1068, 1, x_1039);
lean_ctor_set(x_1068, 2, x_1028);
lean_ctor_set(x_1068, 3, x_1036);
x_1069 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1069, 0, x_1068);
if (lean_is_scalar(x_1037)) {
 x_1070 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1070 = x_1037;
}
lean_ctor_set(x_1070, 0, x_1069);
return x_1070;
}
block_1076:
{
if (x_1073 == 0)
{
lean_dec(x_1034);
lean_dec(x_1023);
lean_dec_ref(x_1);
x_1067 = lean_box(0);
goto block_1071;
}
else
{
uint8_t x_1074; 
x_1074 = l_Lean_instBEqFVarId_beq(x_1023, x_1028);
lean_dec(x_1023);
if (x_1074 == 0)
{
lean_dec(x_1034);
lean_dec_ref(x_1);
x_1067 = lean_box(0);
goto block_1071;
}
else
{
lean_object* x_1075; 
lean_dec_ref(x_1039);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec(x_1021);
if (lean_is_scalar(x_1034)) {
 x_1075 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1075 = x_1034;
}
lean_ctor_set(x_1075, 0, x_1);
return x_1075;
}
}
}
block_1098:
{
lean_object* x_1083; uint8_t x_1084; 
x_1083 = lean_array_get_size(x_1036);
x_1084 = lean_nat_dec_lt(x_1031, x_1083);
if (x_1084 == 0)
{
lean_dec(x_1037);
lean_dec(x_1034);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec_ref(x_1);
x_1050 = x_1083;
x_1051 = x_1078;
x_1052 = x_1079;
x_1053 = x_1081;
x_1054 = x_1077;
x_1055 = x_1080;
x_1056 = lean_box(0);
goto block_1066;
}
else
{
if (x_1084 == 0)
{
lean_dec(x_1037);
lean_dec(x_1034);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec_ref(x_1);
x_1050 = x_1083;
x_1051 = x_1078;
x_1052 = x_1079;
x_1053 = x_1081;
x_1054 = x_1077;
x_1055 = x_1080;
x_1056 = lean_box(0);
goto block_1066;
}
else
{
size_t x_1085; size_t x_1086; uint8_t x_1087; 
x_1085 = 0;
x_1086 = lean_usize_of_nat(x_1083);
x_1087 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(x_122, x_1036, x_1085, x_1086);
if (x_1087 == 0)
{
lean_dec(x_1037);
lean_dec(x_1034);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec_ref(x_1);
x_1050 = x_1083;
x_1051 = x_1078;
x_1052 = x_1079;
x_1053 = x_1081;
x_1054 = x_1077;
x_1055 = x_1080;
x_1056 = lean_box(0);
goto block_1066;
}
else
{
if (x_122 == 0)
{
lean_object* x_1088; 
lean_dec(x_1081);
lean_dec_ref(x_1080);
lean_dec(x_1079);
lean_dec_ref(x_1078);
lean_dec(x_1029);
lean_inc(x_1028);
x_1088 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1028, x_1077);
lean_dec(x_1077);
if (lean_obj_tag(x_1088) == 0)
{
size_t x_1089; size_t x_1090; uint8_t x_1091; 
lean_dec_ref(x_1088);
x_1089 = lean_ptr_addr(x_1024);
lean_dec_ref(x_1024);
x_1090 = lean_ptr_addr(x_1036);
x_1091 = lean_usize_dec_eq(x_1089, x_1090);
if (x_1091 == 0)
{
lean_dec_ref(x_1022);
x_1072 = lean_box(0);
x_1073 = x_1091;
goto block_1076;
}
else
{
size_t x_1092; size_t x_1093; uint8_t x_1094; 
x_1092 = lean_ptr_addr(x_1022);
lean_dec_ref(x_1022);
x_1093 = lean_ptr_addr(x_1039);
x_1094 = lean_usize_dec_eq(x_1092, x_1093);
x_1072 = lean_box(0);
x_1073 = x_1094;
goto block_1076;
}
}
else
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
lean_dec_ref(x_1039);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1034);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec_ref(x_1);
x_1095 = lean_ctor_get(x_1088, 0);
lean_inc(x_1095);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 x_1096 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1096 = lean_box(0);
}
if (lean_is_scalar(x_1096)) {
 x_1097 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1097 = x_1096;
}
lean_ctor_set(x_1097, 0, x_1095);
return x_1097;
}
}
else
{
lean_dec(x_1037);
lean_dec(x_1034);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec_ref(x_1);
x_1050 = x_1083;
x_1051 = x_1078;
x_1052 = x_1079;
x_1053 = x_1081;
x_1054 = x_1077;
x_1055 = x_1080;
x_1056 = lean_box(0);
goto block_1066;
}
}
}
}
}
}
else
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
lean_dec(x_1034);
lean_dec(x_1030);
lean_dec(x_1029);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec(x_1017);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1138 = lean_ctor_get(x_1035, 0);
lean_inc(x_1138);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 x_1139 = x_1035;
} else {
 lean_dec_ref(x_1035);
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
else
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
lean_dec(x_1030);
lean_dec(x_1029);
lean_dec(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec(x_1017);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1141 = lean_ctor_get(x_1032, 0);
lean_inc(x_1141);
if (lean_is_exclusive(x_1032)) {
 lean_ctor_release(x_1032, 0);
 x_1142 = x_1032;
} else {
 lean_dec_ref(x_1032);
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
lean_object* x_1144; 
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec_ref(x_1022);
lean_dec(x_1021);
lean_dec(x_1017);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1144 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1144;
}
}
}
else
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
lean_dec_ref(x_1014);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1145 = lean_ctor_get(x_1015, 0);
lean_inc(x_1145);
if (lean_is_exclusive(x_1015)) {
 lean_ctor_release(x_1015, 0);
 x_1146 = x_1015;
} else {
 lean_dec_ref(x_1015);
 x_1146 = lean_box(0);
}
if (lean_is_scalar(x_1146)) {
 x_1147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1147 = x_1146;
}
lean_ctor_set(x_1147, 0, x_1145);
return x_1147;
}
}
case 5:
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1148 = lean_ctor_get(x_1, 0);
x_1149 = lean_st_ref_get(x_3);
x_1150 = lean_ctor_get(x_1149, 0);
lean_inc_ref(x_1150);
lean_dec(x_1149);
lean_inc(x_1148);
x_1151 = l_Lean_Compiler_LCNF_normFVarImp(x_1150, x_1148, x_122);
lean_dec_ref(x_1150);
if (lean_obj_tag(x_1151) == 0)
{
lean_object* x_1152; lean_object* x_1153; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1152 = lean_ctor_get(x_1151, 0);
lean_inc(x_1152);
lean_dec_ref(x_1151);
lean_inc(x_1152);
x_1153 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1152, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1153) == 0)
{
lean_object* x_1154; uint8_t x_1155; 
if (lean_is_exclusive(x_1153)) {
 lean_ctor_release(x_1153, 0);
 x_1154 = x_1153;
} else {
 lean_dec_ref(x_1153);
 x_1154 = lean_box(0);
}
x_1155 = l_Lean_instBEqFVarId_beq(x_1148, x_1152);
if (x_1155 == 0)
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1156 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1156 = lean_box(0);
}
if (lean_is_scalar(x_1156)) {
 x_1157 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1157 = x_1156;
}
lean_ctor_set(x_1157, 0, x_1152);
if (lean_is_scalar(x_1154)) {
 x_1158 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1158 = x_1154;
}
lean_ctor_set(x_1158, 0, x_1157);
return x_1158;
}
else
{
lean_object* x_1159; 
lean_dec(x_1152);
if (lean_is_scalar(x_1154)) {
 x_1159 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1159 = x_1154;
}
lean_ctor_set(x_1159, 0, x_1);
return x_1159;
}
}
else
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
lean_dec(x_1152);
lean_dec_ref(x_1);
x_1160 = lean_ctor_get(x_1153, 0);
lean_inc(x_1160);
if (lean_is_exclusive(x_1153)) {
 lean_ctor_release(x_1153, 0);
 x_1161 = x_1153;
} else {
 lean_dec_ref(x_1153);
 x_1161 = lean_box(0);
}
if (lean_is_scalar(x_1161)) {
 x_1162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1162 = x_1161;
}
lean_ctor_set(x_1162, 0, x_1160);
return x_1162;
}
}
else
{
lean_object* x_1163; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1163 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1163;
}
}
case 6:
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; size_t x_1168; size_t x_1169; uint8_t x_1170; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1164 = lean_ctor_get(x_1, 0);
x_1165 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_1166 = lean_ctor_get(x_1165, 0);
lean_inc_ref(x_1166);
lean_dec(x_1165);
lean_inc_ref(x_1164);
x_1167 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1166, x_122, x_1164);
lean_dec_ref(x_1166);
x_1168 = lean_ptr_addr(x_1164);
x_1169 = lean_ptr_addr(x_1167);
x_1170 = lean_usize_dec_eq(x_1168, x_1169);
if (x_1170 == 0)
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1171 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1171 = lean_box(0);
}
if (lean_is_scalar(x_1171)) {
 x_1172 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1172 = x_1171;
}
lean_ctor_set(x_1172, 0, x_1167);
x_1173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1173, 0, x_1172);
return x_1173;
}
else
{
lean_object* x_1174; 
lean_dec_ref(x_1167);
x_1174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1174, 0, x_1);
return x_1174;
}
}
default: 
{
lean_object* x_1175; lean_object* x_1176; 
x_1175 = lean_ctor_get(x_1, 0);
x_1176 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1176);
lean_inc_ref(x_1175);
x_735 = x_1175;
x_736 = x_1176;
x_737 = x_2;
x_738 = x_3;
x_739 = x_4;
x_740 = x_5;
x_741 = x_6;
x_742 = x_7;
x_743 = x_8;
goto block_782;
}
}
block_782:
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_744 = lean_ctor_get(x_735, 0);
x_745 = lean_ctor_get(x_735, 2);
x_746 = lean_ctor_get(x_735, 3);
x_747 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_744, x_738);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; uint8_t x_749; 
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
lean_dec_ref(x_747);
x_749 = lean_unbox(x_748);
if (x_749 == 0)
{
uint8_t x_750; 
x_750 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
if (x_750 == 0)
{
uint8_t x_751; 
x_751 = lean_unbox(x_748);
lean_dec(x_748);
x_81 = x_736;
x_82 = x_751;
x_83 = x_735;
x_84 = x_737;
x_85 = x_738;
x_86 = x_739;
x_87 = x_740;
x_88 = x_741;
x_89 = x_742;
x_90 = x_743;
x_91 = lean_box(0);
goto block_97;
}
else
{
uint8_t x_752; 
lean_inc_ref(x_746);
x_752 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_746, x_745);
if (x_752 == 0)
{
uint8_t x_753; 
x_753 = lean_unbox(x_748);
lean_dec(x_748);
x_81 = x_736;
x_82 = x_753;
x_83 = x_735;
x_84 = x_737;
x_85 = x_738;
x_86 = x_739;
x_87 = x_740;
x_88 = x_741;
x_89 = x_742;
x_90 = x_743;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_st_ref_get(x_738);
x_755 = lean_ctor_get(x_754, 0);
lean_inc_ref(x_755);
lean_dec(x_754);
x_756 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_735, x_755, x_740, x_741, x_742, x_743);
lean_dec_ref(x_755);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; lean_object* x_758; 
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
lean_dec_ref(x_756);
lean_inc(x_743);
lean_inc_ref(x_742);
lean_inc(x_741);
lean_inc_ref(x_740);
x_758 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_757, x_740, x_741, x_742, x_743);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
lean_dec_ref(x_758);
x_760 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_738);
if (lean_obj_tag(x_760) == 0)
{
uint8_t x_761; 
lean_dec_ref(x_760);
x_761 = lean_unbox(x_748);
lean_dec(x_748);
x_81 = x_736;
x_82 = x_761;
x_83 = x_759;
x_84 = x_737;
x_85 = x_738;
x_86 = x_739;
x_87 = x_740;
x_88 = x_741;
x_89 = x_742;
x_90 = x_743;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_759);
lean_dec(x_748);
lean_dec(x_743);
lean_dec_ref(x_742);
lean_dec(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec_ref(x_737);
lean_dec_ref(x_736);
lean_dec_ref(x_1);
x_762 = lean_ctor_get(x_760, 0);
lean_inc(x_762);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 x_763 = x_760;
} else {
 lean_dec_ref(x_760);
 x_763 = lean_box(0);
}
if (lean_is_scalar(x_763)) {
 x_764 = lean_alloc_ctor(1, 1, 0);
} else {
 x_764 = x_763;
}
lean_ctor_set(x_764, 0, x_762);
return x_764;
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; 
lean_dec(x_748);
lean_dec(x_743);
lean_dec_ref(x_742);
lean_dec(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec_ref(x_737);
lean_dec_ref(x_736);
lean_dec_ref(x_1);
x_765 = lean_ctor_get(x_758, 0);
lean_inc(x_765);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 x_766 = x_758;
} else {
 lean_dec_ref(x_758);
 x_766 = lean_box(0);
}
if (lean_is_scalar(x_766)) {
 x_767 = lean_alloc_ctor(1, 1, 0);
} else {
 x_767 = x_766;
}
lean_ctor_set(x_767, 0, x_765);
return x_767;
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_748);
lean_dec(x_743);
lean_dec_ref(x_742);
lean_dec(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec_ref(x_737);
lean_dec_ref(x_736);
lean_dec_ref(x_1);
x_768 = lean_ctor_get(x_756, 0);
lean_inc(x_768);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 x_769 = x_756;
} else {
 lean_dec_ref(x_756);
 x_769 = lean_box(0);
}
if (lean_is_scalar(x_769)) {
 x_770 = lean_alloc_ctor(1, 1, 0);
} else {
 x_770 = x_769;
}
lean_ctor_set(x_770, 0, x_768);
return x_770;
}
}
}
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_st_ref_get(x_738);
x_772 = lean_ctor_get(x_771, 0);
lean_inc_ref(x_772);
lean_dec(x_771);
x_773 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_735, x_772, x_740, x_741, x_742, x_743);
lean_dec_ref(x_772);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; uint8_t x_775; 
x_774 = lean_ctor_get(x_773, 0);
lean_inc(x_774);
lean_dec_ref(x_773);
x_775 = lean_unbox(x_748);
lean_dec(x_748);
x_49 = x_736;
x_50 = x_775;
x_51 = x_774;
x_52 = x_737;
x_53 = x_738;
x_54 = x_739;
x_55 = x_740;
x_56 = x_741;
x_57 = x_742;
x_58 = x_743;
x_59 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; 
lean_dec(x_748);
lean_dec(x_743);
lean_dec_ref(x_742);
lean_dec(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec_ref(x_737);
lean_dec_ref(x_736);
lean_dec_ref(x_1);
x_776 = lean_ctor_get(x_773, 0);
lean_inc(x_776);
if (lean_is_exclusive(x_773)) {
 lean_ctor_release(x_773, 0);
 x_777 = x_773;
} else {
 lean_dec_ref(x_773);
 x_777 = lean_box(0);
}
if (lean_is_scalar(x_777)) {
 x_778 = lean_alloc_ctor(1, 1, 0);
} else {
 x_778 = x_777;
}
lean_ctor_set(x_778, 0, x_776);
return x_778;
}
}
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; 
lean_dec(x_743);
lean_dec_ref(x_742);
lean_dec(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec_ref(x_737);
lean_dec_ref(x_736);
lean_dec_ref(x_735);
lean_dec_ref(x_1);
x_779 = lean_ctor_get(x_747, 0);
lean_inc(x_779);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 x_780 = x_747;
} else {
 lean_dec_ref(x_747);
 x_780 = lean_box(0);
}
if (lean_is_scalar(x_780)) {
 x_781 = lean_alloc_ctor(1, 1, 0);
} else {
 x_781 = x_780;
}
lean_ctor_set(x_781, 0, x_779);
return x_781;
}
}
}
}
else
{
uint8_t x_1177; 
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
x_1177 = !lean_is_exclusive(x_138);
if (x_1177 == 0)
{
return x_138;
}
else
{
lean_object* x_1178; lean_object* x_1179; 
x_1178 = lean_ctor_get(x_138, 0);
lean_inc(x_1178);
lean_dec(x_138);
x_1179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1179, 0, x_1178);
return x_1179;
}
}
}
else
{
lean_object* x_1180; 
lean_dec(x_7);
x_1180 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3);
if (lean_obj_tag(x_1180) == 0)
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; 
if (lean_is_exclusive(x_1180)) {
 lean_ctor_release(x_1180, 0);
 x_1181 = x_1180;
} else {
 lean_dec_ref(x_1180);
 x_1181 = lean_box(0);
}
x_1230 = lean_unsigned_to_nat(1u);
x_1231 = lean_nat_add(x_109, x_1230);
lean_dec(x_109);
x_1232 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_1232, 0, x_106);
lean_ctor_set(x_1232, 1, x_107);
lean_ctor_set(x_1232, 2, x_108);
lean_ctor_set(x_1232, 3, x_1231);
lean_ctor_set(x_1232, 4, x_110);
lean_ctor_set(x_1232, 5, x_111);
lean_ctor_set(x_1232, 6, x_112);
lean_ctor_set(x_1232, 7, x_113);
lean_ctor_set(x_1232, 8, x_114);
lean_ctor_set(x_1232, 9, x_115);
lean_ctor_set(x_1232, 10, x_116);
lean_ctor_set(x_1232, 11, x_117);
lean_ctor_set(x_1232, 12, x_119);
lean_ctor_set(x_1232, 13, x_121);
lean_ctor_set_uint8(x_1232, sizeof(void*)*14, x_118);
lean_ctor_set_uint8(x_1232, sizeof(void*)*14 + 1, x_120);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; uint8_t x_1244; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1375; 
lean_dec(x_1181);
x_1233 = lean_ctor_get(x_1, 0);
x_1234 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1233);
x_1375 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_122, x_1233, x_3, x_6);
if (lean_obj_tag(x_1375) == 0)
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; uint8_t x_1410; 
x_1376 = lean_ctor_get(x_1375, 0);
lean_inc(x_1376);
lean_dec_ref(x_1375);
x_1410 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_1233, x_1376);
if (x_1410 == 0)
{
goto block_1409;
}
else
{
if (x_122 == 0)
{
x_1377 = x_2;
x_1378 = x_3;
x_1379 = x_4;
x_1380 = x_5;
x_1381 = x_6;
x_1382 = x_1232;
x_1383 = x_8;
x_1384 = lean_box(0);
goto block_1404;
}
else
{
goto block_1409;
}
}
block_1404:
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
x_1385 = lean_ctor_get(x_1376, 2);
x_1386 = lean_ctor_get(x_1376, 3);
lean_inc(x_1383);
lean_inc_ref(x_1382);
lean_inc(x_1381);
lean_inc_ref(x_1380);
lean_inc_ref(x_1379);
lean_inc(x_1386);
x_1387 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_1386, x_1377, x_1379, x_1380, x_1381, x_1382, x_1383);
if (lean_obj_tag(x_1387) == 0)
{
lean_object* x_1388; 
x_1388 = lean_ctor_get(x_1387, 0);
lean_inc(x_1388);
lean_dec_ref(x_1387);
if (lean_obj_tag(x_1388) == 1)
{
lean_object* x_1389; lean_object* x_1390; 
x_1389 = lean_ctor_get(x_1388, 0);
lean_inc(x_1389);
lean_dec_ref(x_1388);
x_1390 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1378);
if (lean_obj_tag(x_1390) == 0)
{
lean_object* x_1391; 
lean_dec_ref(x_1390);
x_1391 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_1376, x_1389, x_1381);
if (lean_obj_tag(x_1391) == 0)
{
lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; 
x_1392 = lean_ctor_get(x_1391, 0);
lean_inc(x_1392);
lean_dec_ref(x_1391);
x_1393 = lean_ctor_get(x_1392, 2);
lean_inc_ref(x_1393);
x_1394 = lean_ctor_get(x_1392, 3);
lean_inc(x_1394);
x_1360 = x_1392;
x_1361 = x_1393;
x_1362 = x_1394;
x_1363 = x_1377;
x_1364 = x_1378;
x_1365 = x_1379;
x_1366 = x_1380;
x_1367 = x_1381;
x_1368 = x_1382;
x_1369 = x_1383;
x_1370 = lean_box(0);
goto block_1374;
}
else
{
lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; 
lean_dec(x_1383);
lean_dec_ref(x_1382);
lean_dec(x_1381);
lean_dec_ref(x_1380);
lean_dec_ref(x_1379);
lean_dec(x_1378);
lean_dec_ref(x_1377);
lean_dec_ref(x_1);
x_1395 = lean_ctor_get(x_1391, 0);
lean_inc(x_1395);
if (lean_is_exclusive(x_1391)) {
 lean_ctor_release(x_1391, 0);
 x_1396 = x_1391;
} else {
 lean_dec_ref(x_1391);
 x_1396 = lean_box(0);
}
if (lean_is_scalar(x_1396)) {
 x_1397 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1397 = x_1396;
}
lean_ctor_set(x_1397, 0, x_1395);
return x_1397;
}
}
else
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
lean_dec(x_1389);
lean_dec(x_1383);
lean_dec_ref(x_1382);
lean_dec(x_1381);
lean_dec_ref(x_1380);
lean_dec_ref(x_1379);
lean_dec(x_1378);
lean_dec_ref(x_1377);
lean_dec(x_1376);
lean_dec_ref(x_1);
x_1398 = lean_ctor_get(x_1390, 0);
lean_inc(x_1398);
if (lean_is_exclusive(x_1390)) {
 lean_ctor_release(x_1390, 0);
 x_1399 = x_1390;
} else {
 lean_dec_ref(x_1390);
 x_1399 = lean_box(0);
}
if (lean_is_scalar(x_1399)) {
 x_1400 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1400 = x_1399;
}
lean_ctor_set(x_1400, 0, x_1398);
return x_1400;
}
}
else
{
lean_dec(x_1388);
lean_inc(x_1386);
lean_inc_ref(x_1385);
x_1360 = x_1376;
x_1361 = x_1385;
x_1362 = x_1386;
x_1363 = x_1377;
x_1364 = x_1378;
x_1365 = x_1379;
x_1366 = x_1380;
x_1367 = x_1381;
x_1368 = x_1382;
x_1369 = x_1383;
x_1370 = lean_box(0);
goto block_1374;
}
}
else
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
lean_dec(x_1383);
lean_dec_ref(x_1382);
lean_dec(x_1381);
lean_dec_ref(x_1380);
lean_dec_ref(x_1379);
lean_dec(x_1378);
lean_dec_ref(x_1377);
lean_dec(x_1376);
lean_dec_ref(x_1);
x_1401 = lean_ctor_get(x_1387, 0);
lean_inc(x_1401);
if (lean_is_exclusive(x_1387)) {
 lean_ctor_release(x_1387, 0);
 x_1402 = x_1387;
} else {
 lean_dec_ref(x_1387);
 x_1402 = lean_box(0);
}
if (lean_is_scalar(x_1402)) {
 x_1403 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1403 = x_1402;
}
lean_ctor_set(x_1403, 0, x_1401);
return x_1403;
}
}
block_1409:
{
lean_object* x_1405; 
x_1405 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_1405) == 0)
{
lean_dec_ref(x_1405);
x_1377 = x_2;
x_1378 = x_3;
x_1379 = x_4;
x_1380 = x_5;
x_1381 = x_6;
x_1382 = x_1232;
x_1383 = x_8;
x_1384 = lean_box(0);
goto block_1404;
}
else
{
lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; 
lean_dec(x_1376);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1406 = lean_ctor_get(x_1405, 0);
lean_inc(x_1406);
if (lean_is_exclusive(x_1405)) {
 lean_ctor_release(x_1405, 0);
 x_1407 = x_1405;
} else {
 lean_dec_ref(x_1405);
 x_1407 = lean_box(0);
}
if (lean_is_scalar(x_1407)) {
 x_1408 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1408 = x_1407;
}
lean_ctor_set(x_1408, 0, x_1406);
return x_1408;
}
}
}
else
{
lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; 
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1411 = lean_ctor_get(x_1375, 0);
lean_inc(x_1411);
if (lean_is_exclusive(x_1375)) {
 lean_ctor_release(x_1375, 0);
 x_1412 = x_1375;
} else {
 lean_dec_ref(x_1375);
 x_1412 = lean_box(0);
}
if (lean_is_scalar(x_1412)) {
 x_1413 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1413 = x_1412;
}
lean_ctor_set(x_1413, 0, x_1411);
return x_1413;
}
block_1359:
{
if (x_1244 == 0)
{
lean_object* x_1245; 
lean_inc(x_1240);
lean_inc_ref(x_1235);
lean_inc(x_1243);
lean_inc_ref(x_1241);
lean_inc_ref(x_1242);
x_1245 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_1242, x_1241, x_1243, x_1235, x_1240);
if (lean_obj_tag(x_1245) == 0)
{
lean_object* x_1246; 
x_1246 = lean_ctor_get(x_1245, 0);
lean_inc(x_1246);
lean_dec_ref(x_1245);
if (lean_obj_tag(x_1246) == 1)
{
lean_object* x_1247; lean_object* x_1248; 
lean_dec_ref(x_1242);
lean_inc_ref(x_1234);
lean_dec_ref(x_1);
x_1247 = lean_ctor_get(x_1246, 0);
lean_inc(x_1247);
lean_dec_ref(x_1246);
x_1248 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1236);
if (lean_obj_tag(x_1248) == 0)
{
lean_object* x_1249; 
lean_dec_ref(x_1248);
lean_inc(x_1240);
lean_inc_ref(x_1235);
lean_inc(x_1243);
lean_inc_ref(x_1241);
lean_inc_ref(x_1238);
lean_inc(x_1236);
lean_inc_ref(x_1239);
x_1249 = l_Lean_Compiler_LCNF_Simp_simp(x_1234, x_1239, x_1236, x_1238, x_1241, x_1243, x_1235, x_1240);
if (lean_obj_tag(x_1249) == 0)
{
lean_object* x_1250; lean_object* x_1251; 
x_1250 = lean_ctor_get(x_1249, 0);
lean_inc(x_1250);
lean_dec_ref(x_1249);
x_1251 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1247, x_1250, x_1239, x_1236, x_1238, x_1241, x_1243, x_1235, x_1240);
lean_dec(x_1240);
lean_dec_ref(x_1235);
lean_dec(x_1243);
lean_dec_ref(x_1241);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1239);
lean_dec(x_1247);
return x_1251;
}
else
{
lean_dec(x_1247);
lean_dec(x_1243);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
return x_1249;
}
}
else
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; 
lean_dec(x_1247);
lean_dec(x_1243);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1234);
x_1252 = lean_ctor_get(x_1248, 0);
lean_inc(x_1252);
if (lean_is_exclusive(x_1248)) {
 lean_ctor_release(x_1248, 0);
 x_1253 = x_1248;
} else {
 lean_dec_ref(x_1248);
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
lean_object* x_1255; 
lean_dec(x_1246);
lean_inc(x_1240);
lean_inc_ref(x_1235);
lean_inc(x_1243);
lean_inc_ref(x_1241);
lean_inc_ref(x_1242);
x_1255 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1242, x_1239, x_1236, x_1241, x_1243, x_1235, x_1240);
if (lean_obj_tag(x_1255) == 0)
{
lean_object* x_1256; 
x_1256 = lean_ctor_get(x_1255, 0);
lean_inc(x_1256);
lean_dec_ref(x_1255);
if (lean_obj_tag(x_1256) == 1)
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; 
lean_dec_ref(x_1242);
lean_inc_ref(x_1234);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1257 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1257 = lean_box(0);
}
x_1258 = lean_ctor_get(x_1256, 0);
lean_inc(x_1258);
lean_dec_ref(x_1256);
if (lean_is_scalar(x_1257)) {
 x_1259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1259 = x_1257;
 lean_ctor_set_tag(x_1259, 1);
}
lean_ctor_set(x_1259, 0, x_1258);
lean_ctor_set(x_1259, 1, x_1234);
x_1 = x_1259;
x_2 = x_1239;
x_3 = x_1236;
x_4 = x_1238;
x_5 = x_1241;
x_6 = x_1243;
x_7 = x_1235;
x_8 = x_1240;
goto _start;
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
lean_dec(x_1256);
x_1261 = lean_ctor_get(x_1242, 0);
x_1262 = lean_ctor_get(x_1242, 3);
x_1263 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1262);
if (lean_obj_tag(x_1263) == 0)
{
lean_object* x_1264; 
x_1264 = lean_ctor_get(x_1263, 0);
lean_inc(x_1264);
lean_dec_ref(x_1263);
if (lean_obj_tag(x_1264) == 1)
{
lean_object* x_1265; lean_object* x_1266; 
lean_inc_ref(x_1234);
lean_dec_ref(x_1);
x_1265 = lean_ctor_get(x_1264, 0);
lean_inc(x_1265);
lean_dec_ref(x_1264);
lean_inc(x_1261);
x_1266 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1261, x_1265, x_1236, x_1243, x_1235, x_1240);
if (lean_obj_tag(x_1266) == 0)
{
lean_object* x_1267; 
lean_dec_ref(x_1266);
x_1267 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1242, x_1236, x_1243);
lean_dec_ref(x_1242);
if (lean_obj_tag(x_1267) == 0)
{
lean_dec_ref(x_1267);
x_1 = x_1234;
x_2 = x_1239;
x_3 = x_1236;
x_4 = x_1238;
x_5 = x_1241;
x_6 = x_1243;
x_7 = x_1235;
x_8 = x_1240;
goto _start;
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; 
lean_dec(x_1243);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1234);
x_1269 = lean_ctor_get(x_1267, 0);
lean_inc(x_1269);
if (lean_is_exclusive(x_1267)) {
 lean_ctor_release(x_1267, 0);
 x_1270 = x_1267;
} else {
 lean_dec_ref(x_1267);
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
else
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; 
lean_dec(x_1243);
lean_dec_ref(x_1242);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1234);
x_1272 = lean_ctor_get(x_1266, 0);
lean_inc(x_1272);
if (lean_is_exclusive(x_1266)) {
 lean_ctor_release(x_1266, 0);
 x_1273 = x_1266;
} else {
 lean_dec_ref(x_1266);
 x_1273 = lean_box(0);
}
if (lean_is_scalar(x_1273)) {
 x_1274 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1274 = x_1273;
}
lean_ctor_set(x_1274, 0, x_1272);
return x_1274;
}
}
else
{
lean_object* x_1275; 
lean_dec(x_1264);
lean_inc(x_1240);
lean_inc_ref(x_1235);
lean_inc(x_1243);
lean_inc_ref(x_1241);
lean_inc_ref(x_1238);
lean_inc(x_1236);
lean_inc_ref(x_1239);
lean_inc_ref(x_1234);
lean_inc_ref(x_1242);
x_1275 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1242, x_1234, x_1239, x_1236, x_1238, x_1241, x_1243, x_1235, x_1240);
if (lean_obj_tag(x_1275) == 0)
{
lean_object* x_1276; 
x_1276 = lean_ctor_get(x_1275, 0);
lean_inc(x_1276);
lean_dec_ref(x_1275);
if (lean_obj_tag(x_1276) == 1)
{
lean_object* x_1277; lean_object* x_1278; 
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec_ref(x_1235);
lean_dec_ref(x_1);
x_1277 = lean_ctor_get(x_1276, 0);
lean_inc(x_1277);
lean_dec_ref(x_1276);
x_1278 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1242, x_1236, x_1243);
lean_dec(x_1243);
lean_dec(x_1236);
lean_dec_ref(x_1242);
if (lean_obj_tag(x_1278) == 0)
{
lean_object* x_1279; lean_object* x_1280; 
if (lean_is_exclusive(x_1278)) {
 lean_ctor_release(x_1278, 0);
 x_1279 = x_1278;
} else {
 lean_dec_ref(x_1278);
 x_1279 = lean_box(0);
}
if (lean_is_scalar(x_1279)) {
 x_1280 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1280 = x_1279;
}
lean_ctor_set(x_1280, 0, x_1277);
return x_1280;
}
else
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
lean_dec(x_1277);
x_1281 = lean_ctor_get(x_1278, 0);
lean_inc(x_1281);
if (lean_is_exclusive(x_1278)) {
 lean_ctor_release(x_1278, 0);
 x_1282 = x_1278;
} else {
 lean_dec_ref(x_1278);
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
else
{
lean_object* x_1284; 
lean_dec(x_1276);
lean_inc(x_1240);
lean_inc_ref(x_1235);
lean_inc(x_1243);
lean_inc_ref(x_1241);
lean_inc_ref(x_1238);
lean_inc(x_1236);
lean_inc_ref(x_1239);
lean_inc(x_1262);
x_1284 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_1262, x_1239, x_1236, x_1238, x_1241, x_1243, x_1235, x_1240);
if (lean_obj_tag(x_1284) == 0)
{
lean_object* x_1285; 
x_1285 = lean_ctor_get(x_1284, 0);
lean_inc(x_1285);
lean_dec_ref(x_1284);
if (lean_obj_tag(x_1285) == 1)
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
lean_inc_ref(x_1234);
lean_dec_ref(x_1);
x_1286 = lean_ctor_get(x_1285, 0);
lean_inc(x_1286);
lean_dec_ref(x_1285);
x_1287 = lean_ctor_get(x_1286, 0);
lean_inc(x_1287);
x_1288 = lean_ctor_get(x_1286, 1);
lean_inc(x_1288);
lean_dec(x_1286);
lean_inc(x_1261);
x_1289 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1261, x_1288, x_1236, x_1243, x_1235, x_1240);
if (lean_obj_tag(x_1289) == 0)
{
lean_object* x_1290; 
lean_dec_ref(x_1289);
x_1290 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1242, x_1236, x_1243);
lean_dec_ref(x_1242);
if (lean_obj_tag(x_1290) == 0)
{
lean_object* x_1291; 
lean_dec_ref(x_1290);
lean_inc(x_1240);
lean_inc_ref(x_1235);
lean_inc(x_1243);
lean_inc_ref(x_1241);
lean_inc_ref(x_1238);
lean_inc(x_1236);
lean_inc_ref(x_1239);
x_1291 = l_Lean_Compiler_LCNF_Simp_simp(x_1234, x_1239, x_1236, x_1238, x_1241, x_1243, x_1235, x_1240);
if (lean_obj_tag(x_1291) == 0)
{
lean_object* x_1292; lean_object* x_1293; 
x_1292 = lean_ctor_get(x_1291, 0);
lean_inc(x_1292);
lean_dec_ref(x_1291);
x_1293 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1287, x_1292, x_1239, x_1236, x_1238, x_1241, x_1243, x_1235, x_1240);
lean_dec(x_1240);
lean_dec_ref(x_1235);
lean_dec(x_1243);
lean_dec_ref(x_1241);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1239);
lean_dec(x_1287);
return x_1293;
}
else
{
lean_dec(x_1287);
lean_dec(x_1243);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
return x_1291;
}
}
else
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
lean_dec(x_1287);
lean_dec(x_1243);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1234);
x_1294 = lean_ctor_get(x_1290, 0);
lean_inc(x_1294);
if (lean_is_exclusive(x_1290)) {
 lean_ctor_release(x_1290, 0);
 x_1295 = x_1290;
} else {
 lean_dec_ref(x_1290);
 x_1295 = lean_box(0);
}
if (lean_is_scalar(x_1295)) {
 x_1296 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1296 = x_1295;
}
lean_ctor_set(x_1296, 0, x_1294);
return x_1296;
}
}
else
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; 
lean_dec(x_1287);
lean_dec(x_1243);
lean_dec_ref(x_1242);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1234);
x_1297 = lean_ctor_get(x_1289, 0);
lean_inc(x_1297);
if (lean_is_exclusive(x_1289)) {
 lean_ctor_release(x_1289, 0);
 x_1298 = x_1289;
} else {
 lean_dec_ref(x_1289);
 x_1298 = lean_box(0);
}
if (lean_is_scalar(x_1298)) {
 x_1299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1299 = x_1298;
}
lean_ctor_set(x_1299, 0, x_1297);
return x_1299;
}
}
else
{
lean_object* x_1300; 
lean_dec(x_1285);
lean_inc(x_1240);
lean_inc_ref(x_1235);
lean_inc(x_1243);
lean_inc_ref(x_1241);
lean_inc_ref(x_1238);
lean_inc(x_1236);
lean_inc_ref(x_1239);
lean_inc_ref(x_1234);
x_1300 = l_Lean_Compiler_LCNF_Simp_simp(x_1234, x_1239, x_1236, x_1238, x_1241, x_1243, x_1235, x_1240);
if (lean_obj_tag(x_1300) == 0)
{
lean_object* x_1301; lean_object* x_1302; 
x_1301 = lean_ctor_get(x_1300, 0);
lean_inc(x_1301);
lean_dec_ref(x_1300);
x_1302 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_1261, x_1236);
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; uint8_t x_1304; 
x_1303 = lean_ctor_get(x_1302, 0);
lean_inc(x_1303);
lean_dec_ref(x_1302);
x_1304 = lean_unbox(x_1303);
lean_dec(x_1303);
if (x_1304 == 0)
{
lean_object* x_1305; 
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec_ref(x_1235);
lean_dec_ref(x_1);
x_1305 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1242, x_1236, x_1243);
lean_dec(x_1243);
lean_dec(x_1236);
lean_dec_ref(x_1242);
if (lean_obj_tag(x_1305) == 0)
{
lean_object* x_1306; lean_object* x_1307; 
if (lean_is_exclusive(x_1305)) {
 lean_ctor_release(x_1305, 0);
 x_1306 = x_1305;
} else {
 lean_dec_ref(x_1305);
 x_1306 = lean_box(0);
}
if (lean_is_scalar(x_1306)) {
 x_1307 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1307 = x_1306;
}
lean_ctor_set(x_1307, 0, x_1301);
return x_1307;
}
else
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; 
lean_dec(x_1301);
x_1308 = lean_ctor_get(x_1305, 0);
lean_inc(x_1308);
if (lean_is_exclusive(x_1305)) {
 lean_ctor_release(x_1305, 0);
 x_1309 = x_1305;
} else {
 lean_dec_ref(x_1305);
 x_1309 = lean_box(0);
}
if (lean_is_scalar(x_1309)) {
 x_1310 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1310 = x_1309;
}
lean_ctor_set(x_1310, 0, x_1308);
return x_1310;
}
}
else
{
lean_object* x_1311; 
lean_inc_ref(x_1242);
x_1311 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_1242, x_1239, x_1236, x_1238, x_1241, x_1243, x_1235, x_1240);
lean_dec(x_1240);
lean_dec_ref(x_1235);
lean_dec(x_1243);
lean_dec_ref(x_1241);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1239);
if (lean_obj_tag(x_1311) == 0)
{
size_t x_1312; size_t x_1313; uint8_t x_1314; 
lean_dec_ref(x_1311);
x_1312 = lean_ptr_addr(x_1234);
x_1313 = lean_ptr_addr(x_1301);
x_1314 = lean_usize_dec_eq(x_1312, x_1313);
if (x_1314 == 0)
{
x_98 = x_1242;
x_99 = lean_box(0);
x_100 = x_1301;
x_101 = x_1314;
goto block_105;
}
else
{
size_t x_1315; size_t x_1316; uint8_t x_1317; 
x_1315 = lean_ptr_addr(x_1233);
x_1316 = lean_ptr_addr(x_1242);
x_1317 = lean_usize_dec_eq(x_1315, x_1316);
x_98 = x_1242;
x_99 = lean_box(0);
x_100 = x_1301;
x_101 = x_1317;
goto block_105;
}
}
else
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; 
lean_dec(x_1301);
lean_dec_ref(x_1242);
lean_dec_ref(x_1);
x_1318 = lean_ctor_get(x_1311, 0);
lean_inc(x_1318);
if (lean_is_exclusive(x_1311)) {
 lean_ctor_release(x_1311, 0);
 x_1319 = x_1311;
} else {
 lean_dec_ref(x_1311);
 x_1319 = lean_box(0);
}
if (lean_is_scalar(x_1319)) {
 x_1320 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1320 = x_1319;
}
lean_ctor_set(x_1320, 0, x_1318);
return x_1320;
}
}
}
else
{
lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; 
lean_dec(x_1301);
lean_dec(x_1243);
lean_dec_ref(x_1242);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1);
x_1321 = lean_ctor_get(x_1302, 0);
lean_inc(x_1321);
if (lean_is_exclusive(x_1302)) {
 lean_ctor_release(x_1302, 0);
 x_1322 = x_1302;
} else {
 lean_dec_ref(x_1302);
 x_1322 = lean_box(0);
}
if (lean_is_scalar(x_1322)) {
 x_1323 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1323 = x_1322;
}
lean_ctor_set(x_1323, 0, x_1321);
return x_1323;
}
}
else
{
lean_dec(x_1243);
lean_dec_ref(x_1242);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1);
return x_1300;
}
}
}
else
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
lean_dec(x_1243);
lean_dec_ref(x_1242);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1);
x_1324 = lean_ctor_get(x_1284, 0);
lean_inc(x_1324);
if (lean_is_exclusive(x_1284)) {
 lean_ctor_release(x_1284, 0);
 x_1325 = x_1284;
} else {
 lean_dec_ref(x_1284);
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
else
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
lean_dec(x_1243);
lean_dec_ref(x_1242);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1);
x_1327 = lean_ctor_get(x_1275, 0);
lean_inc(x_1327);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 x_1328 = x_1275;
} else {
 lean_dec_ref(x_1275);
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
lean_dec(x_1243);
lean_dec_ref(x_1242);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1);
x_1330 = lean_ctor_get(x_1263, 0);
lean_inc(x_1330);
if (lean_is_exclusive(x_1263)) {
 lean_ctor_release(x_1263, 0);
 x_1331 = x_1263;
} else {
 lean_dec_ref(x_1263);
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
}
}
else
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
lean_dec(x_1243);
lean_dec_ref(x_1242);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1);
x_1333 = lean_ctor_get(x_1255, 0);
lean_inc(x_1333);
if (lean_is_exclusive(x_1255)) {
 lean_ctor_release(x_1255, 0);
 x_1334 = x_1255;
} else {
 lean_dec_ref(x_1255);
 x_1334 = lean_box(0);
}
if (lean_is_scalar(x_1334)) {
 x_1335 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1335 = x_1334;
}
lean_ctor_set(x_1335, 0, x_1333);
return x_1335;
}
}
}
else
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
lean_dec(x_1243);
lean_dec_ref(x_1242);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1);
x_1336 = lean_ctor_get(x_1245, 0);
lean_inc(x_1336);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 x_1337 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1337 = lean_box(0);
}
if (lean_is_scalar(x_1337)) {
 x_1338 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1338 = x_1337;
}
lean_ctor_set(x_1338, 0, x_1336);
return x_1338;
}
}
else
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; uint8_t x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; 
lean_inc_ref(x_1234);
lean_dec_ref(x_1);
x_1339 = lean_st_ref_take(x_1236);
x_1340 = lean_ctor_get(x_1242, 0);
x_1341 = lean_ctor_get(x_1339, 0);
lean_inc_ref(x_1341);
x_1342 = lean_ctor_get(x_1339, 1);
lean_inc_ref(x_1342);
x_1343 = lean_ctor_get(x_1339, 2);
lean_inc(x_1343);
x_1344 = lean_ctor_get(x_1339, 3);
lean_inc_ref(x_1344);
x_1345 = lean_ctor_get_uint8(x_1339, sizeof(void*)*7);
x_1346 = lean_ctor_get(x_1339, 4);
lean_inc(x_1346);
x_1347 = lean_ctor_get(x_1339, 5);
lean_inc(x_1347);
x_1348 = lean_ctor_get(x_1339, 6);
lean_inc(x_1348);
if (lean_is_exclusive(x_1339)) {
 lean_ctor_release(x_1339, 0);
 lean_ctor_release(x_1339, 1);
 lean_ctor_release(x_1339, 2);
 lean_ctor_release(x_1339, 3);
 lean_ctor_release(x_1339, 4);
 lean_ctor_release(x_1339, 5);
 lean_ctor_release(x_1339, 6);
 x_1349 = x_1339;
} else {
 lean_dec_ref(x_1339);
 x_1349 = lean_box(0);
}
x_1350 = lean_box(0);
lean_inc(x_1340);
x_1351 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1341, x_1340, x_1350);
if (lean_is_scalar(x_1349)) {
 x_1352 = lean_alloc_ctor(0, 7, 1);
} else {
 x_1352 = x_1349;
}
lean_ctor_set(x_1352, 0, x_1351);
lean_ctor_set(x_1352, 1, x_1342);
lean_ctor_set(x_1352, 2, x_1343);
lean_ctor_set(x_1352, 3, x_1344);
lean_ctor_set(x_1352, 4, x_1346);
lean_ctor_set(x_1352, 5, x_1347);
lean_ctor_set(x_1352, 6, x_1348);
lean_ctor_set_uint8(x_1352, sizeof(void*)*7, x_1345);
x_1353 = lean_st_ref_set(x_1236, x_1352);
x_1354 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1242, x_1236, x_1243);
lean_dec_ref(x_1242);
if (lean_obj_tag(x_1354) == 0)
{
lean_dec_ref(x_1354);
x_1 = x_1234;
x_2 = x_1239;
x_3 = x_1236;
x_4 = x_1238;
x_5 = x_1241;
x_6 = x_1243;
x_7 = x_1235;
x_8 = x_1240;
goto _start;
}
else
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
lean_dec(x_1243);
lean_dec_ref(x_1241);
lean_dec(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec(x_1236);
lean_dec_ref(x_1235);
lean_dec_ref(x_1234);
x_1356 = lean_ctor_get(x_1354, 0);
lean_inc(x_1356);
if (lean_is_exclusive(x_1354)) {
 lean_ctor_release(x_1354, 0);
 x_1357 = x_1354;
} else {
 lean_dec_ref(x_1354);
 x_1357 = lean_box(0);
}
if (lean_is_scalar(x_1357)) {
 x_1358 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1358 = x_1357;
}
lean_ctor_set(x_1358, 0, x_1356);
return x_1358;
}
}
}
block_1374:
{
uint8_t x_1371; 
x_1371 = l_Lean_Expr_isErased(x_1361);
lean_dec_ref(x_1361);
if (x_1371 == 0)
{
lean_dec(x_1362);
x_1235 = x_1368;
x_1236 = x_1364;
x_1237 = lean_box(0);
x_1238 = x_1365;
x_1239 = x_1363;
x_1240 = x_1369;
x_1241 = x_1366;
x_1242 = x_1360;
x_1243 = x_1367;
x_1244 = x_122;
goto block_1359;
}
else
{
lean_object* x_1372; uint8_t x_1373; 
x_1372 = lean_box(1);
x_1373 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_1362, x_1372);
lean_dec(x_1362);
if (x_1373 == 0)
{
x_1235 = x_1368;
x_1236 = x_1364;
x_1237 = lean_box(0);
x_1238 = x_1365;
x_1239 = x_1363;
x_1240 = x_1369;
x_1241 = x_1366;
x_1242 = x_1360;
x_1243 = x_1367;
x_1244 = x_1371;
goto block_1359;
}
else
{
x_1235 = x_1368;
x_1236 = x_1364;
x_1237 = lean_box(0);
x_1238 = x_1365;
x_1239 = x_1363;
x_1240 = x_1369;
x_1241 = x_1366;
x_1242 = x_1360;
x_1243 = x_1367;
x_1244 = x_122;
goto block_1359;
}
}
}
}
case 3:
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; 
lean_dec(x_1181);
x_1414 = lean_ctor_get(x_1, 0);
x_1415 = lean_ctor_get(x_1, 1);
x_1416 = lean_st_ref_get(x_3);
x_1417 = lean_ctor_get(x_1416, 0);
lean_inc_ref(x_1417);
lean_dec(x_1416);
lean_inc(x_1414);
x_1418 = l_Lean_Compiler_LCNF_normFVarImp(x_1417, x_1414, x_122);
lean_dec_ref(x_1417);
if (lean_obj_tag(x_1418) == 0)
{
lean_object* x_1419; lean_object* x_1420; 
x_1419 = lean_ctor_get(x_1418, 0);
lean_inc(x_1419);
lean_dec_ref(x_1418);
lean_inc_ref(x_1415);
x_1420 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_122, x_1415, x_3);
if (lean_obj_tag(x_1420) == 0)
{
lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; uint8_t x_1424; lean_object* x_1430; lean_object* x_1436; 
x_1421 = lean_ctor_get(x_1420, 0);
lean_inc(x_1421);
if (lean_is_exclusive(x_1420)) {
 lean_ctor_release(x_1420, 0);
 x_1422 = x_1420;
} else {
 lean_dec_ref(x_1420);
 x_1422 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_1232);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1421);
x_1436 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1419, x_1421, x_2, x_3, x_4, x_5, x_6, x_1232, x_8);
if (lean_obj_tag(x_1436) == 0)
{
lean_object* x_1437; 
x_1437 = lean_ctor_get(x_1436, 0);
lean_inc(x_1437);
lean_dec_ref(x_1436);
if (lean_obj_tag(x_1437) == 1)
{
lean_object* x_1438; 
lean_dec(x_1422);
lean_dec(x_1421);
lean_dec(x_1419);
lean_dec_ref(x_1);
x_1438 = lean_ctor_get(x_1437, 0);
lean_inc(x_1438);
lean_dec_ref(x_1437);
x_1 = x_1438;
x_7 = x_1232;
goto _start;
}
else
{
lean_object* x_1440; 
lean_dec(x_1437);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_1419);
x_1440 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1419, x_3);
if (lean_obj_tag(x_1440) == 0)
{
lean_object* x_1441; lean_object* x_1442; uint8_t x_1443; 
lean_dec_ref(x_1440);
x_1441 = lean_unsigned_to_nat(0u);
x_1442 = lean_array_get_size(x_1421);
x_1443 = lean_nat_dec_lt(x_1441, x_1442);
if (x_1443 == 0)
{
lean_dec(x_3);
x_1430 = lean_box(0);
goto block_1435;
}
else
{
uint8_t x_1444; 
x_1444 = lean_nat_dec_le(x_1442, x_1442);
if (x_1444 == 0)
{
lean_dec(x_3);
x_1430 = lean_box(0);
goto block_1435;
}
else
{
lean_object* x_1445; size_t x_1446; size_t x_1447; lean_object* x_1448; 
x_1445 = lean_box(0);
x_1446 = 0;
x_1447 = lean_usize_of_nat(x_1442);
x_1448 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1421, x_1446, x_1447, x_1445, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1448) == 0)
{
lean_dec_ref(x_1448);
x_1430 = lean_box(0);
goto block_1435;
}
else
{
lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
lean_dec(x_1422);
lean_dec(x_1421);
lean_dec(x_1419);
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
}
else
{
lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; 
lean_dec(x_1422);
lean_dec(x_1421);
lean_dec(x_1419);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1452 = lean_ctor_get(x_1440, 0);
lean_inc(x_1452);
if (lean_is_exclusive(x_1440)) {
 lean_ctor_release(x_1440, 0);
 x_1453 = x_1440;
} else {
 lean_dec_ref(x_1440);
 x_1453 = lean_box(0);
}
if (lean_is_scalar(x_1453)) {
 x_1454 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1454 = x_1453;
}
lean_ctor_set(x_1454, 0, x_1452);
return x_1454;
}
}
}
else
{
lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
lean_dec(x_1422);
lean_dec(x_1421);
lean_dec(x_1419);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1455 = lean_ctor_get(x_1436, 0);
lean_inc(x_1455);
if (lean_is_exclusive(x_1436)) {
 lean_ctor_release(x_1436, 0);
 x_1456 = x_1436;
} else {
 lean_dec_ref(x_1436);
 x_1456 = lean_box(0);
}
if (lean_is_scalar(x_1456)) {
 x_1457 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1457 = x_1456;
}
lean_ctor_set(x_1457, 0, x_1455);
return x_1457;
}
block_1429:
{
if (x_1424 == 0)
{
lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1425 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1425 = lean_box(0);
}
if (lean_is_scalar(x_1425)) {
 x_1426 = lean_alloc_ctor(3, 2, 0);
} else {
 x_1426 = x_1425;
}
lean_ctor_set(x_1426, 0, x_1419);
lean_ctor_set(x_1426, 1, x_1421);
if (lean_is_scalar(x_1422)) {
 x_1427 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1427 = x_1422;
}
lean_ctor_set(x_1427, 0, x_1426);
return x_1427;
}
else
{
lean_object* x_1428; 
lean_dec(x_1421);
lean_dec(x_1419);
if (lean_is_scalar(x_1422)) {
 x_1428 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1428 = x_1422;
}
lean_ctor_set(x_1428, 0, x_1);
return x_1428;
}
}
block_1435:
{
uint8_t x_1431; 
x_1431 = l_Lean_instBEqFVarId_beq(x_1414, x_1419);
if (x_1431 == 0)
{
x_1423 = lean_box(0);
x_1424 = x_1431;
goto block_1429;
}
else
{
size_t x_1432; size_t x_1433; uint8_t x_1434; 
x_1432 = lean_ptr_addr(x_1415);
x_1433 = lean_ptr_addr(x_1421);
x_1434 = lean_usize_dec_eq(x_1432, x_1433);
x_1423 = lean_box(0);
x_1424 = x_1434;
goto block_1429;
}
}
}
else
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; 
lean_dec(x_1419);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1458 = lean_ctor_get(x_1420, 0);
lean_inc(x_1458);
if (lean_is_exclusive(x_1420)) {
 lean_ctor_release(x_1420, 0);
 x_1459 = x_1420;
} else {
 lean_dec_ref(x_1420);
 x_1459 = lean_box(0);
}
if (lean_is_scalar(x_1459)) {
 x_1460 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1460 = x_1459;
}
lean_ctor_set(x_1460, 0, x_1458);
return x_1460;
}
}
else
{
lean_object* x_1461; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1461 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1232, x_8);
lean_dec(x_8);
lean_dec_ref(x_1232);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1461;
}
}
case 4:
{
lean_object* x_1462; lean_object* x_1463; 
lean_dec(x_1181);
x_1462 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1462);
lean_inc(x_8);
lean_inc_ref(x_1232);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1462);
x_1463 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1462, x_2, x_3, x_4, x_5, x_6, x_1232, x_8);
if (lean_obj_tag(x_1463) == 0)
{
lean_object* x_1464; lean_object* x_1465; 
x_1464 = lean_ctor_get(x_1463, 0);
lean_inc(x_1464);
if (lean_is_exclusive(x_1463)) {
 lean_ctor_release(x_1463, 0);
 x_1465 = x_1463;
} else {
 lean_dec_ref(x_1463);
 x_1465 = lean_box(0);
}
if (lean_obj_tag(x_1464) == 1)
{
lean_object* x_1466; lean_object* x_1467; 
lean_dec_ref(x_1462);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1466 = lean_ctor_get(x_1464, 0);
lean_inc(x_1466);
lean_dec_ref(x_1464);
if (lean_is_scalar(x_1465)) {
 x_1467 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1467 = x_1465;
}
lean_ctor_set(x_1467, 0, x_1466);
return x_1467;
}
else
{
lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; 
lean_dec(x_1464);
x_1468 = lean_st_ref_get(x_3);
x_1469 = lean_ctor_get(x_1462, 0);
lean_inc(x_1469);
x_1470 = lean_ctor_get(x_1462, 1);
lean_inc_ref(x_1470);
x_1471 = lean_ctor_get(x_1462, 2);
lean_inc(x_1471);
x_1472 = lean_ctor_get(x_1462, 3);
lean_inc_ref(x_1472);
if (lean_is_exclusive(x_1462)) {
 lean_ctor_release(x_1462, 0);
 lean_ctor_release(x_1462, 1);
 lean_ctor_release(x_1462, 2);
 lean_ctor_release(x_1462, 3);
 x_1473 = x_1462;
} else {
 lean_dec_ref(x_1462);
 x_1473 = lean_box(0);
}
x_1474 = lean_ctor_get(x_1468, 0);
lean_inc_ref(x_1474);
lean_dec(x_1468);
lean_inc(x_1471);
x_1475 = l_Lean_Compiler_LCNF_normFVarImp(x_1474, x_1471, x_122);
lean_dec_ref(x_1474);
if (lean_obj_tag(x_1475) == 0)
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; 
x_1476 = lean_ctor_get(x_1475, 0);
lean_inc(x_1476);
if (lean_is_exclusive(x_1475)) {
 lean_ctor_release(x_1475, 0);
 x_1477 = x_1475;
} else {
 lean_dec_ref(x_1475);
 x_1477 = lean_box(0);
}
x_1478 = lean_st_ref_get(x_3);
x_1479 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_1232);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1472);
lean_inc(x_1476);
x_1480 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_1476, x_122, x_1479, x_1472, x_2, x_3, x_4, x_5, x_6, x_1232, x_8);
if (lean_obj_tag(x_1480) == 0)
{
lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; 
x_1481 = lean_ctor_get(x_1480, 0);
lean_inc(x_1481);
if (lean_is_exclusive(x_1480)) {
 lean_ctor_release(x_1480, 0);
 x_1482 = x_1480;
} else {
 lean_dec_ref(x_1480);
 x_1482 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_1232);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_1483 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1481, x_2, x_3, x_4, x_5, x_6, x_1232, x_8);
if (lean_obj_tag(x_1483) == 0)
{
lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1515; lean_object* x_1520; uint8_t x_1521; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1547; uint8_t x_1548; 
x_1484 = lean_ctor_get(x_1483, 0);
lean_inc(x_1484);
if (lean_is_exclusive(x_1483)) {
 lean_ctor_release(x_1483, 0);
 x_1485 = x_1483;
} else {
 lean_dec_ref(x_1483);
 x_1485 = lean_box(0);
}
x_1486 = lean_ctor_get(x_1478, 0);
lean_inc_ref(x_1486);
lean_dec(x_1478);
lean_inc_ref(x_1470);
x_1487 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1486, x_122, x_1470);
lean_dec_ref(x_1486);
x_1547 = lean_array_get_size(x_1484);
x_1548 = lean_nat_dec_eq(x_1547, x_1230);
if (x_1548 == 0)
{
lean_dec(x_1465);
x_1525 = x_3;
x_1526 = x_5;
x_1527 = x_6;
x_1528 = x_1232;
x_1529 = x_8;
x_1530 = lean_box(0);
goto block_1546;
}
else
{
lean_object* x_1549; 
x_1549 = lean_array_fget_borrowed(x_1484, x_1479);
if (lean_obj_tag(x_1549) == 0)
{
lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1560; lean_object* x_1561; uint8_t x_1572; lean_object* x_1573; uint8_t x_1575; 
lean_dec(x_1465);
x_1550 = lean_ctor_get(x_1549, 1);
x_1551 = lean_ctor_get(x_1549, 2);
x_1560 = lean_array_get_size(x_1550);
x_1575 = lean_nat_dec_lt(x_1479, x_1560);
if (x_1575 == 0)
{
x_1572 = x_122;
x_1573 = lean_box(0);
goto block_1574;
}
else
{
if (x_1575 == 0)
{
x_1572 = x_122;
x_1573 = lean_box(0);
goto block_1574;
}
else
{
size_t x_1576; size_t x_1577; lean_object* x_1578; 
x_1576 = 0;
x_1577 = lean_usize_of_nat(x_1560);
x_1578 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1550, x_1576, x_1577, x_3);
if (lean_obj_tag(x_1578) == 0)
{
lean_object* x_1579; uint8_t x_1580; 
x_1579 = lean_ctor_get(x_1578, 0);
lean_inc(x_1579);
lean_dec_ref(x_1578);
x_1580 = lean_unbox(x_1579);
lean_dec(x_1579);
x_1572 = x_1580;
x_1573 = lean_box(0);
goto block_1574;
}
else
{
lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; 
lean_dec_ref(x_1487);
lean_dec(x_1485);
lean_dec(x_1484);
lean_dec(x_1482);
lean_dec(x_1477);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1581 = lean_ctor_get(x_1578, 0);
lean_inc(x_1581);
if (lean_is_exclusive(x_1578)) {
 lean_ctor_release(x_1578, 0);
 x_1582 = x_1578;
} else {
 lean_dec_ref(x_1578);
 x_1582 = lean_box(0);
}
if (lean_is_scalar(x_1582)) {
 x_1583 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1583 = x_1582;
}
lean_ctor_set(x_1583, 0, x_1581);
return x_1583;
}
}
}
block_1559:
{
lean_object* x_1553; 
x_1553 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1553) == 0)
{
lean_object* x_1554; lean_object* x_1555; 
if (lean_is_exclusive(x_1553)) {
 lean_ctor_release(x_1553, 0);
 x_1554 = x_1553;
} else {
 lean_dec_ref(x_1553);
 x_1554 = lean_box(0);
}
if (lean_is_scalar(x_1554)) {
 x_1555 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1555 = x_1554;
}
lean_ctor_set(x_1555, 0, x_1551);
return x_1555;
}
else
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; 
lean_dec_ref(x_1551);
x_1556 = lean_ctor_get(x_1553, 0);
lean_inc(x_1556);
if (lean_is_exclusive(x_1553)) {
 lean_ctor_release(x_1553, 0);
 x_1557 = x_1553;
} else {
 lean_dec_ref(x_1553);
 x_1557 = lean_box(0);
}
if (lean_is_scalar(x_1557)) {
 x_1558 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1558 = x_1557;
}
lean_ctor_set(x_1558, 0, x_1556);
return x_1558;
}
}
block_1571:
{
uint8_t x_1562; 
x_1562 = lean_nat_dec_lt(x_1479, x_1560);
if (x_1562 == 0)
{
lean_dec_ref(x_1550);
lean_dec(x_6);
x_1552 = lean_box(0);
goto block_1559;
}
else
{
uint8_t x_1563; 
x_1563 = lean_nat_dec_le(x_1560, x_1560);
if (x_1563 == 0)
{
lean_dec_ref(x_1550);
lean_dec(x_6);
x_1552 = lean_box(0);
goto block_1559;
}
else
{
lean_object* x_1564; size_t x_1565; size_t x_1566; lean_object* x_1567; 
x_1564 = lean_box(0);
x_1565 = 0;
x_1566 = lean_usize_of_nat(x_1560);
x_1567 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_1550, x_1565, x_1566, x_1564, x_6);
lean_dec(x_6);
lean_dec_ref(x_1550);
if (lean_obj_tag(x_1567) == 0)
{
lean_dec_ref(x_1567);
x_1552 = lean_box(0);
goto block_1559;
}
else
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
lean_dec_ref(x_1551);
lean_dec(x_3);
x_1568 = lean_ctor_get(x_1567, 0);
lean_inc(x_1568);
if (lean_is_exclusive(x_1567)) {
 lean_ctor_release(x_1567, 0);
 x_1569 = x_1567;
} else {
 lean_dec_ref(x_1567);
 x_1569 = lean_box(0);
}
if (lean_is_scalar(x_1569)) {
 x_1570 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1570 = x_1569;
}
lean_ctor_set(x_1570, 0, x_1568);
return x_1570;
}
}
}
}
block_1574:
{
if (x_1572 == 0)
{
lean_inc_ref(x_1551);
lean_inc_ref(x_1550);
lean_dec_ref(x_1487);
lean_dec(x_1485);
lean_dec(x_1484);
lean_dec(x_1482);
lean_dec(x_1477);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1561 = lean_box(0);
goto block_1571;
}
else
{
if (x_122 == 0)
{
x_1525 = x_3;
x_1526 = x_5;
x_1527 = x_6;
x_1528 = x_1232;
x_1529 = x_8;
x_1530 = lean_box(0);
goto block_1546;
}
else
{
lean_inc_ref(x_1551);
lean_inc_ref(x_1550);
lean_dec_ref(x_1487);
lean_dec(x_1485);
lean_dec(x_1484);
lean_dec(x_1482);
lean_dec(x_1477);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1561 = lean_box(0);
goto block_1571;
}
}
}
}
else
{
lean_object* x_1584; lean_object* x_1585; 
lean_inc_ref(x_1549);
lean_dec_ref(x_1487);
lean_dec(x_1485);
lean_dec(x_1484);
lean_dec(x_1482);
lean_dec(x_1477);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1584 = lean_ctor_get(x_1549, 0);
lean_inc_ref(x_1584);
lean_dec_ref(x_1549);
if (lean_is_scalar(x_1465)) {
 x_1585 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1585 = x_1465;
}
lean_ctor_set(x_1585, 0, x_1584);
return x_1585;
}
}
block_1497:
{
lean_object* x_1490; 
x_1490 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1488);
lean_dec(x_1488);
if (lean_obj_tag(x_1490) == 0)
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; 
if (lean_is_exclusive(x_1490)) {
 lean_ctor_release(x_1490, 0);
 x_1491 = x_1490;
} else {
 lean_dec_ref(x_1490);
 x_1491 = lean_box(0);
}
if (lean_is_scalar(x_1477)) {
 x_1492 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1492 = x_1477;
 lean_ctor_set_tag(x_1492, 6);
}
lean_ctor_set(x_1492, 0, x_1487);
if (lean_is_scalar(x_1491)) {
 x_1493 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1493 = x_1491;
}
lean_ctor_set(x_1493, 0, x_1492);
return x_1493;
}
else
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; 
lean_dec_ref(x_1487);
lean_dec(x_1477);
x_1494 = lean_ctor_get(x_1490, 0);
lean_inc(x_1494);
if (lean_is_exclusive(x_1490)) {
 lean_ctor_release(x_1490, 0);
 x_1495 = x_1490;
} else {
 lean_dec_ref(x_1490);
 x_1495 = lean_box(0);
}
if (lean_is_scalar(x_1495)) {
 x_1496 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1496 = x_1495;
}
lean_ctor_set(x_1496, 0, x_1494);
return x_1496;
}
}
block_1514:
{
uint8_t x_1505; 
x_1505 = lean_nat_dec_lt(x_1479, x_1498);
if (x_1505 == 0)
{
lean_dec_ref(x_1503);
lean_dec(x_1501);
lean_dec(x_1500);
lean_dec_ref(x_1499);
lean_dec(x_1498);
lean_dec(x_1484);
x_1488 = x_1502;
x_1489 = lean_box(0);
goto block_1497;
}
else
{
uint8_t x_1506; 
x_1506 = lean_nat_dec_le(x_1498, x_1498);
if (x_1506 == 0)
{
lean_dec_ref(x_1503);
lean_dec(x_1501);
lean_dec(x_1500);
lean_dec_ref(x_1499);
lean_dec(x_1498);
lean_dec(x_1484);
x_1488 = x_1502;
x_1489 = lean_box(0);
goto block_1497;
}
else
{
lean_object* x_1507; size_t x_1508; size_t x_1509; lean_object* x_1510; 
x_1507 = lean_box(0);
x_1508 = 0;
x_1509 = lean_usize_of_nat(x_1498);
lean_dec(x_1498);
x_1510 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1479, x_1484, x_1508, x_1509, x_1507, x_1499, x_1500, x_1503, x_1501);
lean_dec(x_1501);
lean_dec_ref(x_1503);
lean_dec(x_1500);
lean_dec_ref(x_1499);
lean_dec(x_1484);
if (lean_obj_tag(x_1510) == 0)
{
lean_dec_ref(x_1510);
x_1488 = x_1502;
x_1489 = lean_box(0);
goto block_1497;
}
else
{
lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; 
lean_dec(x_1502);
lean_dec_ref(x_1487);
lean_dec(x_1477);
x_1511 = lean_ctor_get(x_1510, 0);
lean_inc(x_1511);
if (lean_is_exclusive(x_1510)) {
 lean_ctor_release(x_1510, 0);
 x_1512 = x_1510;
} else {
 lean_dec_ref(x_1510);
 x_1512 = lean_box(0);
}
if (lean_is_scalar(x_1512)) {
 x_1513 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1513 = x_1512;
}
lean_ctor_set(x_1513, 0, x_1511);
return x_1513;
}
}
}
}
block_1519:
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; 
if (lean_is_scalar(x_1473)) {
 x_1516 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1516 = x_1473;
}
lean_ctor_set(x_1516, 0, x_1469);
lean_ctor_set(x_1516, 1, x_1487);
lean_ctor_set(x_1516, 2, x_1476);
lean_ctor_set(x_1516, 3, x_1484);
x_1517 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1517, 0, x_1516);
if (lean_is_scalar(x_1485)) {
 x_1518 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1518 = x_1485;
}
lean_ctor_set(x_1518, 0, x_1517);
return x_1518;
}
block_1524:
{
if (x_1521 == 0)
{
lean_dec(x_1482);
lean_dec(x_1471);
lean_dec_ref(x_1);
x_1515 = lean_box(0);
goto block_1519;
}
else
{
uint8_t x_1522; 
x_1522 = l_Lean_instBEqFVarId_beq(x_1471, x_1476);
lean_dec(x_1471);
if (x_1522 == 0)
{
lean_dec(x_1482);
lean_dec_ref(x_1);
x_1515 = lean_box(0);
goto block_1519;
}
else
{
lean_object* x_1523; 
lean_dec_ref(x_1487);
lean_dec(x_1485);
lean_dec(x_1484);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec(x_1469);
if (lean_is_scalar(x_1482)) {
 x_1523 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1523 = x_1482;
}
lean_ctor_set(x_1523, 0, x_1);
return x_1523;
}
}
}
block_1546:
{
lean_object* x_1531; uint8_t x_1532; 
x_1531 = lean_array_get_size(x_1484);
x_1532 = lean_nat_dec_lt(x_1479, x_1531);
if (x_1532 == 0)
{
lean_dec(x_1485);
lean_dec(x_1482);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec_ref(x_1);
x_1498 = x_1531;
x_1499 = x_1526;
x_1500 = x_1527;
x_1501 = x_1529;
x_1502 = x_1525;
x_1503 = x_1528;
x_1504 = lean_box(0);
goto block_1514;
}
else
{
if (x_1532 == 0)
{
lean_dec(x_1485);
lean_dec(x_1482);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec_ref(x_1);
x_1498 = x_1531;
x_1499 = x_1526;
x_1500 = x_1527;
x_1501 = x_1529;
x_1502 = x_1525;
x_1503 = x_1528;
x_1504 = lean_box(0);
goto block_1514;
}
else
{
size_t x_1533; size_t x_1534; uint8_t x_1535; 
x_1533 = 0;
x_1534 = lean_usize_of_nat(x_1531);
x_1535 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(x_122, x_1484, x_1533, x_1534);
if (x_1535 == 0)
{
lean_dec(x_1485);
lean_dec(x_1482);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec_ref(x_1);
x_1498 = x_1531;
x_1499 = x_1526;
x_1500 = x_1527;
x_1501 = x_1529;
x_1502 = x_1525;
x_1503 = x_1528;
x_1504 = lean_box(0);
goto block_1514;
}
else
{
if (x_122 == 0)
{
lean_object* x_1536; 
lean_dec(x_1529);
lean_dec_ref(x_1528);
lean_dec(x_1527);
lean_dec_ref(x_1526);
lean_dec(x_1477);
lean_inc(x_1476);
x_1536 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1476, x_1525);
lean_dec(x_1525);
if (lean_obj_tag(x_1536) == 0)
{
size_t x_1537; size_t x_1538; uint8_t x_1539; 
lean_dec_ref(x_1536);
x_1537 = lean_ptr_addr(x_1472);
lean_dec_ref(x_1472);
x_1538 = lean_ptr_addr(x_1484);
x_1539 = lean_usize_dec_eq(x_1537, x_1538);
if (x_1539 == 0)
{
lean_dec_ref(x_1470);
x_1520 = lean_box(0);
x_1521 = x_1539;
goto block_1524;
}
else
{
size_t x_1540; size_t x_1541; uint8_t x_1542; 
x_1540 = lean_ptr_addr(x_1470);
lean_dec_ref(x_1470);
x_1541 = lean_ptr_addr(x_1487);
x_1542 = lean_usize_dec_eq(x_1540, x_1541);
x_1520 = lean_box(0);
x_1521 = x_1542;
goto block_1524;
}
}
else
{
lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; 
lean_dec_ref(x_1487);
lean_dec(x_1485);
lean_dec(x_1484);
lean_dec(x_1482);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec_ref(x_1);
x_1543 = lean_ctor_get(x_1536, 0);
lean_inc(x_1543);
if (lean_is_exclusive(x_1536)) {
 lean_ctor_release(x_1536, 0);
 x_1544 = x_1536;
} else {
 lean_dec_ref(x_1536);
 x_1544 = lean_box(0);
}
if (lean_is_scalar(x_1544)) {
 x_1545 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1545 = x_1544;
}
lean_ctor_set(x_1545, 0, x_1543);
return x_1545;
}
}
else
{
lean_dec(x_1485);
lean_dec(x_1482);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec_ref(x_1);
x_1498 = x_1531;
x_1499 = x_1526;
x_1500 = x_1527;
x_1501 = x_1529;
x_1502 = x_1525;
x_1503 = x_1528;
x_1504 = lean_box(0);
goto block_1514;
}
}
}
}
}
}
else
{
lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; 
lean_dec(x_1482);
lean_dec(x_1478);
lean_dec(x_1477);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec(x_1465);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1586 = lean_ctor_get(x_1483, 0);
lean_inc(x_1586);
if (lean_is_exclusive(x_1483)) {
 lean_ctor_release(x_1483, 0);
 x_1587 = x_1483;
} else {
 lean_dec_ref(x_1483);
 x_1587 = lean_box(0);
}
if (lean_is_scalar(x_1587)) {
 x_1588 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1588 = x_1587;
}
lean_ctor_set(x_1588, 0, x_1586);
return x_1588;
}
}
else
{
lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; 
lean_dec(x_1478);
lean_dec(x_1477);
lean_dec(x_1476);
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec(x_1465);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1589 = lean_ctor_get(x_1480, 0);
lean_inc(x_1589);
if (lean_is_exclusive(x_1480)) {
 lean_ctor_release(x_1480, 0);
 x_1590 = x_1480;
} else {
 lean_dec_ref(x_1480);
 x_1590 = lean_box(0);
}
if (lean_is_scalar(x_1590)) {
 x_1591 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1591 = x_1590;
}
lean_ctor_set(x_1591, 0, x_1589);
return x_1591;
}
}
else
{
lean_object* x_1592; 
lean_dec(x_1473);
lean_dec_ref(x_1472);
lean_dec(x_1471);
lean_dec_ref(x_1470);
lean_dec(x_1469);
lean_dec(x_1465);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1592 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1232, x_8);
lean_dec(x_8);
lean_dec_ref(x_1232);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1592;
}
}
}
else
{
lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; 
lean_dec_ref(x_1462);
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1593 = lean_ctor_get(x_1463, 0);
lean_inc(x_1593);
if (lean_is_exclusive(x_1463)) {
 lean_ctor_release(x_1463, 0);
 x_1594 = x_1463;
} else {
 lean_dec_ref(x_1463);
 x_1594 = lean_box(0);
}
if (lean_is_scalar(x_1594)) {
 x_1595 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1595 = x_1594;
}
lean_ctor_set(x_1595, 0, x_1593);
return x_1595;
}
}
case 5:
{
lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
lean_dec(x_1181);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1596 = lean_ctor_get(x_1, 0);
x_1597 = lean_st_ref_get(x_3);
x_1598 = lean_ctor_get(x_1597, 0);
lean_inc_ref(x_1598);
lean_dec(x_1597);
lean_inc(x_1596);
x_1599 = l_Lean_Compiler_LCNF_normFVarImp(x_1598, x_1596, x_122);
lean_dec_ref(x_1598);
if (lean_obj_tag(x_1599) == 0)
{
lean_object* x_1600; lean_object* x_1601; 
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1600 = lean_ctor_get(x_1599, 0);
lean_inc(x_1600);
lean_dec_ref(x_1599);
lean_inc(x_1600);
x_1601 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1600, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1601) == 0)
{
lean_object* x_1602; uint8_t x_1603; 
if (lean_is_exclusive(x_1601)) {
 lean_ctor_release(x_1601, 0);
 x_1602 = x_1601;
} else {
 lean_dec_ref(x_1601);
 x_1602 = lean_box(0);
}
x_1603 = l_Lean_instBEqFVarId_beq(x_1596, x_1600);
if (x_1603 == 0)
{
lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1604 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1604 = lean_box(0);
}
if (lean_is_scalar(x_1604)) {
 x_1605 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1605 = x_1604;
}
lean_ctor_set(x_1605, 0, x_1600);
if (lean_is_scalar(x_1602)) {
 x_1606 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1606 = x_1602;
}
lean_ctor_set(x_1606, 0, x_1605);
return x_1606;
}
else
{
lean_object* x_1607; 
lean_dec(x_1600);
if (lean_is_scalar(x_1602)) {
 x_1607 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1607 = x_1602;
}
lean_ctor_set(x_1607, 0, x_1);
return x_1607;
}
}
else
{
lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; 
lean_dec(x_1600);
lean_dec_ref(x_1);
x_1608 = lean_ctor_get(x_1601, 0);
lean_inc(x_1608);
if (lean_is_exclusive(x_1601)) {
 lean_ctor_release(x_1601, 0);
 x_1609 = x_1601;
} else {
 lean_dec_ref(x_1601);
 x_1609 = lean_box(0);
}
if (lean_is_scalar(x_1609)) {
 x_1610 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1610 = x_1609;
}
lean_ctor_set(x_1610, 0, x_1608);
return x_1610;
}
}
else
{
lean_object* x_1611; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1611 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1232, x_8);
lean_dec(x_8);
lean_dec_ref(x_1232);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1611;
}
}
case 6:
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; size_t x_1616; size_t x_1617; uint8_t x_1618; 
lean_dec_ref(x_1232);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1612 = lean_ctor_get(x_1, 0);
x_1613 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_1614 = lean_ctor_get(x_1613, 0);
lean_inc_ref(x_1614);
lean_dec(x_1613);
lean_inc_ref(x_1612);
x_1615 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1614, x_122, x_1612);
lean_dec_ref(x_1614);
x_1616 = lean_ptr_addr(x_1612);
x_1617 = lean_ptr_addr(x_1615);
x_1618 = lean_usize_dec_eq(x_1616, x_1617);
if (x_1618 == 0)
{
lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1619 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1619 = lean_box(0);
}
if (lean_is_scalar(x_1619)) {
 x_1620 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1620 = x_1619;
}
lean_ctor_set(x_1620, 0, x_1615);
if (lean_is_scalar(x_1181)) {
 x_1621 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1621 = x_1181;
}
lean_ctor_set(x_1621, 0, x_1620);
return x_1621;
}
else
{
lean_object* x_1622; 
lean_dec_ref(x_1615);
if (lean_is_scalar(x_1181)) {
 x_1622 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1622 = x_1181;
}
lean_ctor_set(x_1622, 0, x_1);
return x_1622;
}
}
default: 
{
lean_object* x_1623; lean_object* x_1624; 
lean_dec(x_1181);
x_1623 = lean_ctor_get(x_1, 0);
x_1624 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1624);
lean_inc_ref(x_1623);
x_1182 = x_1623;
x_1183 = x_1624;
x_1184 = x_2;
x_1185 = x_3;
x_1186 = x_4;
x_1187 = x_5;
x_1188 = x_6;
x_1189 = x_1232;
x_1190 = x_8;
goto block_1229;
}
}
block_1229:
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
x_1191 = lean_ctor_get(x_1182, 0);
x_1192 = lean_ctor_get(x_1182, 2);
x_1193 = lean_ctor_get(x_1182, 3);
x_1194 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_1191, x_1185);
if (lean_obj_tag(x_1194) == 0)
{
lean_object* x_1195; uint8_t x_1196; 
x_1195 = lean_ctor_get(x_1194, 0);
lean_inc(x_1195);
lean_dec_ref(x_1194);
x_1196 = lean_unbox(x_1195);
if (x_1196 == 0)
{
uint8_t x_1197; 
x_1197 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
if (x_1197 == 0)
{
uint8_t x_1198; 
x_1198 = lean_unbox(x_1195);
lean_dec(x_1195);
x_81 = x_1183;
x_82 = x_1198;
x_83 = x_1182;
x_84 = x_1184;
x_85 = x_1185;
x_86 = x_1186;
x_87 = x_1187;
x_88 = x_1188;
x_89 = x_1189;
x_90 = x_1190;
x_91 = lean_box(0);
goto block_97;
}
else
{
uint8_t x_1199; 
lean_inc_ref(x_1193);
x_1199 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_1193, x_1192);
if (x_1199 == 0)
{
uint8_t x_1200; 
x_1200 = lean_unbox(x_1195);
lean_dec(x_1195);
x_81 = x_1183;
x_82 = x_1200;
x_83 = x_1182;
x_84 = x_1184;
x_85 = x_1185;
x_86 = x_1186;
x_87 = x_1187;
x_88 = x_1188;
x_89 = x_1189;
x_90 = x_1190;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
x_1201 = lean_st_ref_get(x_1185);
x_1202 = lean_ctor_get(x_1201, 0);
lean_inc_ref(x_1202);
lean_dec(x_1201);
x_1203 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_1182, x_1202, x_1187, x_1188, x_1189, x_1190);
lean_dec_ref(x_1202);
if (lean_obj_tag(x_1203) == 0)
{
lean_object* x_1204; lean_object* x_1205; 
x_1204 = lean_ctor_get(x_1203, 0);
lean_inc(x_1204);
lean_dec_ref(x_1203);
lean_inc(x_1190);
lean_inc_ref(x_1189);
lean_inc(x_1188);
lean_inc_ref(x_1187);
x_1205 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_1204, x_1187, x_1188, x_1189, x_1190);
if (lean_obj_tag(x_1205) == 0)
{
lean_object* x_1206; lean_object* x_1207; 
x_1206 = lean_ctor_get(x_1205, 0);
lean_inc(x_1206);
lean_dec_ref(x_1205);
x_1207 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1185);
if (lean_obj_tag(x_1207) == 0)
{
uint8_t x_1208; 
lean_dec_ref(x_1207);
x_1208 = lean_unbox(x_1195);
lean_dec(x_1195);
x_81 = x_1183;
x_82 = x_1208;
x_83 = x_1206;
x_84 = x_1184;
x_85 = x_1185;
x_86 = x_1186;
x_87 = x_1187;
x_88 = x_1188;
x_89 = x_1189;
x_90 = x_1190;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
lean_dec(x_1206);
lean_dec(x_1195);
lean_dec(x_1190);
lean_dec_ref(x_1189);
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec_ref(x_1186);
lean_dec(x_1185);
lean_dec_ref(x_1184);
lean_dec_ref(x_1183);
lean_dec_ref(x_1);
x_1209 = lean_ctor_get(x_1207, 0);
lean_inc(x_1209);
if (lean_is_exclusive(x_1207)) {
 lean_ctor_release(x_1207, 0);
 x_1210 = x_1207;
} else {
 lean_dec_ref(x_1207);
 x_1210 = lean_box(0);
}
if (lean_is_scalar(x_1210)) {
 x_1211 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1211 = x_1210;
}
lean_ctor_set(x_1211, 0, x_1209);
return x_1211;
}
}
else
{
lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
lean_dec(x_1195);
lean_dec(x_1190);
lean_dec_ref(x_1189);
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec_ref(x_1186);
lean_dec(x_1185);
lean_dec_ref(x_1184);
lean_dec_ref(x_1183);
lean_dec_ref(x_1);
x_1212 = lean_ctor_get(x_1205, 0);
lean_inc(x_1212);
if (lean_is_exclusive(x_1205)) {
 lean_ctor_release(x_1205, 0);
 x_1213 = x_1205;
} else {
 lean_dec_ref(x_1205);
 x_1213 = lean_box(0);
}
if (lean_is_scalar(x_1213)) {
 x_1214 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1214 = x_1213;
}
lean_ctor_set(x_1214, 0, x_1212);
return x_1214;
}
}
else
{
lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; 
lean_dec(x_1195);
lean_dec(x_1190);
lean_dec_ref(x_1189);
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec_ref(x_1186);
lean_dec(x_1185);
lean_dec_ref(x_1184);
lean_dec_ref(x_1183);
lean_dec_ref(x_1);
x_1215 = lean_ctor_get(x_1203, 0);
lean_inc(x_1215);
if (lean_is_exclusive(x_1203)) {
 lean_ctor_release(x_1203, 0);
 x_1216 = x_1203;
} else {
 lean_dec_ref(x_1203);
 x_1216 = lean_box(0);
}
if (lean_is_scalar(x_1216)) {
 x_1217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1217 = x_1216;
}
lean_ctor_set(x_1217, 0, x_1215);
return x_1217;
}
}
}
}
else
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; 
x_1218 = lean_st_ref_get(x_1185);
x_1219 = lean_ctor_get(x_1218, 0);
lean_inc_ref(x_1219);
lean_dec(x_1218);
x_1220 = l_Lean_Compiler_LCNF_normFunDeclImp(x_122, x_1182, x_1219, x_1187, x_1188, x_1189, x_1190);
lean_dec_ref(x_1219);
if (lean_obj_tag(x_1220) == 0)
{
lean_object* x_1221; uint8_t x_1222; 
x_1221 = lean_ctor_get(x_1220, 0);
lean_inc(x_1221);
lean_dec_ref(x_1220);
x_1222 = lean_unbox(x_1195);
lean_dec(x_1195);
x_49 = x_1183;
x_50 = x_1222;
x_51 = x_1221;
x_52 = x_1184;
x_53 = x_1185;
x_54 = x_1186;
x_55 = x_1187;
x_56 = x_1188;
x_57 = x_1189;
x_58 = x_1190;
x_59 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; 
lean_dec(x_1195);
lean_dec(x_1190);
lean_dec_ref(x_1189);
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec_ref(x_1186);
lean_dec(x_1185);
lean_dec_ref(x_1184);
lean_dec_ref(x_1183);
lean_dec_ref(x_1);
x_1223 = lean_ctor_get(x_1220, 0);
lean_inc(x_1223);
if (lean_is_exclusive(x_1220)) {
 lean_ctor_release(x_1220, 0);
 x_1224 = x_1220;
} else {
 lean_dec_ref(x_1220);
 x_1224 = lean_box(0);
}
if (lean_is_scalar(x_1224)) {
 x_1225 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1225 = x_1224;
}
lean_ctor_set(x_1225, 0, x_1223);
return x_1225;
}
}
}
else
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
lean_dec(x_1190);
lean_dec_ref(x_1189);
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec_ref(x_1186);
lean_dec(x_1185);
lean_dec_ref(x_1184);
lean_dec_ref(x_1183);
lean_dec_ref(x_1182);
lean_dec_ref(x_1);
x_1226 = lean_ctor_get(x_1194, 0);
lean_inc(x_1226);
if (lean_is_exclusive(x_1194)) {
 lean_ctor_release(x_1194, 0);
 x_1227 = x_1194;
} else {
 lean_dec_ref(x_1194);
 x_1227 = lean_box(0);
}
if (lean_is_scalar(x_1227)) {
 x_1228 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1228 = x_1227;
}
lean_ctor_set(x_1228, 0, x_1226);
return x_1228;
}
}
}
else
{
lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; 
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
x_1625 = lean_ctor_get(x_1180, 0);
lean_inc(x_1625);
if (lean_is_exclusive(x_1180)) {
 lean_ctor_release(x_1180, 0);
 x_1626 = x_1180;
} else {
 lean_dec_ref(x_1180);
 x_1626 = lean_box(0);
}
if (lean_is_scalar(x_1626)) {
 x_1627 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1627 = x_1626;
}
lean_ctor_set(x_1627, 0, x_1625);
return x_1627;
}
}
}
else
{
lean_object* x_1628; 
lean_dec_ref(x_1);
x_1628 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1628;
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
x_46 = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0(x_45);
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
x_60 = l_Lean_Compiler_LCNF_Simp_simp(x_49, x_52, x_53, x_54, x_55, x_56, x_57, x_58);
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
if (x_50 == 0)
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
lean_dec_ref(x_81);
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
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_100);
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
lean_dec(x_10);
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
lean_dec(x_10);
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
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1, x_6, x_7, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_spec__5(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0);
l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2);
l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0 = _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0);
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
l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
