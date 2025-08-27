// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Main
// Imports: Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.ElimDead Lean.Compiler.LCNF.AlphaEqv Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.Simp.FunDeclInfo Lean.Compiler.LCNF.Simp.InlineCandidate Lean.Compiler.LCNF.Simp.InlineProj Lean.Compiler.LCNF.Simp.Used Lean.Compiler.LCNF.Simp.DefaultAlt Lean.Compiler.LCNF.Simp.SimpValue Lean.Compiler.LCNF.Simp.ConstantFold
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
uint8_t l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic_4164288206____hygCtx___hyg_104_(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Compiler_LCNF_defaultAlt____x40_Lean_Compiler_LCNF_Basic_2228446694____hygCtx___hyg_273_;
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(lean_object*);
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
uint64_t l_Lean_hashFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_39_(lean_object*);
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
extern lean_object* l_Lean_Compiler_LCNF_defaultParam____x40_Lean_Compiler_LCNF_Basic_2211743917____hygCtx___hyg_43_;
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic_915775888____hygCtx___hyg_49_(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getCode(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_Simp_simp_spec__0___closed__0;
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_defaultAlt____x40_Lean_Compiler_LCNF_Basic_2898322213____hygCtx___hyg_7_;
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
x_1 = l_Lean_Compiler_LCNF_defaultAlt____x40_Lean_Compiler_LCNF_Basic_2898322213____hygCtx___hyg_7_;
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
x_6 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_4, x_1);
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
x_7 = l_Lean_hashFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_39_(x_4);
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
x_26 = l_Lean_hashFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_39_(x_22);
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
x_8 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_5, x_1);
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
x_13 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_10, x_1);
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
x_8 = l_Lean_hashFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_39_(x_2);
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
x_40 = l_Lean_hashFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_39_(x_2);
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
static lean_object* _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___closed__0;
x_17 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_16);
lean_inc(x_15);
lean_inc(x_12);
x_18 = lean_apply_2(x_17, x_12, x_15);
x_19 = lean_unbox(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_array_fget_borrowed(x_22, x_15);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_25, 2);
x_28 = lean_unbox(x_18);
lean_inc_ref(x_27);
x_29 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_27, x_24, x_28, x_8);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = 0;
x_33 = l_Lean_Compiler_LCNF_mkAuxParam(x_30, x_32, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_15, x_37);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_38);
x_39 = lean_array_push(x_23, x_34);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_36);
lean_inc(x_26);
x_41 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_24, x_26, x_40);
lean_ctor_set(x_3, 1, x_41);
lean_ctor_set(x_3, 0, x_39);
x_8 = x_35;
goto _start;
}
else
{
uint8_t x_43; 
lean_free_object(x_3);
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
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
lean_free_object(x_3);
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
return x_29;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_29, 0);
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_29);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_3);
x_54 = lean_array_fget_borrowed(x_51, x_15);
x_55 = lean_ctor_get(x_54, 0);
x_56 = lean_ctor_get(x_54, 2);
x_57 = lean_unbox(x_18);
lean_inc_ref(x_56);
x_58 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_56, x_53, x_57, x_8);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = 0;
x_62 = l_Lean_Compiler_LCNF_mkAuxParam(x_59, x_61, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_15, x_66);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_67);
x_68 = lean_array_push(x_52, x_63);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_65);
lean_inc(x_55);
x_70 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_53, x_55, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_3 = x_71;
x_8 = x_64;
goto _start;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_73 = lean_ctor_get(x_62, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_75 = x_62;
} else {
 lean_dec_ref(x_62);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
x_77 = lean_ctor_get(x_58, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_58, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_79 = x_58;
} else {
 lean_dec_ref(x_58);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_9, 0);
lean_inc(x_81);
lean_dec(x_9);
x_82 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___closed__0;
x_83 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_82);
lean_inc(x_81);
lean_inc(x_12);
x_84 = lean_apply_2(x_83, x_12, x_81);
x_85 = lean_unbox(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_81);
lean_free_object(x_2);
lean_dec(x_12);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_3);
lean_ctor_set(x_86, 1, x_8);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_1, 0);
x_88 = lean_ctor_get(x_3, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_3, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_90 = x_3;
} else {
 lean_dec_ref(x_3);
 x_90 = lean_box(0);
}
x_91 = lean_array_fget_borrowed(x_87, x_81);
x_92 = lean_ctor_get(x_91, 0);
x_93 = lean_ctor_get(x_91, 2);
x_94 = lean_unbox(x_84);
lean_inc_ref(x_93);
x_95 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_93, x_89, x_94, x_8);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = 0;
x_99 = l_Lean_Compiler_LCNF_mkAuxParam(x_96, x_98, x_4, x_5, x_6, x_7, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_add(x_81, x_103);
lean_dec(x_81);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_2, 0, x_105);
x_106 = lean_array_push(x_88, x_100);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_102);
lean_inc(x_92);
x_108 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_89, x_92, x_107);
if (lean_is_scalar(x_90)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_90;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_3 = x_109;
x_8 = x_101;
goto _start;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_81);
lean_free_object(x_2);
lean_dec(x_12);
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_99, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_113 = x_99;
} else {
 lean_dec_ref(x_99);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_81);
lean_free_object(x_2);
lean_dec(x_12);
x_115 = lean_ctor_get(x_95, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_95, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_117 = x_95;
} else {
 lean_dec_ref(x_95);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_119 = lean_ctor_get(x_2, 1);
lean_inc(x_119);
lean_dec(x_2);
x_120 = lean_ctor_get(x_9, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_121 = x_9;
} else {
 lean_dec_ref(x_9);
 x_121 = lean_box(0);
}
x_122 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___closed__0;
x_123 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_122);
lean_inc(x_120);
lean_inc(x_119);
x_124 = lean_apply_2(x_123, x_119, x_120);
x_125 = lean_unbox(x_124);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_3);
lean_ctor_set(x_126, 1, x_8);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; 
x_127 = lean_ctor_get(x_1, 0);
x_128 = lean_ctor_get(x_3, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_3, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_130 = x_3;
} else {
 lean_dec_ref(x_3);
 x_130 = lean_box(0);
}
x_131 = lean_array_fget_borrowed(x_127, x_120);
x_132 = lean_ctor_get(x_131, 0);
x_133 = lean_ctor_get(x_131, 2);
x_134 = lean_unbox(x_124);
lean_inc_ref(x_133);
x_135 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_133, x_129, x_134, x_8);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec_ref(x_135);
x_138 = 0;
x_139 = l_Lean_Compiler_LCNF_mkAuxParam(x_136, x_138, x_4, x_5, x_6, x_7, x_137);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec_ref(x_139);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_add(x_120, x_143);
lean_dec(x_120);
if (lean_is_scalar(x_121)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_121;
}
lean_ctor_set(x_145, 0, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_119);
x_147 = lean_array_push(x_128, x_140);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_142);
lean_inc(x_132);
x_149 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_129, x_132, x_148);
if (lean_is_scalar(x_130)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_130;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
x_2 = x_146;
x_3 = x_150;
x_8 = x_141;
goto _start;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
x_152 = lean_ctor_get(x_139, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_139, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_154 = x_139;
} else {
 lean_dec_ref(x_139);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_135, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_158 = x_135;
} else {
 lean_dec_ref(x_135);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
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
lean_free_object(x_20);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_26);
x_75 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_76 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_63, x_74, x_75, x_4, x_5, x_6, x_7, x_72);
lean_dec_ref(x_4);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_inc(x_15);
x_80 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_79, x_3, x_5, x_6, x_7, x_78);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_81);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
lean_ctor_set(x_46, 0, x_77);
lean_ctor_set(x_82, 0, x_46);
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
lean_ctor_set(x_46, 0, x_77);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_46);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
uint8_t x_87; 
lean_dec(x_77);
lean_free_object(x_46);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
return x_82;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_82);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_77);
lean_free_object(x_46);
lean_dec(x_5);
lean_dec_ref(x_1);
x_91 = !lean_is_exclusive(x_80);
if (x_91 == 0)
{
return x_80;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_80, 0);
x_93 = lean_ctor_get(x_80, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_80);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_free_object(x_46);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_76);
if (x_95 == 0)
{
return x_76;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_76, 0);
x_97 = lean_ctor_get(x_76, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_76);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_63);
lean_free_object(x_46);
lean_free_object(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_99 = !lean_is_exclusive(x_70);
if (x_99 == 0)
{
return x_70;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_70, 0);
x_101 = lean_ctor_get(x_70, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_70);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_free_object(x_46);
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_103 = !lean_is_exclusive(x_62);
if (x_103 == 0)
{
return x_62;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_62, 0);
x_105 = lean_ctor_get(x_62, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_62);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_46, 0);
lean_inc(x_107);
lean_dec(x_46);
x_108 = lean_array_get_size(x_19);
x_109 = l_Lean_Compiler_LCNF_Decl_getArity(x_107);
lean_dec(x_107);
x_110 = lean_nat_dec_lt(x_108, x_109);
lean_dec(x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; 
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_111 = lean_box(0);
lean_ctor_set(x_45, 0, x_111);
return x_45;
}
else
{
lean_object* x_112; 
lean_free_object(x_45);
lean_inc_ref(x_16);
x_112 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; size_t x_115; size_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec_ref(x_112);
x_115 = lean_array_size(x_113);
x_116 = 0;
lean_inc(x_113);
x_117 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_115, x_116, x_113);
x_118 = l_Array_append___redArg(x_19, x_117);
lean_dec_ref(x_117);
lean_ctor_set(x_13, 2, x_118);
x_119 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_120 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_119, x_4, x_5, x_6, x_7, x_114);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_123);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_26);
x_125 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_126 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_113, x_124, x_125, x_4, x_5, x_6, x_7, x_122);
lean_dec_ref(x_4);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_inc(x_15);
x_130 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_129, x_3, x_5, x_6, x_7, x_128);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_131);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_127);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_127);
x_137 = lean_ctor_get(x_132, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_139 = x_132;
} else {
 lean_dec_ref(x_132);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_127);
lean_dec(x_5);
lean_dec_ref(x_1);
x_141 = lean_ctor_get(x_130, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_130, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_143 = x_130;
} else {
 lean_dec_ref(x_130);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_145 = lean_ctor_get(x_126, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_126, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_147 = x_126;
} else {
 lean_dec_ref(x_126);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_113);
lean_free_object(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_149 = lean_ctor_get(x_120, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_120, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_151 = x_120;
} else {
 lean_dec_ref(x_120);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_153 = lean_ctor_get(x_112, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_112, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_155 = x_112;
} else {
 lean_dec_ref(x_112);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_157 = lean_ctor_get(x_45, 1);
lean_inc(x_157);
lean_dec(x_45);
x_158 = lean_ctor_get(x_46, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_159 = x_46;
} else {
 lean_dec_ref(x_46);
 x_159 = lean_box(0);
}
x_160 = lean_array_get_size(x_19);
x_161 = l_Lean_Compiler_LCNF_Decl_getArity(x_158);
lean_dec(x_158);
x_162 = lean_nat_dec_lt(x_160, x_161);
lean_dec(x_161);
lean_dec(x_160);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_159);
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_157);
return x_164;
}
else
{
lean_object* x_165; 
lean_inc_ref(x_16);
x_165 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7, x_157);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; size_t x_168; size_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = lean_array_size(x_166);
x_169 = 0;
lean_inc(x_166);
x_170 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_168, x_169, x_166);
x_171 = l_Array_append___redArg(x_19, x_170);
lean_dec_ref(x_170);
lean_ctor_set(x_13, 2, x_171);
x_172 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_173 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_172, x_4, x_5, x_6, x_7, x_167);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec_ref(x_173);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_176);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_26);
x_178 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_179 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_166, x_177, x_178, x_4, x_5, x_6, x_7, x_175);
lean_dec_ref(x_4);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec_ref(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_inc(x_15);
x_183 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_182, x_3, x_5, x_6, x_7, x_181);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_184);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_159;
}
lean_ctor_set(x_188, 0, x_180);
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_187;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_186);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_180);
lean_dec(x_159);
x_190 = lean_ctor_get(x_185, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_185, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_192 = x_185;
} else {
 lean_dec_ref(x_185);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_180);
lean_dec(x_159);
lean_dec(x_5);
lean_dec_ref(x_1);
x_194 = lean_ctor_get(x_183, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_183, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_196 = x_183;
} else {
 lean_dec_ref(x_183);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_159);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_198 = lean_ctor_get(x_179, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_179, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_200 = x_179;
} else {
 lean_dec_ref(x_179);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_166);
lean_dec(x_159);
lean_free_object(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_202 = lean_ctor_get(x_173, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_173, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_204 = x_173;
} else {
 lean_dec_ref(x_173);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_159);
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_206 = lean_ctor_get(x_165, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_165, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_208 = x_165;
} else {
 lean_dec_ref(x_165);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
}
}
}
else
{
uint8_t x_210; 
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_210 = !lean_is_exclusive(x_45);
if (x_210 == 0)
{
return x_45;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_45, 0);
x_212 = lean_ctor_get(x_45, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_45);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_214 = !lean_is_exclusive(x_41);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_41, 0);
lean_dec(x_215);
x_216 = lean_box(0);
lean_ctor_set(x_41, 0, x_216);
return x_41;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_41, 1);
lean_inc(x_217);
lean_dec(x_41);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
}
else
{
uint8_t x_220; 
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_220 = !lean_is_exclusive(x_41);
if (x_220 == 0)
{
return x_41;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_41, 0);
x_222 = lean_ctor_get(x_41, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_41);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
}
else
{
uint8_t x_224; 
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_224 = !lean_is_exclusive(x_31);
if (x_224 == 0)
{
return x_31;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_31, 0);
x_226 = lean_ctor_get(x_31, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_31);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_26, 0);
lean_inc(x_228);
lean_dec(x_26);
x_229 = l_Lean_ConstantInfo_type(x_228);
lean_dec(x_228);
x_230 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_229, x_7, x_23);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_unbox(x_231);
lean_dec(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_234 = x_230;
} else {
 lean_dec_ref(x_230);
 x_234 = lean_box(0);
}
x_235 = lean_box(0);
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_233);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_230, 1);
lean_inc(x_237);
lean_dec_ref(x_230);
x_238 = l_Lean_Meta_isInstance___redArg(x_17, x_7, x_237);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_unbox(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_dec_ref(x_238);
lean_inc(x_17);
x_242 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
x_246 = lean_box(0);
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_248 = lean_ctor_get(x_242, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_249 = x_242;
} else {
 lean_dec_ref(x_242);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_243, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_251 = x_243;
} else {
 lean_dec_ref(x_243);
 x_251 = lean_box(0);
}
x_252 = lean_array_get_size(x_19);
x_253 = l_Lean_Compiler_LCNF_Decl_getArity(x_250);
lean_dec(x_250);
x_254 = lean_nat_dec_lt(x_252, x_253);
lean_dec(x_253);
lean_dec(x_252);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_251);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_255 = lean_box(0);
if (lean_is_scalar(x_249)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_249;
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_248);
return x_256;
}
else
{
lean_object* x_257; 
lean_dec(x_249);
lean_inc_ref(x_16);
x_257 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7, x_248);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; size_t x_260; size_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec_ref(x_257);
x_260 = lean_array_size(x_258);
x_261 = 0;
lean_inc(x_258);
x_262 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_260, x_261, x_258);
x_263 = l_Array_append___redArg(x_19, x_262);
lean_dec_ref(x_262);
lean_ctor_set(x_13, 2, x_263);
x_264 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_265 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_264, x_4, x_5, x_6, x_7, x_259);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec_ref(x_265);
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
x_269 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_269);
x_271 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_272 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_258, x_270, x_271, x_4, x_5, x_6, x_7, x_267);
lean_dec_ref(x_4);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec_ref(x_272);
x_275 = lean_ctor_get(x_273, 0);
lean_inc(x_275);
lean_inc(x_15);
x_276 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_275, x_3, x_5, x_6, x_7, x_274);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec_ref(x_276);
x_278 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_277);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_280 = x_278;
} else {
 lean_dec_ref(x_278);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_251;
}
lean_ctor_set(x_281, 0, x_273);
if (lean_is_scalar(x_280)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_280;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_279);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_273);
lean_dec(x_251);
x_283 = lean_ctor_get(x_278, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_278, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_285 = x_278;
} else {
 lean_dec_ref(x_278);
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
lean_dec(x_273);
lean_dec(x_251);
lean_dec(x_5);
lean_dec_ref(x_1);
x_287 = lean_ctor_get(x_276, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_276, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_289 = x_276;
} else {
 lean_dec_ref(x_276);
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
lean_dec(x_251);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_291 = lean_ctor_get(x_272, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_272, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_293 = x_272;
} else {
 lean_dec_ref(x_272);
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
lean_dec(x_258);
lean_dec(x_251);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_295 = lean_ctor_get(x_265, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_265, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_297 = x_265;
} else {
 lean_dec_ref(x_265);
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
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_251);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_299 = lean_ctor_get(x_257, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_257, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_301 = x_257;
} else {
 lean_dec_ref(x_257);
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
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_303 = lean_ctor_get(x_242, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_242, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_305 = x_242;
} else {
 lean_dec_ref(x_242);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_307 = lean_ctor_get(x_238, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_308 = x_238;
} else {
 lean_dec_ref(x_238);
 x_308 = lean_box(0);
}
x_309 = lean_box(0);
if (lean_is_scalar(x_308)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_308;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_307);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_311 = lean_ctor_get(x_238, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_238, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_313 = x_238;
} else {
 lean_dec_ref(x_238);
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
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_315 = lean_ctor_get(x_230, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_230, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_317 = x_230;
} else {
 lean_dec_ref(x_230);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; 
x_319 = lean_ctor_get(x_20, 0);
x_320 = lean_ctor_get(x_20, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_20);
x_321 = lean_ctor_get(x_319, 0);
lean_inc_ref(x_321);
lean_dec(x_319);
x_322 = 0;
lean_inc(x_17);
x_323 = l_Lean_Environment_find_x3f(x_321, x_17, x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_324 = lean_box(0);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_320);
return x_325;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_326 = lean_ctor_get(x_323, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 x_327 = x_323;
} else {
 lean_dec_ref(x_323);
 x_327 = lean_box(0);
}
x_328 = l_Lean_ConstantInfo_type(x_326);
lean_dec(x_326);
x_329 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_328, x_7, x_320);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; uint8_t x_331; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_unbox(x_330);
lean_dec(x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_327);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_333 = x_329;
} else {
 lean_dec_ref(x_329);
 x_333 = lean_box(0);
}
x_334 = lean_box(0);
if (lean_is_scalar(x_333)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_333;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_332);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_329, 1);
lean_inc(x_336);
lean_dec_ref(x_329);
x_337 = l_Lean_Meta_isInstance___redArg(x_17, x_7, x_336);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; uint8_t x_339; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_unbox(x_338);
lean_dec(x_338);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_337, 1);
lean_inc(x_340);
lean_dec_ref(x_337);
lean_inc(x_17);
x_341 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7, x_340);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_327);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_344 = x_341;
} else {
 lean_dec_ref(x_341);
 x_344 = lean_box(0);
}
x_345 = lean_box(0);
if (lean_is_scalar(x_344)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_344;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_343);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_341, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_348 = x_341;
} else {
 lean_dec_ref(x_341);
 x_348 = lean_box(0);
}
x_349 = lean_ctor_get(x_342, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 x_350 = x_342;
} else {
 lean_dec_ref(x_342);
 x_350 = lean_box(0);
}
x_351 = lean_array_get_size(x_19);
x_352 = l_Lean_Compiler_LCNF_Decl_getArity(x_349);
lean_dec(x_349);
x_353 = lean_nat_dec_lt(x_351, x_352);
lean_dec(x_352);
lean_dec(x_351);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_350);
lean_dec(x_327);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_354 = lean_box(0);
if (lean_is_scalar(x_348)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_348;
}
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_347);
return x_355;
}
else
{
lean_object* x_356; 
lean_dec(x_348);
lean_inc_ref(x_16);
x_356 = l_Lean_Compiler_LCNF_mkNewParams(x_16, x_4, x_5, x_6, x_7, x_347);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; size_t x_359; size_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec_ref(x_356);
x_359 = lean_array_size(x_357);
x_360 = 0;
lean_inc(x_357);
x_361 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_359, x_360, x_357);
x_362 = l_Array_append___redArg(x_19, x_361);
lean_dec_ref(x_361);
lean_ctor_set(x_13, 2, x_362);
x_363 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_364 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_363, x_4, x_5, x_6, x_7, x_358);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec_ref(x_364);
x_367 = lean_ctor_get(x_365, 0);
lean_inc(x_367);
if (lean_is_scalar(x_327)) {
 x_368 = lean_alloc_ctor(5, 1, 0);
} else {
 x_368 = x_327;
 lean_ctor_set_tag(x_368, 5);
}
lean_ctor_set(x_368, 0, x_367);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_365);
lean_ctor_set(x_369, 1, x_368);
x_370 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_371 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_357, x_369, x_370, x_4, x_5, x_6, x_7, x_366);
lean_dec_ref(x_4);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
lean_dec_ref(x_371);
x_374 = lean_ctor_get(x_372, 0);
lean_inc(x_374);
lean_inc(x_15);
x_375 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_374, x_3, x_5, x_6, x_7, x_373);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec_ref(x_375);
x_377 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_376);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_379 = x_377;
} else {
 lean_dec_ref(x_377);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_380 = lean_alloc_ctor(1, 1, 0);
} else {
 x_380 = x_350;
}
lean_ctor_set(x_380, 0, x_372);
if (lean_is_scalar(x_379)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_379;
}
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_378);
return x_381;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_372);
lean_dec(x_350);
x_382 = lean_ctor_get(x_377, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_377, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_384 = x_377;
} else {
 lean_dec_ref(x_377);
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
lean_dec(x_372);
lean_dec(x_350);
lean_dec(x_5);
lean_dec_ref(x_1);
x_386 = lean_ctor_get(x_375, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_375, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_388 = x_375;
} else {
 lean_dec_ref(x_375);
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
lean_dec(x_350);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_390 = lean_ctor_get(x_371, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_371, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_392 = x_371;
} else {
 lean_dec_ref(x_371);
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
lean_dec(x_357);
lean_dec(x_350);
lean_dec(x_327);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_394 = lean_ctor_get(x_364, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_364, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_396 = x_364;
} else {
 lean_dec_ref(x_364);
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
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_350);
lean_dec(x_327);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_398 = lean_ctor_get(x_356, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_356, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_400 = x_356;
} else {
 lean_dec_ref(x_356);
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
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_327);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_402 = lean_ctor_get(x_341, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_341, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_404 = x_341;
} else {
 lean_dec_ref(x_341);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_402);
lean_ctor_set(x_405, 1, x_403);
return x_405;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_327);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_406 = lean_ctor_get(x_337, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_407 = x_337;
} else {
 lean_dec_ref(x_337);
 x_407 = lean_box(0);
}
x_408 = lean_box(0);
if (lean_is_scalar(x_407)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_407;
}
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_406);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_327);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_410 = lean_ctor_get(x_337, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_337, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_412 = x_337;
} else {
 lean_dec_ref(x_337);
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
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_327);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_414 = lean_ctor_get(x_329, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_329, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_416 = x_329;
} else {
 lean_dec_ref(x_329);
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
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; lean_object* x_429; 
x_418 = lean_ctor_get(x_1, 0);
x_419 = lean_ctor_get(x_1, 2);
x_420 = lean_ctor_get(x_13, 0);
x_421 = lean_ctor_get(x_13, 1);
x_422 = lean_ctor_get(x_13, 2);
lean_inc(x_422);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_13);
x_423 = lean_st_ref_get(x_7, x_8);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_426 = x_423;
} else {
 lean_dec_ref(x_423);
 x_426 = lean_box(0);
}
x_427 = lean_ctor_get(x_424, 0);
lean_inc_ref(x_427);
lean_dec(x_424);
x_428 = 0;
lean_inc(x_420);
x_429 = l_Lean_Environment_find_x3f(x_427, x_420, x_428);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; 
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_430 = lean_box(0);
if (lean_is_scalar(x_426)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_426;
}
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_425);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_426);
x_432 = lean_ctor_get(x_429, 0);
lean_inc(x_432);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 x_433 = x_429;
} else {
 lean_dec_ref(x_429);
 x_433 = lean_box(0);
}
x_434 = l_Lean_ConstantInfo_type(x_432);
lean_dec(x_432);
x_435 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_434, x_7, x_425);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; uint8_t x_437; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_unbox(x_436);
lean_dec(x_436);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_433);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_438 = lean_ctor_get(x_435, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_439 = x_435;
} else {
 lean_dec_ref(x_435);
 x_439 = lean_box(0);
}
x_440 = lean_box(0);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_438);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; 
x_442 = lean_ctor_get(x_435, 1);
lean_inc(x_442);
lean_dec_ref(x_435);
x_443 = l_Lean_Meta_isInstance___redArg(x_420, x_7, x_442);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; uint8_t x_445; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_unbox(x_444);
lean_dec(x_444);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_ctor_get(x_443, 1);
lean_inc(x_446);
lean_dec_ref(x_443);
lean_inc(x_420);
x_447 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_420, x_4, x_7, x_446);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_433);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_450 = x_447;
} else {
 lean_dec_ref(x_447);
 x_450 = lean_box(0);
}
x_451 = lean_box(0);
if (lean_is_scalar(x_450)) {
 x_452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_452 = x_450;
}
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_449);
return x_452;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; 
x_453 = lean_ctor_get(x_447, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_454 = x_447;
} else {
 lean_dec_ref(x_447);
 x_454 = lean_box(0);
}
x_455 = lean_ctor_get(x_448, 0);
lean_inc(x_455);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 x_456 = x_448;
} else {
 lean_dec_ref(x_448);
 x_456 = lean_box(0);
}
x_457 = lean_array_get_size(x_422);
x_458 = l_Lean_Compiler_LCNF_Decl_getArity(x_455);
lean_dec(x_455);
x_459 = lean_nat_dec_lt(x_457, x_458);
lean_dec(x_458);
lean_dec(x_457);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; 
lean_dec(x_456);
lean_dec(x_433);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_460 = lean_box(0);
if (lean_is_scalar(x_454)) {
 x_461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_461 = x_454;
}
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_453);
return x_461;
}
else
{
lean_object* x_462; 
lean_dec(x_454);
lean_inc_ref(x_419);
x_462 = l_Lean_Compiler_LCNF_mkNewParams(x_419, x_4, x_5, x_6, x_7, x_453);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; size_t x_465; size_t x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec_ref(x_462);
x_465 = lean_array_size(x_463);
x_466 = 0;
lean_inc(x_463);
x_467 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_465, x_466, x_463);
x_468 = l_Array_append___redArg(x_422, x_467);
lean_dec_ref(x_467);
x_469 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_469, 0, x_420);
lean_ctor_set(x_469, 1, x_421);
lean_ctor_set(x_469, 2, x_468);
x_470 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_471 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_469, x_470, x_4, x_5, x_6, x_7, x_464);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec_ref(x_471);
x_474 = lean_ctor_get(x_472, 0);
lean_inc(x_474);
if (lean_is_scalar(x_433)) {
 x_475 = lean_alloc_ctor(5, 1, 0);
} else {
 x_475 = x_433;
 lean_ctor_set_tag(x_475, 5);
}
lean_ctor_set(x_475, 0, x_474);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_472);
lean_ctor_set(x_476, 1, x_475);
x_477 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_478 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_463, x_476, x_477, x_4, x_5, x_6, x_7, x_473);
lean_dec_ref(x_4);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec_ref(x_478);
x_481 = lean_ctor_get(x_479, 0);
lean_inc(x_481);
lean_inc(x_418);
x_482 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_418, x_481, x_3, x_5, x_6, x_7, x_480);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
lean_dec_ref(x_482);
x_484 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_483);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_486 = x_484;
} else {
 lean_dec_ref(x_484);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_487 = lean_alloc_ctor(1, 1, 0);
} else {
 x_487 = x_456;
}
lean_ctor_set(x_487, 0, x_479);
if (lean_is_scalar(x_486)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_486;
}
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_485);
return x_488;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_479);
lean_dec(x_456);
x_489 = lean_ctor_get(x_484, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_484, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_491 = x_484;
} else {
 lean_dec_ref(x_484);
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
lean_dec(x_479);
lean_dec(x_456);
lean_dec(x_5);
lean_dec_ref(x_1);
x_493 = lean_ctor_get(x_482, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_482, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_495 = x_482;
} else {
 lean_dec_ref(x_482);
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
lean_dec(x_456);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_497 = lean_ctor_get(x_478, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_478, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_499 = x_478;
} else {
 lean_dec_ref(x_478);
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
lean_dec(x_463);
lean_dec(x_456);
lean_dec(x_433);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_501 = lean_ctor_get(x_471, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_471, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 x_503 = x_471;
} else {
 lean_dec_ref(x_471);
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
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_456);
lean_dec(x_433);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_505 = lean_ctor_get(x_462, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_462, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_507 = x_462;
} else {
 lean_dec_ref(x_462);
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
}
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_433);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_509 = lean_ctor_get(x_447, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_447, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_511 = x_447;
} else {
 lean_dec_ref(x_447);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(1, 2, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_509);
lean_ctor_set(x_512, 1, x_510);
return x_512;
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_433);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_513 = lean_ctor_get(x_443, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_514 = x_443;
} else {
 lean_dec_ref(x_443);
 x_514 = lean_box(0);
}
x_515 = lean_box(0);
if (lean_is_scalar(x_514)) {
 x_516 = lean_alloc_ctor(0, 2, 0);
} else {
 x_516 = x_514;
}
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_513);
return x_516;
}
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_433);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_517 = lean_ctor_get(x_443, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_443, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_519 = x_443;
} else {
 lean_dec_ref(x_443);
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
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_433);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_521 = lean_ctor_get(x_435, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_435, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_523 = x_435;
} else {
 lean_dec_ref(x_435);
 x_523 = lean_box(0);
}
if (lean_is_scalar(x_523)) {
 x_524 = lean_alloc_ctor(1, 2, 0);
} else {
 x_524 = x_523;
}
lean_ctor_set(x_524, 0, x_521);
lean_ctor_set(x_524, 1, x_522);
return x_524;
}
}
}
}
else
{
lean_object* x_525; lean_object* x_526; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_525 = lean_box(0);
x_526 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_8);
return x_526;
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
x_13 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_12, x_2);
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
x_22 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_21, x_2);
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
lean_inc(x_34);
lean_inc_ref(x_39);
lean_inc(x_41);
lean_inc_ref(x_43);
lean_inc_ref(x_35);
lean_inc(x_40);
lean_inc_ref(x_42);
x_44 = l_Lean_Compiler_LCNF_Simp_simp(x_36, x_42, x_40, x_35, x_43, x_41, x_39, x_34, x_33);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_40, x_46);
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
lean_dec_ref(x_37);
x_50 = l_Lean_Compiler_LCNF_inferAppType(x_26, x_38, x_43, x_41, x_39, x_34, x_48);
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
x_55 = l_Lean_Compiler_LCNF_mkAuxParam(x_51, x_32, x_43, x_41, x_39, x_34, x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_34);
lean_inc_ref(x_39);
lean_inc(x_41);
lean_inc_ref(x_43);
lean_inc(x_58);
x_59 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_30, x_29, x_11, x_2, x_27, x_58, x_42, x_40, x_35, x_43, x_41, x_39, x_34, x_57);
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
x_66 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_64, x_60, x_65, x_43, x_41, x_39, x_34, x_61);
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
x_70 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_45, x_69, x_43, x_41, x_39, x_34, x_68);
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
lean_dec_ref(x_43);
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec(x_34);
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
lean_dec_ref(x_43);
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec(x_34);
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
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_35);
lean_dec(x_34);
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
x_98 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_96, x_45, x_97, x_43, x_41, x_39, x_34, x_52);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
lean_inc(x_34);
lean_inc_ref(x_39);
lean_inc(x_41);
lean_inc_ref(x_43);
x_101 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_99, x_43, x_41, x_39, x_34, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_34);
lean_inc_ref(x_39);
lean_inc(x_41);
lean_inc_ref(x_43);
lean_inc_ref(x_35);
lean_inc(x_40);
lean_inc_ref(x_42);
lean_inc(x_104);
x_105 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_30, x_29, x_11, x_2, x_27, x_104, x_42, x_40, x_35, x_43, x_41, x_39, x_34, x_103);
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
x_111 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_110, x_106, x_42, x_40, x_35, x_43, x_41, x_39, x_34, x_107);
lean_dec(x_34);
lean_dec_ref(x_39);
lean_dec(x_41);
lean_dec_ref(x_43);
lean_dec_ref(x_35);
lean_dec(x_40);
lean_dec_ref(x_42);
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
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_35);
lean_dec(x_34);
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
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_35);
lean_dec(x_34);
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
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_35);
lean_dec(x_34);
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
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_35);
lean_dec(x_34);
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
lean_dec_ref(x_42);
lean_dec(x_40);
lean_dec_ref(x_38);
lean_dec_ref(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_11);
lean_dec_ref(x_2);
x_139 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_45, x_37, x_43, x_41, x_39, x_34, x_48);
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
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_35);
lean_dec(x_34);
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
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_35);
lean_dec(x_34);
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
lean_inc(x_160);
lean_inc_ref(x_163);
lean_inc(x_165);
lean_inc_ref(x_168);
lean_inc_ref(x_172);
x_173 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_24, x_25, x_172, x_32, x_166, x_164, x_161, x_168, x_165, x_163, x_160, x_167);
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
x_33 = x_175;
x_34 = x_160;
x_35 = x_161;
x_36 = x_174;
x_37 = x_162;
x_38 = x_172;
x_39 = x_163;
x_40 = x_164;
x_41 = x_165;
x_42 = x_166;
x_43 = x_168;
goto block_159;
}
else
{
uint8_t x_177; 
x_177 = lean_nat_dec_eq(x_29, x_30);
if (x_177 == 0)
{
x_33 = x_175;
x_34 = x_160;
x_35 = x_161;
x_36 = x_174;
x_37 = x_162;
x_38 = x_172;
x_39 = x_163;
x_40 = x_164;
x_41 = x_165;
x_42 = x_166;
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
x_178 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_164, x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec_ref(x_178);
x_180 = l_Lean_Compiler_LCNF_Simp_simp(x_174, x_166, x_164, x_161, x_168, x_165, x_163, x_160, x_179);
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
lean_dec_ref(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec_ref(x_163);
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
lean_dec_ref(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec_ref(x_163);
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
x_160 = x_207;
x_161 = x_203;
x_162 = x_209;
x_163 = x_206;
x_164 = x_202;
x_165 = x_205;
x_166 = x_201;
x_167 = x_208;
x_168 = x_204;
x_169 = x_210;
x_170 = x_29;
goto block_200;
}
else
{
lean_inc(x_30);
x_160 = x_207;
x_161 = x_203;
x_162 = x_209;
x_163 = x_206;
x_164 = x_202;
x_165 = x_205;
x_166 = x_201;
x_167 = x_208;
x_168 = x_204;
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
x_1 = l_Lean_Compiler_LCNF_defaultAlt____x40_Lean_Compiler_LCNF_Basic_2228446694____hygCtx___hyg_273_;
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_50; uint8_t x_51; lean_object* x_74; uint8_t x_75; uint8_t x_77; lean_object* x_78; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
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
x_33 = x_74;
goto block_49;
}
else
{
x_50 = x_74;
x_51 = x_75;
goto block_73;
}
}
block_79:
{
if (lean_obj_tag(x_32) == 6)
{
x_74 = x_78;
x_75 = x_77;
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
x_74 = x_78;
x_75 = x_77;
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
x_3 = lean_unsigned_to_nat(319u);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_134; lean_object* x_135; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec_ref(x_70);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_add(x_41, x_134);
lean_dec(x_41);
lean_ctor_set(x_7, 3, x_135);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_336; 
x_136 = lean_ctor_get(x_1, 0);
x_137 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_136);
x_336 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_54, x_136, x_3, x_6, x_71);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_381; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec_ref(x_336);
x_381 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic_915775888____hygCtx___hyg_49_(x_136, x_337);
if (x_381 == 0)
{
goto block_380;
}
else
{
if (x_54 == 0)
{
x_339 = x_2;
x_340 = x_3;
x_341 = x_4;
x_342 = x_5;
x_343 = x_6;
x_344 = x_7;
x_345 = x_8;
x_346 = x_338;
goto block_373;
}
else
{
goto block_380;
}
}
block_373:
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_337, 2);
x_348 = lean_ctor_get(x_337, 3);
lean_inc(x_345);
lean_inc_ref(x_344);
lean_inc(x_343);
lean_inc_ref(x_342);
lean_inc_ref(x_341);
lean_inc(x_348);
x_349 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_348, x_339, x_341, x_342, x_343, x_344, x_345, x_346);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; 
lean_inc(x_348);
lean_inc_ref(x_347);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec_ref(x_349);
x_321 = x_337;
x_322 = x_347;
x_323 = x_348;
x_324 = x_339;
x_325 = x_340;
x_326 = x_341;
x_327 = x_342;
x_328 = x_343;
x_329 = x_344;
x_330 = x_345;
x_331 = x_351;
goto block_335;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
lean_dec_ref(x_349);
x_353 = lean_ctor_get(x_350, 0);
lean_inc(x_353);
lean_dec_ref(x_350);
x_354 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_340, x_352);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
lean_dec_ref(x_354);
x_356 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_337, x_353, x_343, x_355);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec_ref(x_356);
x_359 = lean_ctor_get(x_357, 2);
lean_inc_ref(x_359);
x_360 = lean_ctor_get(x_357, 3);
lean_inc(x_360);
x_321 = x_357;
x_322 = x_359;
x_323 = x_360;
x_324 = x_339;
x_325 = x_340;
x_326 = x_341;
x_327 = x_342;
x_328 = x_343;
x_329 = x_344;
x_330 = x_345;
x_331 = x_358;
goto block_335;
}
else
{
uint8_t x_361; 
lean_dec(x_345);
lean_dec_ref(x_344);
lean_dec(x_343);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_1);
x_361 = !lean_is_exclusive(x_356);
if (x_361 == 0)
{
return x_356;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_356, 0);
x_363 = lean_ctor_get(x_356, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_356);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
else
{
uint8_t x_365; 
lean_dec(x_353);
lean_dec(x_345);
lean_dec_ref(x_344);
lean_dec(x_343);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec(x_340);
lean_dec_ref(x_339);
lean_dec(x_337);
lean_dec_ref(x_1);
x_365 = !lean_is_exclusive(x_354);
if (x_365 == 0)
{
return x_354;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_354, 0);
x_367 = lean_ctor_get(x_354, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_354);
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
}
}
}
else
{
uint8_t x_369; 
lean_dec(x_345);
lean_dec_ref(x_344);
lean_dec(x_343);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec(x_340);
lean_dec_ref(x_339);
lean_dec(x_337);
lean_dec_ref(x_1);
x_369 = !lean_is_exclusive(x_349);
if (x_369 == 0)
{
return x_349;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_349, 0);
x_371 = lean_ctor_get(x_349, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_349);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
block_380:
{
lean_object* x_374; 
x_374 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_338);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; 
x_375 = lean_ctor_get(x_374, 1);
lean_inc(x_375);
lean_dec_ref(x_374);
x_339 = x_2;
x_340 = x_3;
x_341 = x_4;
x_342 = x_5;
x_343 = x_6;
x_344 = x_7;
x_345 = x_8;
x_346 = x_375;
goto block_373;
}
else
{
uint8_t x_376; 
lean_dec(x_337);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_376 = !lean_is_exclusive(x_374);
if (x_376 == 0)
{
return x_374;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_374, 0);
x_378 = lean_ctor_get(x_374, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_374);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
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
x_382 = !lean_is_exclusive(x_336);
if (x_382 == 0)
{
return x_336;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_336, 0);
x_384 = lean_ctor_get(x_336, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_336);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
block_320:
{
if (x_147 == 0)
{
lean_object* x_148; 
lean_inc(x_142);
lean_inc_ref(x_143);
lean_inc(x_144);
lean_inc_ref(x_146);
lean_inc_ref(x_140);
x_148 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_140, x_146, x_144, x_143, x_142, x_145);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec_ref(x_148);
lean_inc(x_142);
lean_inc_ref(x_143);
lean_inc(x_144);
lean_inc_ref(x_146);
lean_inc_ref(x_140);
x_151 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_140, x_141, x_139, x_146, x_144, x_143, x_142, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec_ref(x_151);
x_154 = lean_ctor_get(x_140, 0);
x_155 = lean_ctor_get(x_140, 3);
lean_inc(x_155);
x_156 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_155, x_153);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec_ref(x_156);
lean_inc(x_142);
lean_inc_ref(x_143);
lean_inc(x_144);
lean_inc_ref(x_146);
lean_inc_ref(x_138);
lean_inc(x_139);
lean_inc_ref(x_141);
lean_inc_ref(x_137);
lean_inc_ref(x_140);
x_159 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_140, x_137, x_141, x_139, x_138, x_146, x_144, x_143, x_142, x_158);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
lean_inc(x_142);
lean_inc_ref(x_143);
lean_inc(x_144);
lean_inc_ref(x_146);
lean_inc_ref(x_138);
lean_inc(x_139);
lean_inc_ref(x_141);
lean_inc(x_155);
x_162 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_155, x_141, x_139, x_138, x_146, x_144, x_143, x_142, x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec_ref(x_162);
lean_inc(x_142);
lean_inc_ref(x_143);
lean_inc(x_144);
lean_inc_ref(x_146);
lean_inc_ref(x_138);
lean_inc(x_139);
lean_inc_ref(x_141);
lean_inc_ref(x_137);
x_165 = l_Lean_Compiler_LCNF_Simp_simp(x_137, x_141, x_139, x_138, x_146, x_144, x_143, x_142, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_154, x_139, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_unbox(x_169);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec_ref(x_146);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_138);
lean_dec_ref(x_1);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec_ref(x_168);
x_172 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_140, x_139, x_144, x_171);
lean_dec(x_144);
lean_dec(x_139);
lean_dec_ref(x_140);
if (lean_obj_tag(x_172) == 0)
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_172, 0);
lean_dec(x_174);
lean_ctor_set(x_172, 0, x_166);
return x_172;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_166);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
else
{
uint8_t x_177; 
lean_dec(x_166);
x_177 = !lean_is_exclusive(x_172);
if (x_177 == 0)
{
return x_172;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_172, 0);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_172);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_168, 1);
lean_inc(x_181);
lean_dec_ref(x_168);
lean_inc_ref(x_140);
x_182 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_140, x_141, x_139, x_138, x_146, x_144, x_143, x_142, x_181);
lean_dec(x_142);
lean_dec_ref(x_143);
lean_dec(x_144);
lean_dec_ref(x_146);
lean_dec_ref(x_138);
lean_dec(x_139);
lean_dec_ref(x_141);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; size_t x_184; size_t x_185; uint8_t x_186; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = lean_ptr_addr(x_137);
x_185 = lean_ptr_addr(x_166);
x_186 = lean_usize_dec_eq(x_184, x_185);
if (x_186 == 0)
{
x_10 = x_140;
x_11 = x_183;
x_12 = x_166;
x_13 = x_186;
goto block_17;
}
else
{
size_t x_187; size_t x_188; uint8_t x_189; 
x_187 = lean_ptr_addr(x_136);
x_188 = lean_ptr_addr(x_140);
x_189 = lean_usize_dec_eq(x_187, x_188);
x_10 = x_140;
x_11 = x_183;
x_12 = x_166;
x_13 = x_189;
goto block_17;
}
}
else
{
uint8_t x_190; 
lean_dec(x_166);
lean_dec_ref(x_140);
lean_dec_ref(x_1);
x_190 = !lean_is_exclusive(x_182);
if (x_190 == 0)
{
return x_182;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_182, 0);
x_192 = lean_ctor_get(x_182, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_182);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_166);
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_1);
x_194 = !lean_is_exclusive(x_168);
if (x_194 == 0)
{
return x_168;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_168, 0);
x_196 = lean_ctor_get(x_168, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_168);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_1);
return x_165;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_inc_ref(x_137);
lean_dec_ref(x_1);
x_198 = lean_ctor_get(x_163, 0);
lean_inc(x_198);
lean_dec_ref(x_163);
x_199 = lean_ctor_get(x_162, 1);
lean_inc(x_199);
lean_dec_ref(x_162);
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
lean_inc(x_154);
x_202 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_154, x_201, x_139, x_144, x_143, x_142, x_199);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec_ref(x_202);
x_204 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_140, x_139, x_144, x_203);
lean_dec_ref(x_140);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec_ref(x_204);
lean_inc(x_142);
lean_inc_ref(x_143);
lean_inc(x_144);
lean_inc_ref(x_146);
lean_inc_ref(x_138);
lean_inc(x_139);
lean_inc_ref(x_141);
x_206 = l_Lean_Compiler_LCNF_Simp_simp(x_137, x_141, x_139, x_138, x_146, x_144, x_143, x_142, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec_ref(x_206);
x_209 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_200, x_207, x_141, x_139, x_138, x_146, x_144, x_143, x_142, x_208);
lean_dec(x_142);
lean_dec_ref(x_143);
lean_dec(x_144);
lean_dec_ref(x_146);
lean_dec_ref(x_138);
lean_dec(x_139);
lean_dec_ref(x_141);
lean_dec(x_200);
return x_209;
}
else
{
lean_dec(x_200);
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_139);
lean_dec_ref(x_138);
return x_206;
}
}
else
{
uint8_t x_210; 
lean_dec(x_200);
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
x_210 = !lean_is_exclusive(x_204);
if (x_210 == 0)
{
return x_204;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_204, 0);
x_212 = lean_ctor_get(x_204, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_204);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_200);
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
x_214 = !lean_is_exclusive(x_202);
if (x_214 == 0)
{
return x_202;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_202, 0);
x_216 = lean_ctor_get(x_202, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_202);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_1);
x_218 = !lean_is_exclusive(x_162);
if (x_218 == 0)
{
return x_162;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_162, 0);
x_220 = lean_ctor_get(x_162, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_162);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec_ref(x_146);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_138);
lean_dec_ref(x_1);
x_222 = lean_ctor_get(x_159, 1);
lean_inc(x_222);
lean_dec_ref(x_159);
x_223 = lean_ctor_get(x_160, 0);
lean_inc(x_223);
lean_dec_ref(x_160);
x_224 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_140, x_139, x_144, x_222);
lean_dec(x_144);
lean_dec(x_139);
lean_dec_ref(x_140);
if (lean_obj_tag(x_224) == 0)
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_224, 0);
lean_dec(x_226);
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_223);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
else
{
uint8_t x_229; 
lean_dec(x_223);
x_229 = !lean_is_exclusive(x_224);
if (x_229 == 0)
{
return x_224;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_224, 0);
x_231 = lean_ctor_get(x_224, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_224);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
}
else
{
uint8_t x_233; 
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_1);
x_233 = !lean_is_exclusive(x_159);
if (x_233 == 0)
{
return x_159;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_159, 0);
x_235 = lean_ctor_get(x_159, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_159);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_inc_ref(x_137);
lean_dec_ref(x_1);
x_237 = lean_ctor_get(x_156, 1);
lean_inc(x_237);
lean_dec_ref(x_156);
x_238 = lean_ctor_get(x_157, 0);
lean_inc(x_238);
lean_dec_ref(x_157);
lean_inc(x_154);
x_239 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_154, x_238, x_139, x_144, x_143, x_142, x_237);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec_ref(x_239);
x_241 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_140, x_139, x_144, x_240);
lean_dec_ref(x_140);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec_ref(x_241);
x_1 = x_137;
x_2 = x_141;
x_3 = x_139;
x_4 = x_138;
x_5 = x_146;
x_6 = x_144;
x_7 = x_143;
x_8 = x_142;
x_9 = x_242;
goto _start;
}
else
{
uint8_t x_244; 
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
x_244 = !lean_is_exclusive(x_241);
if (x_244 == 0)
{
return x_241;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_241, 0);
x_246 = lean_ctor_get(x_241, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_241);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
else
{
uint8_t x_248; 
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
x_248 = !lean_is_exclusive(x_239);
if (x_248 == 0)
{
return x_239;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_239, 0);
x_250 = lean_ctor_get(x_239, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_239);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
}
else
{
uint8_t x_252; 
lean_dec_ref(x_140);
lean_inc_ref(x_137);
x_252 = !lean_is_exclusive(x_1);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_253 = lean_ctor_get(x_1, 1);
lean_dec(x_253);
x_254 = lean_ctor_get(x_1, 0);
lean_dec(x_254);
x_255 = lean_ctor_get(x_151, 1);
lean_inc(x_255);
lean_dec_ref(x_151);
x_256 = lean_ctor_get(x_152, 0);
lean_inc(x_256);
lean_dec_ref(x_152);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_256);
x_2 = x_141;
x_3 = x_139;
x_4 = x_138;
x_5 = x_146;
x_6 = x_144;
x_7 = x_143;
x_8 = x_142;
x_9 = x_255;
goto _start;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_1);
x_258 = lean_ctor_get(x_151, 1);
lean_inc(x_258);
lean_dec_ref(x_151);
x_259 = lean_ctor_get(x_152, 0);
lean_inc(x_259);
lean_dec_ref(x_152);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_137);
x_1 = x_260;
x_2 = x_141;
x_3 = x_139;
x_4 = x_138;
x_5 = x_146;
x_6 = x_144;
x_7 = x_143;
x_8 = x_142;
x_9 = x_258;
goto _start;
}
}
}
else
{
uint8_t x_262; 
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_1);
x_262 = !lean_is_exclusive(x_151);
if (x_262 == 0)
{
return x_151;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_151, 0);
x_264 = lean_ctor_get(x_151, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_151);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec_ref(x_140);
lean_inc_ref(x_137);
lean_dec_ref(x_1);
x_266 = lean_ctor_get(x_148, 1);
lean_inc(x_266);
lean_dec_ref(x_148);
x_267 = lean_ctor_get(x_149, 0);
lean_inc(x_267);
lean_dec_ref(x_149);
x_268 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_139, x_266);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec_ref(x_268);
lean_inc(x_142);
lean_inc_ref(x_143);
lean_inc(x_144);
lean_inc_ref(x_146);
lean_inc_ref(x_138);
lean_inc(x_139);
lean_inc_ref(x_141);
x_270 = l_Lean_Compiler_LCNF_Simp_simp(x_137, x_141, x_139, x_138, x_146, x_144, x_143, x_142, x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec_ref(x_270);
x_273 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_267, x_271, x_141, x_139, x_138, x_146, x_144, x_143, x_142, x_272);
lean_dec(x_142);
lean_dec_ref(x_143);
lean_dec(x_144);
lean_dec_ref(x_146);
lean_dec_ref(x_138);
lean_dec(x_139);
lean_dec_ref(x_141);
lean_dec(x_267);
return x_273;
}
else
{
lean_dec(x_267);
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_139);
lean_dec_ref(x_138);
return x_270;
}
}
else
{
uint8_t x_274; 
lean_dec(x_267);
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
x_274 = !lean_is_exclusive(x_268);
if (x_274 == 0)
{
return x_268;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_268, 0);
x_276 = lean_ctor_get(x_268, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_268);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
}
}
}
else
{
uint8_t x_278; 
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_1);
x_278 = !lean_is_exclusive(x_148);
if (x_278 == 0)
{
return x_148;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_148, 0);
x_280 = lean_ctor_get(x_148, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_148);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
lean_inc_ref(x_137);
lean_dec_ref(x_1);
x_282 = lean_st_ref_take(x_139, x_145);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec_ref(x_282);
x_285 = !lean_is_exclusive(x_283);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_286 = lean_ctor_get(x_140, 0);
x_287 = lean_ctor_get(x_283, 0);
x_288 = lean_box(0);
lean_inc(x_286);
x_289 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_287, x_286, x_288);
lean_ctor_set(x_283, 0, x_289);
x_290 = lean_st_ref_set(x_139, x_283, x_284);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec_ref(x_290);
x_292 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_140, x_139, x_144, x_291);
lean_dec_ref(x_140);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec_ref(x_292);
x_1 = x_137;
x_2 = x_141;
x_3 = x_139;
x_4 = x_138;
x_5 = x_146;
x_6 = x_144;
x_7 = x_143;
x_8 = x_142;
x_9 = x_293;
goto _start;
}
else
{
uint8_t x_295; 
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
x_295 = !lean_is_exclusive(x_292);
if (x_295 == 0)
{
return x_292;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_292, 0);
x_297 = lean_ctor_get(x_292, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_292);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_299 = lean_ctor_get(x_140, 0);
x_300 = lean_ctor_get(x_283, 0);
x_301 = lean_ctor_get(x_283, 1);
x_302 = lean_ctor_get(x_283, 2);
x_303 = lean_ctor_get(x_283, 3);
x_304 = lean_ctor_get_uint8(x_283, sizeof(void*)*7);
x_305 = lean_ctor_get(x_283, 4);
x_306 = lean_ctor_get(x_283, 5);
x_307 = lean_ctor_get(x_283, 6);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_283);
x_308 = lean_box(0);
lean_inc(x_299);
x_309 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_300, x_299, x_308);
x_310 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_301);
lean_ctor_set(x_310, 2, x_302);
lean_ctor_set(x_310, 3, x_303);
lean_ctor_set(x_310, 4, x_305);
lean_ctor_set(x_310, 5, x_306);
lean_ctor_set(x_310, 6, x_307);
lean_ctor_set_uint8(x_310, sizeof(void*)*7, x_304);
x_311 = lean_st_ref_set(x_139, x_310, x_284);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
lean_dec_ref(x_311);
x_313 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_140, x_139, x_144, x_312);
lean_dec_ref(x_140);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec_ref(x_313);
x_1 = x_137;
x_2 = x_141;
x_3 = x_139;
x_4 = x_138;
x_5 = x_146;
x_6 = x_144;
x_7 = x_143;
x_8 = x_142;
x_9 = x_314;
goto _start;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
x_316 = lean_ctor_get(x_313, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_313, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_318 = x_313;
} else {
 lean_dec_ref(x_313);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
}
}
}
block_335:
{
uint8_t x_332; 
x_332 = l_Lean_Expr_isErased(x_322);
lean_dec_ref(x_322);
if (x_332 == 0)
{
lean_dec(x_323);
x_138 = x_326;
x_139 = x_325;
x_140 = x_321;
x_141 = x_324;
x_142 = x_330;
x_143 = x_329;
x_144 = x_328;
x_145 = x_331;
x_146 = x_327;
x_147 = x_54;
goto block_320;
}
else
{
lean_object* x_333; uint8_t x_334; 
x_333 = lean_box(1);
x_334 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic_4164288206____hygCtx___hyg_104_(x_323, x_333);
lean_dec(x_323);
if (x_334 == 0)
{
x_138 = x_326;
x_139 = x_325;
x_140 = x_321;
x_141 = x_324;
x_142 = x_330;
x_143 = x_329;
x_144 = x_328;
x_145 = x_331;
x_146 = x_327;
x_147 = x_332;
goto block_320;
}
else
{
x_138 = x_326;
x_139 = x_325;
x_140 = x_321;
x_141 = x_324;
x_142 = x_330;
x_143 = x_329;
x_144 = x_328;
x_145 = x_331;
x_146 = x_327;
x_147 = x_54;
goto block_320;
}
}
}
}
case 3:
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_386 = lean_ctor_get(x_1, 0);
x_387 = lean_ctor_get(x_1, 1);
x_388 = lean_st_ref_get(x_3, x_71);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec_ref(x_388);
x_391 = lean_ctor_get(x_389, 0);
lean_inc_ref(x_391);
lean_dec(x_389);
lean_inc(x_386);
x_392 = l_Lean_Compiler_LCNF_normFVarImp(x_391, x_386, x_54);
lean_dec_ref(x_391);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_408; lean_object* x_414; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
lean_dec_ref(x_392);
lean_inc_ref(x_387);
x_394 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_54, x_387, x_3, x_390);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_397 = x_394;
} else {
 lean_dec_ref(x_394);
 x_397 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_395);
x_414 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_393, x_395, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_396);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec_ref(x_414);
lean_inc(x_393);
x_417 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_393, x_3, x_416);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; 
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec_ref(x_417);
x_419 = lean_unsigned_to_nat(0u);
x_420 = lean_array_get_size(x_395);
x_421 = lean_nat_dec_lt(x_419, x_420);
if (x_421 == 0)
{
lean_dec(x_420);
lean_dec(x_3);
x_408 = x_418;
goto block_413;
}
else
{
uint8_t x_422; 
x_422 = lean_nat_dec_le(x_420, x_420);
if (x_422 == 0)
{
lean_dec(x_420);
lean_dec(x_3);
x_408 = x_418;
goto block_413;
}
else
{
lean_object* x_423; size_t x_424; size_t x_425; lean_object* x_426; 
x_423 = lean_box(0);
x_424 = 0;
x_425 = lean_usize_of_nat(x_420);
lean_dec(x_420);
x_426 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_395, x_424, x_425, x_423, x_3, x_418);
lean_dec(x_3);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_426, 1);
lean_inc(x_427);
lean_dec_ref(x_426);
x_408 = x_427;
goto block_413;
}
else
{
uint8_t x_428; 
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_393);
lean_dec_ref(x_1);
x_428 = !lean_is_exclusive(x_426);
if (x_428 == 0)
{
return x_426;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_426, 0);
x_430 = lean_ctor_get(x_426, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_426);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
}
}
}
}
else
{
uint8_t x_432; 
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_393);
lean_dec(x_3);
lean_dec_ref(x_1);
x_432 = !lean_is_exclusive(x_417);
if (x_432 == 0)
{
return x_417;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_433 = lean_ctor_get(x_417, 0);
x_434 = lean_ctor_get(x_417, 1);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_417);
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
return x_435;
}
}
}
else
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_393);
lean_dec_ref(x_1);
x_436 = lean_ctor_get(x_414, 1);
lean_inc(x_436);
lean_dec_ref(x_414);
x_437 = lean_ctor_get(x_415, 0);
lean_inc(x_437);
lean_dec_ref(x_415);
x_1 = x_437;
x_9 = x_436;
goto _start;
}
}
else
{
uint8_t x_439; 
lean_dec(x_397);
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
x_439 = !lean_is_exclusive(x_414);
if (x_439 == 0)
{
return x_414;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_414, 0);
x_441 = lean_ctor_get(x_414, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_414);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
block_407:
{
if (x_399 == 0)
{
uint8_t x_400; 
x_400 = !lean_is_exclusive(x_1);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_1, 1);
lean_dec(x_401);
x_402 = lean_ctor_get(x_1, 0);
lean_dec(x_402);
lean_ctor_set(x_1, 1, x_395);
lean_ctor_set(x_1, 0, x_393);
if (lean_is_scalar(x_397)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_397;
}
lean_ctor_set(x_403, 0, x_1);
lean_ctor_set(x_403, 1, x_398);
return x_403;
}
else
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_1);
x_404 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_404, 0, x_393);
lean_ctor_set(x_404, 1, x_395);
if (lean_is_scalar(x_397)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_397;
}
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_398);
return x_405;
}
}
else
{
lean_object* x_406; 
lean_dec(x_395);
lean_dec(x_393);
if (lean_is_scalar(x_397)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_397;
}
lean_ctor_set(x_406, 0, x_1);
lean_ctor_set(x_406, 1, x_398);
return x_406;
}
}
block_413:
{
uint8_t x_409; 
x_409 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_386, x_393);
if (x_409 == 0)
{
x_398 = x_408;
x_399 = x_409;
goto block_407;
}
else
{
size_t x_410; size_t x_411; uint8_t x_412; 
x_410 = lean_ptr_addr(x_387);
x_411 = lean_ptr_addr(x_395);
x_412 = lean_usize_dec_eq(x_410, x_411);
x_398 = x_408;
x_399 = x_412;
goto block_407;
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
x_443 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_390);
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
x_445 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_444, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_71);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec_ref(x_445);
x_448 = lean_st_ref_get(x_3, x_447);
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec_ref(x_448);
x_451 = lean_ctor_get(x_444, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_444, 1);
lean_inc_ref(x_452);
x_453 = lean_ctor_get(x_444, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_444, 3);
lean_inc_ref(x_454);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 lean_ctor_release(x_444, 2);
 lean_ctor_release(x_444, 3);
 x_455 = x_444;
} else {
 lean_dec_ref(x_444);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_449, 0);
lean_inc_ref(x_456);
lean_dec(x_449);
lean_inc(x_453);
x_457 = l_Lean_Compiler_LCNF_normFVarImp(x_456, x_453, x_54);
lean_dec_ref(x_456);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 x_459 = x_457;
} else {
 lean_dec_ref(x_457);
 x_459 = lean_box(0);
}
x_460 = lean_st_ref_get(x_3, x_450);
x_461 = !lean_is_exclusive(x_460);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_462 = lean_ctor_get(x_460, 0);
x_463 = lean_ctor_get(x_460, 1);
x_464 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_454);
lean_inc(x_458);
x_465 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_458, x_54, x_464, x_454, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_463);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_468 = x_465;
} else {
 lean_dec_ref(x_465);
 x_468 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_469 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_466, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_467);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_480; uint8_t x_481; lean_object* x_485; lean_object* x_486; lean_object* x_500; uint8_t x_501; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_472 = x_469;
} else {
 lean_dec_ref(x_469);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_462, 0);
lean_inc_ref(x_473);
lean_dec(x_462);
lean_inc_ref(x_452);
x_474 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_473, x_54, x_452);
lean_dec_ref(x_473);
x_500 = lean_array_get_size(x_470);
x_501 = lean_nat_dec_eq(x_500, x_134);
lean_dec(x_500);
if (x_501 == 0)
{
lean_free_object(x_460);
lean_dec(x_6);
x_485 = x_3;
x_486 = x_471;
goto block_499;
}
else
{
lean_object* x_502; 
x_502 = lean_array_fget_borrowed(x_470, x_464);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_516; lean_object* x_517; uint8_t x_530; lean_object* x_531; uint8_t x_533; 
lean_free_object(x_460);
x_503 = lean_ctor_get(x_502, 1);
x_504 = lean_ctor_get(x_502, 2);
x_516 = lean_array_get_size(x_503);
x_533 = lean_nat_dec_lt(x_464, x_516);
if (x_533 == 0)
{
x_530 = x_54;
x_531 = x_471;
goto block_532;
}
else
{
if (x_533 == 0)
{
x_530 = x_54;
x_531 = x_471;
goto block_532;
}
else
{
size_t x_534; size_t x_535; lean_object* x_536; 
x_534 = 0;
x_535 = lean_usize_of_nat(x_516);
x_536 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_503, x_534, x_535, x_3, x_471);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; uint8_t x_539; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec_ref(x_536);
x_539 = lean_unbox(x_537);
lean_dec(x_537);
x_530 = x_539;
x_531 = x_538;
goto block_532;
}
else
{
uint8_t x_540; 
lean_dec(x_516);
lean_dec_ref(x_474);
lean_dec(x_472);
lean_dec(x_470);
lean_dec(x_468);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_540 = !lean_is_exclusive(x_536);
if (x_540 == 0)
{
return x_536;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_536, 0);
x_542 = lean_ctor_get(x_536, 1);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_536);
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_541);
lean_ctor_set(x_543, 1, x_542);
return x_543;
}
}
}
}
block_515:
{
lean_object* x_506; 
x_506 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_505);
lean_dec(x_3);
if (lean_obj_tag(x_506) == 0)
{
uint8_t x_507; 
x_507 = !lean_is_exclusive(x_506);
if (x_507 == 0)
{
lean_object* x_508; 
x_508 = lean_ctor_get(x_506, 0);
lean_dec(x_508);
lean_ctor_set(x_506, 0, x_504);
return x_506;
}
else
{
lean_object* x_509; lean_object* x_510; 
x_509 = lean_ctor_get(x_506, 1);
lean_inc(x_509);
lean_dec(x_506);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_504);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
else
{
uint8_t x_511; 
lean_dec_ref(x_504);
x_511 = !lean_is_exclusive(x_506);
if (x_511 == 0)
{
return x_506;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_512 = lean_ctor_get(x_506, 0);
x_513 = lean_ctor_get(x_506, 1);
lean_inc(x_513);
lean_inc(x_512);
lean_dec(x_506);
x_514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
return x_514;
}
}
}
block_529:
{
uint8_t x_518; 
x_518 = lean_nat_dec_lt(x_464, x_516);
if (x_518 == 0)
{
lean_dec(x_516);
lean_dec_ref(x_503);
lean_dec(x_6);
x_505 = x_517;
goto block_515;
}
else
{
uint8_t x_519; 
x_519 = lean_nat_dec_le(x_516, x_516);
if (x_519 == 0)
{
lean_dec(x_516);
lean_dec_ref(x_503);
lean_dec(x_6);
x_505 = x_517;
goto block_515;
}
else
{
lean_object* x_520; size_t x_521; size_t x_522; lean_object* x_523; 
x_520 = lean_box(0);
x_521 = 0;
x_522 = lean_usize_of_nat(x_516);
lean_dec(x_516);
x_523 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_503, x_521, x_522, x_520, x_6, x_517);
lean_dec(x_6);
lean_dec_ref(x_503);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; 
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
lean_dec_ref(x_523);
x_505 = x_524;
goto block_515;
}
else
{
uint8_t x_525; 
lean_dec_ref(x_504);
lean_dec(x_3);
x_525 = !lean_is_exclusive(x_523);
if (x_525 == 0)
{
return x_523;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_ctor_get(x_523, 0);
x_527 = lean_ctor_get(x_523, 1);
lean_inc(x_527);
lean_inc(x_526);
lean_dec(x_523);
x_528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_527);
return x_528;
}
}
}
}
}
block_532:
{
if (x_530 == 0)
{
lean_inc_ref(x_504);
lean_inc_ref(x_503);
lean_dec_ref(x_474);
lean_dec(x_472);
lean_dec(x_470);
lean_dec(x_468);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_1);
x_517 = x_531;
goto block_529;
}
else
{
if (x_54 == 0)
{
lean_dec(x_516);
lean_dec(x_6);
x_485 = x_3;
x_486 = x_531;
goto block_499;
}
else
{
lean_inc_ref(x_504);
lean_inc_ref(x_503);
lean_dec_ref(x_474);
lean_dec(x_472);
lean_dec(x_470);
lean_dec(x_468);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_1);
x_517 = x_531;
goto block_529;
}
}
}
}
else
{
lean_object* x_544; 
lean_inc_ref(x_502);
lean_dec_ref(x_474);
lean_dec(x_472);
lean_dec(x_470);
lean_dec(x_468);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_544 = lean_ctor_get(x_502, 0);
lean_inc_ref(x_544);
lean_dec_ref(x_502);
lean_ctor_set(x_460, 1, x_471);
lean_ctor_set(x_460, 0, x_544);
return x_460;
}
}
block_479:
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
if (lean_is_scalar(x_455)) {
 x_476 = lean_alloc_ctor(0, 4, 0);
} else {
 x_476 = x_455;
}
lean_ctor_set(x_476, 0, x_451);
lean_ctor_set(x_476, 1, x_474);
lean_ctor_set(x_476, 2, x_458);
lean_ctor_set(x_476, 3, x_470);
if (lean_is_scalar(x_459)) {
 x_477 = lean_alloc_ctor(4, 1, 0);
} else {
 x_477 = x_459;
 lean_ctor_set_tag(x_477, 4);
}
lean_ctor_set(x_477, 0, x_476);
if (lean_is_scalar(x_472)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_472;
}
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_475);
return x_478;
}
block_484:
{
if (x_481 == 0)
{
lean_dec(x_468);
lean_dec(x_453);
lean_dec_ref(x_1);
x_475 = x_480;
goto block_479;
}
else
{
uint8_t x_482; 
x_482 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_453, x_458);
lean_dec(x_453);
if (x_482 == 0)
{
lean_dec(x_468);
lean_dec_ref(x_1);
x_475 = x_480;
goto block_479;
}
else
{
lean_object* x_483; 
lean_dec_ref(x_474);
lean_dec(x_472);
lean_dec(x_470);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec(x_451);
if (lean_is_scalar(x_468)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_468;
}
lean_ctor_set(x_483, 0, x_1);
lean_ctor_set(x_483, 1, x_480);
return x_483;
}
}
}
block_499:
{
lean_object* x_487; 
lean_inc(x_458);
x_487 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_458, x_485, x_486);
lean_dec(x_485);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; size_t x_489; size_t x_490; uint8_t x_491; 
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
lean_dec_ref(x_487);
x_489 = lean_ptr_addr(x_454);
lean_dec_ref(x_454);
x_490 = lean_ptr_addr(x_470);
x_491 = lean_usize_dec_eq(x_489, x_490);
if (x_491 == 0)
{
lean_dec_ref(x_452);
x_480 = x_488;
x_481 = x_491;
goto block_484;
}
else
{
size_t x_492; size_t x_493; uint8_t x_494; 
x_492 = lean_ptr_addr(x_452);
lean_dec_ref(x_452);
x_493 = lean_ptr_addr(x_474);
x_494 = lean_usize_dec_eq(x_492, x_493);
x_480 = x_488;
x_481 = x_494;
goto block_484;
}
}
else
{
uint8_t x_495; 
lean_dec_ref(x_474);
lean_dec(x_472);
lean_dec(x_470);
lean_dec(x_468);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_1);
x_495 = !lean_is_exclusive(x_487);
if (x_495 == 0)
{
return x_487;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_487, 0);
x_497 = lean_ctor_get(x_487, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_487);
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
return x_498;
}
}
}
}
else
{
uint8_t x_545; 
lean_dec(x_468);
lean_free_object(x_460);
lean_dec(x_462);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_545 = !lean_is_exclusive(x_469);
if (x_545 == 0)
{
return x_469;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_469, 0);
x_547 = lean_ctor_get(x_469, 1);
lean_inc(x_547);
lean_inc(x_546);
lean_dec(x_469);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
return x_548;
}
}
}
else
{
uint8_t x_549; 
lean_free_object(x_460);
lean_dec(x_462);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_549 = !lean_is_exclusive(x_465);
if (x_549 == 0)
{
return x_465;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_465, 0);
x_551 = lean_ctor_get(x_465, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_465);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_553 = lean_ctor_get(x_460, 0);
x_554 = lean_ctor_get(x_460, 1);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_460);
x_555 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_454);
lean_inc(x_458);
x_556 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_458, x_54, x_555, x_454, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_554);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_559 = x_556;
} else {
 lean_dec_ref(x_556);
 x_559 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_560 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_557, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_558);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_571; uint8_t x_572; lean_object* x_576; lean_object* x_577; lean_object* x_591; uint8_t x_592; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_563 = x_560;
} else {
 lean_dec_ref(x_560);
 x_563 = lean_box(0);
}
x_564 = lean_ctor_get(x_553, 0);
lean_inc_ref(x_564);
lean_dec(x_553);
lean_inc_ref(x_452);
x_565 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_564, x_54, x_452);
lean_dec_ref(x_564);
x_591 = lean_array_get_size(x_561);
x_592 = lean_nat_dec_eq(x_591, x_134);
lean_dec(x_591);
if (x_592 == 0)
{
lean_dec(x_6);
x_576 = x_3;
x_577 = x_562;
goto block_590;
}
else
{
lean_object* x_593; 
x_593 = lean_array_fget_borrowed(x_561, x_555);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_606; lean_object* x_607; uint8_t x_620; lean_object* x_621; uint8_t x_623; 
x_594 = lean_ctor_get(x_593, 1);
x_595 = lean_ctor_get(x_593, 2);
x_606 = lean_array_get_size(x_594);
x_623 = lean_nat_dec_lt(x_555, x_606);
if (x_623 == 0)
{
x_620 = x_54;
x_621 = x_562;
goto block_622;
}
else
{
if (x_623 == 0)
{
x_620 = x_54;
x_621 = x_562;
goto block_622;
}
else
{
size_t x_624; size_t x_625; lean_object* x_626; 
x_624 = 0;
x_625 = lean_usize_of_nat(x_606);
x_626 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_594, x_624, x_625, x_3, x_562);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; uint8_t x_629; 
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_626, 1);
lean_inc(x_628);
lean_dec_ref(x_626);
x_629 = lean_unbox(x_627);
lean_dec(x_627);
x_620 = x_629;
x_621 = x_628;
goto block_622;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
lean_dec(x_606);
lean_dec_ref(x_565);
lean_dec(x_563);
lean_dec(x_561);
lean_dec(x_559);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_630 = lean_ctor_get(x_626, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_626, 1);
lean_inc(x_631);
if (lean_is_exclusive(x_626)) {
 lean_ctor_release(x_626, 0);
 lean_ctor_release(x_626, 1);
 x_632 = x_626;
} else {
 lean_dec_ref(x_626);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(1, 2, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_630);
lean_ctor_set(x_633, 1, x_631);
return x_633;
}
}
}
block_605:
{
lean_object* x_597; 
x_597 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_596);
lean_dec(x_3);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_597, 1);
lean_inc(x_598);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 x_599 = x_597;
} else {
 lean_dec_ref(x_597);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(0, 2, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_595);
lean_ctor_set(x_600, 1, x_598);
return x_600;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec_ref(x_595);
x_601 = lean_ctor_get(x_597, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_597, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 x_603 = x_597;
} else {
 lean_dec_ref(x_597);
 x_603 = lean_box(0);
}
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(1, 2, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_601);
lean_ctor_set(x_604, 1, x_602);
return x_604;
}
}
block_619:
{
uint8_t x_608; 
x_608 = lean_nat_dec_lt(x_555, x_606);
if (x_608 == 0)
{
lean_dec(x_606);
lean_dec_ref(x_594);
lean_dec(x_6);
x_596 = x_607;
goto block_605;
}
else
{
uint8_t x_609; 
x_609 = lean_nat_dec_le(x_606, x_606);
if (x_609 == 0)
{
lean_dec(x_606);
lean_dec_ref(x_594);
lean_dec(x_6);
x_596 = x_607;
goto block_605;
}
else
{
lean_object* x_610; size_t x_611; size_t x_612; lean_object* x_613; 
x_610 = lean_box(0);
x_611 = 0;
x_612 = lean_usize_of_nat(x_606);
lean_dec(x_606);
x_613 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_594, x_611, x_612, x_610, x_6, x_607);
lean_dec(x_6);
lean_dec_ref(x_594);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; 
x_614 = lean_ctor_get(x_613, 1);
lean_inc(x_614);
lean_dec_ref(x_613);
x_596 = x_614;
goto block_605;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec_ref(x_595);
lean_dec(x_3);
x_615 = lean_ctor_get(x_613, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_613, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_617 = x_613;
} else {
 lean_dec_ref(x_613);
 x_617 = lean_box(0);
}
if (lean_is_scalar(x_617)) {
 x_618 = lean_alloc_ctor(1, 2, 0);
} else {
 x_618 = x_617;
}
lean_ctor_set(x_618, 0, x_615);
lean_ctor_set(x_618, 1, x_616);
return x_618;
}
}
}
}
block_622:
{
if (x_620 == 0)
{
lean_inc_ref(x_595);
lean_inc_ref(x_594);
lean_dec_ref(x_565);
lean_dec(x_563);
lean_dec(x_561);
lean_dec(x_559);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_1);
x_607 = x_621;
goto block_619;
}
else
{
if (x_54 == 0)
{
lean_dec(x_606);
lean_dec(x_6);
x_576 = x_3;
x_577 = x_621;
goto block_590;
}
else
{
lean_inc_ref(x_595);
lean_inc_ref(x_594);
lean_dec_ref(x_565);
lean_dec(x_563);
lean_dec(x_561);
lean_dec(x_559);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_1);
x_607 = x_621;
goto block_619;
}
}
}
}
else
{
lean_object* x_634; lean_object* x_635; 
lean_inc_ref(x_593);
lean_dec_ref(x_565);
lean_dec(x_563);
lean_dec(x_561);
lean_dec(x_559);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_634 = lean_ctor_get(x_593, 0);
lean_inc_ref(x_634);
lean_dec_ref(x_593);
x_635 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_562);
return x_635;
}
}
block_570:
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
if (lean_is_scalar(x_455)) {
 x_567 = lean_alloc_ctor(0, 4, 0);
} else {
 x_567 = x_455;
}
lean_ctor_set(x_567, 0, x_451);
lean_ctor_set(x_567, 1, x_565);
lean_ctor_set(x_567, 2, x_458);
lean_ctor_set(x_567, 3, x_561);
if (lean_is_scalar(x_459)) {
 x_568 = lean_alloc_ctor(4, 1, 0);
} else {
 x_568 = x_459;
 lean_ctor_set_tag(x_568, 4);
}
lean_ctor_set(x_568, 0, x_567);
if (lean_is_scalar(x_563)) {
 x_569 = lean_alloc_ctor(0, 2, 0);
} else {
 x_569 = x_563;
}
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_566);
return x_569;
}
block_575:
{
if (x_572 == 0)
{
lean_dec(x_559);
lean_dec(x_453);
lean_dec_ref(x_1);
x_566 = x_571;
goto block_570;
}
else
{
uint8_t x_573; 
x_573 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_453, x_458);
lean_dec(x_453);
if (x_573 == 0)
{
lean_dec(x_559);
lean_dec_ref(x_1);
x_566 = x_571;
goto block_570;
}
else
{
lean_object* x_574; 
lean_dec_ref(x_565);
lean_dec(x_563);
lean_dec(x_561);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec(x_451);
if (lean_is_scalar(x_559)) {
 x_574 = lean_alloc_ctor(0, 2, 0);
} else {
 x_574 = x_559;
}
lean_ctor_set(x_574, 0, x_1);
lean_ctor_set(x_574, 1, x_571);
return x_574;
}
}
}
block_590:
{
lean_object* x_578; 
lean_inc(x_458);
x_578 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_458, x_576, x_577);
lean_dec(x_576);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; size_t x_580; size_t x_581; uint8_t x_582; 
x_579 = lean_ctor_get(x_578, 1);
lean_inc(x_579);
lean_dec_ref(x_578);
x_580 = lean_ptr_addr(x_454);
lean_dec_ref(x_454);
x_581 = lean_ptr_addr(x_561);
x_582 = lean_usize_dec_eq(x_580, x_581);
if (x_582 == 0)
{
lean_dec_ref(x_452);
x_571 = x_579;
x_572 = x_582;
goto block_575;
}
else
{
size_t x_583; size_t x_584; uint8_t x_585; 
x_583 = lean_ptr_addr(x_452);
lean_dec_ref(x_452);
x_584 = lean_ptr_addr(x_565);
x_585 = lean_usize_dec_eq(x_583, x_584);
x_571 = x_579;
x_572 = x_585;
goto block_575;
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
lean_dec_ref(x_565);
lean_dec(x_563);
lean_dec(x_561);
lean_dec(x_559);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_1);
x_586 = lean_ctor_get(x_578, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_578, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 x_588 = x_578;
} else {
 lean_dec_ref(x_578);
 x_588 = lean_box(0);
}
if (lean_is_scalar(x_588)) {
 x_589 = lean_alloc_ctor(1, 2, 0);
} else {
 x_589 = x_588;
}
lean_ctor_set(x_589, 0, x_586);
lean_ctor_set(x_589, 1, x_587);
return x_589;
}
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_559);
lean_dec(x_553);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_636 = lean_ctor_get(x_560, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_560, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_638 = x_560;
} else {
 lean_dec_ref(x_560);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_638)) {
 x_639 = lean_alloc_ctor(1, 2, 0);
} else {
 x_639 = x_638;
}
lean_ctor_set(x_639, 0, x_636);
lean_ctor_set(x_639, 1, x_637);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_553);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_640 = lean_ctor_get(x_556, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_556, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_642 = x_556;
} else {
 lean_dec_ref(x_556);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_642)) {
 x_643 = lean_alloc_ctor(1, 2, 0);
} else {
 x_643 = x_642;
}
lean_ctor_set(x_643, 0, x_640);
lean_ctor_set(x_643, 1, x_641);
return x_643;
}
}
}
else
{
lean_object* x_644; 
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_644 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_450);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_644;
}
}
else
{
uint8_t x_645; 
lean_dec_ref(x_444);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_645 = !lean_is_exclusive(x_445);
if (x_645 == 0)
{
lean_object* x_646; lean_object* x_647; 
x_646 = lean_ctor_get(x_445, 0);
lean_dec(x_646);
x_647 = lean_ctor_get(x_446, 0);
lean_inc(x_647);
lean_dec_ref(x_446);
lean_ctor_set(x_445, 0, x_647);
return x_445;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_445, 1);
lean_inc(x_648);
lean_dec(x_445);
x_649 = lean_ctor_get(x_446, 0);
lean_inc(x_649);
lean_dec_ref(x_446);
x_650 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_650, 0, x_649);
lean_ctor_set(x_650, 1, x_648);
return x_650;
}
}
}
else
{
uint8_t x_651; 
lean_dec_ref(x_444);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_651 = !lean_is_exclusive(x_445);
if (x_651 == 0)
{
return x_445;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_445, 0);
x_653 = lean_ctor_get(x_445, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_445);
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_653);
return x_654;
}
}
}
case 5:
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_655 = lean_ctor_get(x_1, 0);
x_656 = lean_st_ref_get(x_3, x_71);
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec_ref(x_656);
x_659 = lean_ctor_get(x_657, 0);
lean_inc_ref(x_659);
lean_dec(x_657);
lean_inc(x_655);
x_660 = l_Lean_Compiler_LCNF_normFVarImp(x_659, x_655, x_54);
lean_dec_ref(x_659);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
lean_dec_ref(x_660);
lean_inc(x_661);
x_662 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_661, x_3, x_658);
lean_dec(x_3);
if (lean_obj_tag(x_662) == 0)
{
uint8_t x_663; 
x_663 = !lean_is_exclusive(x_662);
if (x_663 == 0)
{
lean_object* x_664; uint8_t x_665; 
x_664 = lean_ctor_get(x_662, 0);
lean_dec(x_664);
x_665 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_655, x_661);
if (x_665 == 0)
{
uint8_t x_666; 
x_666 = !lean_is_exclusive(x_1);
if (x_666 == 0)
{
lean_object* x_667; 
x_667 = lean_ctor_get(x_1, 0);
lean_dec(x_667);
lean_ctor_set(x_1, 0, x_661);
lean_ctor_set(x_662, 0, x_1);
return x_662;
}
else
{
lean_object* x_668; 
lean_dec(x_1);
x_668 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_668, 0, x_661);
lean_ctor_set(x_662, 0, x_668);
return x_662;
}
}
else
{
lean_dec(x_661);
lean_ctor_set(x_662, 0, x_1);
return x_662;
}
}
else
{
lean_object* x_669; uint8_t x_670; 
x_669 = lean_ctor_get(x_662, 1);
lean_inc(x_669);
lean_dec(x_662);
x_670 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_655, x_661);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_671 = x_1;
} else {
 lean_dec_ref(x_1);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_671)) {
 x_672 = lean_alloc_ctor(5, 1, 0);
} else {
 x_672 = x_671;
}
lean_ctor_set(x_672, 0, x_661);
x_673 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_669);
return x_673;
}
else
{
lean_object* x_674; 
lean_dec(x_661);
x_674 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_674, 0, x_1);
lean_ctor_set(x_674, 1, x_669);
return x_674;
}
}
}
else
{
uint8_t x_675; 
lean_dec(x_661);
lean_dec_ref(x_1);
x_675 = !lean_is_exclusive(x_662);
if (x_675 == 0)
{
return x_662;
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_676 = lean_ctor_get(x_662, 0);
x_677 = lean_ctor_get(x_662, 1);
lean_inc(x_677);
lean_inc(x_676);
lean_dec(x_662);
x_678 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set(x_678, 1, x_677);
return x_678;
}
}
}
else
{
lean_object* x_679; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_679 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_658);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_679;
}
}
case 6:
{
lean_object* x_680; lean_object* x_681; uint8_t x_682; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_680 = lean_ctor_get(x_1, 0);
x_681 = lean_st_ref_get(x_3, x_71);
lean_dec(x_3);
x_682 = !lean_is_exclusive(x_681);
if (x_682 == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; size_t x_686; size_t x_687; uint8_t x_688; 
x_683 = lean_ctor_get(x_681, 0);
x_684 = lean_ctor_get(x_683, 0);
lean_inc_ref(x_684);
lean_dec(x_683);
lean_inc_ref(x_680);
x_685 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_684, x_54, x_680);
lean_dec_ref(x_684);
x_686 = lean_ptr_addr(x_680);
x_687 = lean_ptr_addr(x_685);
x_688 = lean_usize_dec_eq(x_686, x_687);
if (x_688 == 0)
{
uint8_t x_689; 
x_689 = !lean_is_exclusive(x_1);
if (x_689 == 0)
{
lean_object* x_690; 
x_690 = lean_ctor_get(x_1, 0);
lean_dec(x_690);
lean_ctor_set(x_1, 0, x_685);
lean_ctor_set(x_681, 0, x_1);
return x_681;
}
else
{
lean_object* x_691; 
lean_dec(x_1);
x_691 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_691, 0, x_685);
lean_ctor_set(x_681, 0, x_691);
return x_681;
}
}
else
{
lean_dec_ref(x_685);
lean_ctor_set(x_681, 0, x_1);
return x_681;
}
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; size_t x_696; size_t x_697; uint8_t x_698; 
x_692 = lean_ctor_get(x_681, 0);
x_693 = lean_ctor_get(x_681, 1);
lean_inc(x_693);
lean_inc(x_692);
lean_dec(x_681);
x_694 = lean_ctor_get(x_692, 0);
lean_inc_ref(x_694);
lean_dec(x_692);
lean_inc_ref(x_680);
x_695 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_694, x_54, x_680);
lean_dec_ref(x_694);
x_696 = lean_ptr_addr(x_680);
x_697 = lean_ptr_addr(x_695);
x_698 = lean_usize_dec_eq(x_696, x_697);
if (x_698 == 0)
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_699 = x_1;
} else {
 lean_dec_ref(x_1);
 x_699 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_700 = lean_alloc_ctor(6, 1, 0);
} else {
 x_700 = x_699;
}
lean_ctor_set(x_700, 0, x_695);
x_701 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_701, 0, x_700);
lean_ctor_set(x_701, 1, x_693);
return x_701;
}
else
{
lean_object* x_702; 
lean_dec_ref(x_695);
x_702 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_702, 0, x_1);
lean_ctor_set(x_702, 1, x_693);
return x_702;
}
}
}
default: 
{
lean_object* x_703; lean_object* x_704; 
x_703 = lean_ctor_get(x_1, 0);
x_704 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_704);
lean_inc_ref(x_703);
x_72 = x_703;
x_73 = x_704;
x_74 = x_2;
x_75 = x_3;
x_76 = x_4;
x_77 = x_5;
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
goto block_133;
}
}
block_133:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_72, 0);
x_82 = lean_ctor_get(x_72, 2);
x_83 = lean_ctor_get(x_72, 3);
x_84 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_81, x_75, x_71);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
lean_inc(x_85);
lean_inc_ref(x_1);
lean_inc_ref(x_73);
x_87 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_87, 0, x_73);
lean_closure_set(x_87, 1, x_1);
lean_closure_set(x_87, 2, x_85);
x_88 = lean_unbox(x_85);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_85);
lean_dec_ref(x_73);
x_89 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_89 == 0)
{
x_18 = x_87;
x_19 = x_72;
x_20 = x_74;
x_21 = x_75;
x_22 = x_76;
x_23 = x_77;
x_24 = x_78;
x_25 = x_79;
x_26 = x_80;
x_27 = x_86;
goto block_37;
}
else
{
uint8_t x_90; 
lean_inc_ref(x_83);
x_90 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_83, x_82);
if (x_90 == 0)
{
x_18 = x_87;
x_19 = x_72;
x_20 = x_74;
x_21 = x_75;
x_22 = x_76;
x_23 = x_77;
x_24 = x_78;
x_25 = x_79;
x_26 = x_80;
x_27 = x_86;
goto block_37;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_st_ref_get(x_75, x_86);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc_ref(x_94);
lean_dec(x_92);
x_95 = l_Lean_Compiler_LCNF_normFunDeclImp(x_54, x_72, x_94, x_77, x_78, x_79, x_80, x_93);
lean_dec_ref(x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
lean_inc(x_80);
lean_inc_ref(x_79);
lean_inc(x_78);
lean_inc_ref(x_77);
x_98 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_96, x_77, x_78, x_79, x_80, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
x_101 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_75, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec_ref(x_101);
x_18 = x_87;
x_19 = x_99;
x_20 = x_74;
x_21 = x_75;
x_22 = x_76;
x_23 = x_77;
x_24 = x_78;
x_25 = x_79;
x_26 = x_80;
x_27 = x_102;
goto block_37;
}
else
{
uint8_t x_103; 
lean_dec(x_99);
lean_dec_ref(x_87);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
x_103 = !lean_is_exclusive(x_101);
if (x_103 == 0)
{
return x_101;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_101, 0);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_101);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec_ref(x_87);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
x_107 = !lean_is_exclusive(x_98);
if (x_107 == 0)
{
return x_98;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_98, 0);
x_109 = lean_ctor_get(x_98, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_98);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec_ref(x_87);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
x_111 = !lean_is_exclusive(x_95);
if (x_111 == 0)
{
return x_95;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_95, 0);
x_113 = lean_ctor_get(x_95, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_95);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec_ref(x_87);
x_115 = lean_st_ref_get(x_75, x_86);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec_ref(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc_ref(x_118);
lean_dec(x_116);
x_119 = l_Lean_Compiler_LCNF_normFunDeclImp(x_54, x_72, x_118, x_77, x_78, x_79, x_80, x_117);
lean_dec_ref(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_box(0);
x_123 = lean_unbox(x_85);
lean_dec(x_85);
x_124 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_73, x_1, x_123, x_120, x_122, x_74, x_75, x_76, x_77, x_78, x_79, x_80, x_121);
return x_124;
}
else
{
uint8_t x_125; 
lean_dec(x_85);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_1);
x_125 = !lean_is_exclusive(x_119);
if (x_125 == 0)
{
return x_119;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_119, 0);
x_127 = lean_ctor_get(x_119, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_119);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_1);
x_129 = !lean_is_exclusive(x_84);
if (x_129 == 0)
{
return x_84;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_84, 0);
x_131 = lean_ctor_get(x_84, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_84);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
else
{
uint8_t x_705; 
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
x_705 = !lean_is_exclusive(x_70);
if (x_705 == 0)
{
return x_70;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_706 = lean_ctor_get(x_70, 0);
x_707 = lean_ctor_get(x_70, 1);
lean_inc(x_707);
lean_inc(x_706);
lean_dec(x_70);
x_708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_708, 0, x_706);
lean_ctor_set(x_708, 1, x_707);
return x_708;
}
}
}
else
{
lean_object* x_709; 
lean_dec(x_7);
x_709 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_710 = lean_ctor_get(x_709, 1);
lean_inc(x_710);
lean_dec_ref(x_709);
x_773 = lean_unsigned_to_nat(1u);
x_774 = lean_nat_add(x_41, x_773);
lean_dec(x_41);
x_775 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_775, 0, x_38);
lean_ctor_set(x_775, 1, x_39);
lean_ctor_set(x_775, 2, x_40);
lean_ctor_set(x_775, 3, x_774);
lean_ctor_set(x_775, 4, x_42);
lean_ctor_set(x_775, 5, x_43);
lean_ctor_set(x_775, 6, x_44);
lean_ctor_set(x_775, 7, x_45);
lean_ctor_set(x_775, 8, x_46);
lean_ctor_set(x_775, 9, x_47);
lean_ctor_set(x_775, 10, x_48);
lean_ctor_set(x_775, 11, x_49);
lean_ctor_set(x_775, 12, x_51);
lean_ctor_set(x_775, 13, x_53);
lean_ctor_set_uint8(x_775, sizeof(void*)*14, x_50);
lean_ctor_set_uint8(x_775, sizeof(void*)*14 + 1, x_52);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; uint8_t x_787; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_956; 
x_776 = lean_ctor_get(x_1, 0);
x_777 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_776);
x_956 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_54, x_776, x_3, x_6, x_710);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; uint8_t x_1001; 
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
lean_dec_ref(x_956);
x_1001 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic_915775888____hygCtx___hyg_49_(x_776, x_957);
if (x_1001 == 0)
{
goto block_1000;
}
else
{
if (x_54 == 0)
{
x_959 = x_2;
x_960 = x_3;
x_961 = x_4;
x_962 = x_5;
x_963 = x_6;
x_964 = x_775;
x_965 = x_8;
x_966 = x_958;
goto block_993;
}
else
{
goto block_1000;
}
}
block_993:
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_967 = lean_ctor_get(x_957, 2);
x_968 = lean_ctor_get(x_957, 3);
lean_inc(x_965);
lean_inc_ref(x_964);
lean_inc(x_963);
lean_inc_ref(x_962);
lean_inc_ref(x_961);
lean_inc(x_968);
x_969 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_968, x_959, x_961, x_962, x_963, x_964, x_965, x_966);
if (lean_obj_tag(x_969) == 0)
{
lean_object* x_970; 
x_970 = lean_ctor_get(x_969, 0);
lean_inc(x_970);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; 
lean_inc(x_968);
lean_inc_ref(x_967);
x_971 = lean_ctor_get(x_969, 1);
lean_inc(x_971);
lean_dec_ref(x_969);
x_941 = x_957;
x_942 = x_967;
x_943 = x_968;
x_944 = x_959;
x_945 = x_960;
x_946 = x_961;
x_947 = x_962;
x_948 = x_963;
x_949 = x_964;
x_950 = x_965;
x_951 = x_971;
goto block_955;
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_972 = lean_ctor_get(x_969, 1);
lean_inc(x_972);
lean_dec_ref(x_969);
x_973 = lean_ctor_get(x_970, 0);
lean_inc(x_973);
lean_dec_ref(x_970);
x_974 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_960, x_972);
if (lean_obj_tag(x_974) == 0)
{
lean_object* x_975; lean_object* x_976; 
x_975 = lean_ctor_get(x_974, 1);
lean_inc(x_975);
lean_dec_ref(x_974);
x_976 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_957, x_973, x_963, x_975);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_976, 1);
lean_inc(x_978);
lean_dec_ref(x_976);
x_979 = lean_ctor_get(x_977, 2);
lean_inc_ref(x_979);
x_980 = lean_ctor_get(x_977, 3);
lean_inc(x_980);
x_941 = x_977;
x_942 = x_979;
x_943 = x_980;
x_944 = x_959;
x_945 = x_960;
x_946 = x_961;
x_947 = x_962;
x_948 = x_963;
x_949 = x_964;
x_950 = x_965;
x_951 = x_978;
goto block_955;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_dec(x_965);
lean_dec_ref(x_964);
lean_dec(x_963);
lean_dec_ref(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec_ref(x_1);
x_981 = lean_ctor_get(x_976, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_976, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_983 = x_976;
} else {
 lean_dec_ref(x_976);
 x_983 = lean_box(0);
}
if (lean_is_scalar(x_983)) {
 x_984 = lean_alloc_ctor(1, 2, 0);
} else {
 x_984 = x_983;
}
lean_ctor_set(x_984, 0, x_981);
lean_ctor_set(x_984, 1, x_982);
return x_984;
}
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec(x_973);
lean_dec(x_965);
lean_dec_ref(x_964);
lean_dec(x_963);
lean_dec_ref(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_957);
lean_dec_ref(x_1);
x_985 = lean_ctor_get(x_974, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_974, 1);
lean_inc(x_986);
if (lean_is_exclusive(x_974)) {
 lean_ctor_release(x_974, 0);
 lean_ctor_release(x_974, 1);
 x_987 = x_974;
} else {
 lean_dec_ref(x_974);
 x_987 = lean_box(0);
}
if (lean_is_scalar(x_987)) {
 x_988 = lean_alloc_ctor(1, 2, 0);
} else {
 x_988 = x_987;
}
lean_ctor_set(x_988, 0, x_985);
lean_ctor_set(x_988, 1, x_986);
return x_988;
}
}
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
lean_dec(x_965);
lean_dec_ref(x_964);
lean_dec(x_963);
lean_dec_ref(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_957);
lean_dec_ref(x_1);
x_989 = lean_ctor_get(x_969, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_969, 1);
lean_inc(x_990);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 lean_ctor_release(x_969, 1);
 x_991 = x_969;
} else {
 lean_dec_ref(x_969);
 x_991 = lean_box(0);
}
if (lean_is_scalar(x_991)) {
 x_992 = lean_alloc_ctor(1, 2, 0);
} else {
 x_992 = x_991;
}
lean_ctor_set(x_992, 0, x_989);
lean_ctor_set(x_992, 1, x_990);
return x_992;
}
}
block_1000:
{
lean_object* x_994; 
x_994 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_958);
if (lean_obj_tag(x_994) == 0)
{
lean_object* x_995; 
x_995 = lean_ctor_get(x_994, 1);
lean_inc(x_995);
lean_dec_ref(x_994);
x_959 = x_2;
x_960 = x_3;
x_961 = x_4;
x_962 = x_5;
x_963 = x_6;
x_964 = x_775;
x_965 = x_8;
x_966 = x_995;
goto block_993;
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; 
lean_dec(x_957);
lean_dec_ref(x_775);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_996 = lean_ctor_get(x_994, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_994, 1);
lean_inc(x_997);
if (lean_is_exclusive(x_994)) {
 lean_ctor_release(x_994, 0);
 lean_ctor_release(x_994, 1);
 x_998 = x_994;
} else {
 lean_dec_ref(x_994);
 x_998 = lean_box(0);
}
if (lean_is_scalar(x_998)) {
 x_999 = lean_alloc_ctor(1, 2, 0);
} else {
 x_999 = x_998;
}
lean_ctor_set(x_999, 0, x_996);
lean_ctor_set(x_999, 1, x_997);
return x_999;
}
}
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
lean_dec_ref(x_775);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1002 = lean_ctor_get(x_956, 0);
lean_inc(x_1002);
x_1003 = lean_ctor_get(x_956, 1);
lean_inc(x_1003);
if (lean_is_exclusive(x_956)) {
 lean_ctor_release(x_956, 0);
 lean_ctor_release(x_956, 1);
 x_1004 = x_956;
} else {
 lean_dec_ref(x_956);
 x_1004 = lean_box(0);
}
if (lean_is_scalar(x_1004)) {
 x_1005 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1005 = x_1004;
}
lean_ctor_set(x_1005, 0, x_1002);
lean_ctor_set(x_1005, 1, x_1003);
return x_1005;
}
block_940:
{
if (x_787 == 0)
{
lean_object* x_788; 
lean_inc(x_782);
lean_inc_ref(x_783);
lean_inc(x_784);
lean_inc_ref(x_786);
lean_inc_ref(x_780);
x_788 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_780, x_786, x_784, x_783, x_782, x_785);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; 
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; 
x_790 = lean_ctor_get(x_788, 1);
lean_inc(x_790);
lean_dec_ref(x_788);
lean_inc(x_782);
lean_inc_ref(x_783);
lean_inc(x_784);
lean_inc_ref(x_786);
lean_inc_ref(x_780);
x_791 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_780, x_781, x_779, x_786, x_784, x_783, x_782, x_790);
if (lean_obj_tag(x_791) == 0)
{
lean_object* x_792; 
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
if (lean_obj_tag(x_792) == 0)
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_793 = lean_ctor_get(x_791, 1);
lean_inc(x_793);
lean_dec_ref(x_791);
x_794 = lean_ctor_get(x_780, 0);
x_795 = lean_ctor_get(x_780, 3);
lean_inc(x_795);
x_796 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_795, x_793);
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; lean_object* x_799; 
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
lean_dec_ref(x_796);
lean_inc(x_782);
lean_inc_ref(x_783);
lean_inc(x_784);
lean_inc_ref(x_786);
lean_inc_ref(x_778);
lean_inc(x_779);
lean_inc_ref(x_781);
lean_inc_ref(x_777);
lean_inc_ref(x_780);
x_799 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_780, x_777, x_781, x_779, x_778, x_786, x_784, x_783, x_782, x_798);
if (lean_obj_tag(x_799) == 0)
{
lean_object* x_800; 
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_801; lean_object* x_802; 
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
lean_dec_ref(x_799);
lean_inc(x_782);
lean_inc_ref(x_783);
lean_inc(x_784);
lean_inc_ref(x_786);
lean_inc_ref(x_778);
lean_inc(x_779);
lean_inc_ref(x_781);
lean_inc(x_795);
x_802 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_795, x_781, x_779, x_778, x_786, x_784, x_783, x_782, x_801);
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; 
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_804; lean_object* x_805; 
x_804 = lean_ctor_get(x_802, 1);
lean_inc(x_804);
lean_dec_ref(x_802);
lean_inc(x_782);
lean_inc_ref(x_783);
lean_inc(x_784);
lean_inc_ref(x_786);
lean_inc_ref(x_778);
lean_inc(x_779);
lean_inc_ref(x_781);
lean_inc_ref(x_777);
x_805 = l_Lean_Compiler_LCNF_Simp_simp(x_777, x_781, x_779, x_778, x_786, x_784, x_783, x_782, x_804);
if (lean_obj_tag(x_805) == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_806 = lean_ctor_get(x_805, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_805, 1);
lean_inc(x_807);
lean_dec_ref(x_805);
x_808 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_794, x_779, x_807);
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; uint8_t x_810; 
x_809 = lean_ctor_get(x_808, 0);
lean_inc(x_809);
x_810 = lean_unbox(x_809);
lean_dec(x_809);
if (x_810 == 0)
{
lean_object* x_811; lean_object* x_812; 
lean_dec_ref(x_786);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec_ref(x_778);
lean_dec_ref(x_1);
x_811 = lean_ctor_get(x_808, 1);
lean_inc(x_811);
lean_dec_ref(x_808);
x_812 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_780, x_779, x_784, x_811);
lean_dec(x_784);
lean_dec(x_779);
lean_dec_ref(x_780);
if (lean_obj_tag(x_812) == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_812, 1);
lean_inc(x_813);
if (lean_is_exclusive(x_812)) {
 lean_ctor_release(x_812, 0);
 lean_ctor_release(x_812, 1);
 x_814 = x_812;
} else {
 lean_dec_ref(x_812);
 x_814 = lean_box(0);
}
if (lean_is_scalar(x_814)) {
 x_815 = lean_alloc_ctor(0, 2, 0);
} else {
 x_815 = x_814;
}
lean_ctor_set(x_815, 0, x_806);
lean_ctor_set(x_815, 1, x_813);
return x_815;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
lean_dec(x_806);
x_816 = lean_ctor_get(x_812, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_812, 1);
lean_inc(x_817);
if (lean_is_exclusive(x_812)) {
 lean_ctor_release(x_812, 0);
 lean_ctor_release(x_812, 1);
 x_818 = x_812;
} else {
 lean_dec_ref(x_812);
 x_818 = lean_box(0);
}
if (lean_is_scalar(x_818)) {
 x_819 = lean_alloc_ctor(1, 2, 0);
} else {
 x_819 = x_818;
}
lean_ctor_set(x_819, 0, x_816);
lean_ctor_set(x_819, 1, x_817);
return x_819;
}
}
else
{
lean_object* x_820; lean_object* x_821; 
x_820 = lean_ctor_get(x_808, 1);
lean_inc(x_820);
lean_dec_ref(x_808);
lean_inc_ref(x_780);
x_821 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_780, x_781, x_779, x_778, x_786, x_784, x_783, x_782, x_820);
lean_dec(x_782);
lean_dec_ref(x_783);
lean_dec(x_784);
lean_dec_ref(x_786);
lean_dec_ref(x_778);
lean_dec(x_779);
lean_dec_ref(x_781);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; size_t x_823; size_t x_824; uint8_t x_825; 
x_822 = lean_ctor_get(x_821, 1);
lean_inc(x_822);
lean_dec_ref(x_821);
x_823 = lean_ptr_addr(x_777);
x_824 = lean_ptr_addr(x_806);
x_825 = lean_usize_dec_eq(x_823, x_824);
if (x_825 == 0)
{
x_10 = x_780;
x_11 = x_822;
x_12 = x_806;
x_13 = x_825;
goto block_17;
}
else
{
size_t x_826; size_t x_827; uint8_t x_828; 
x_826 = lean_ptr_addr(x_776);
x_827 = lean_ptr_addr(x_780);
x_828 = lean_usize_dec_eq(x_826, x_827);
x_10 = x_780;
x_11 = x_822;
x_12 = x_806;
x_13 = x_828;
goto block_17;
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
lean_dec(x_806);
lean_dec_ref(x_780);
lean_dec_ref(x_1);
x_829 = lean_ctor_get(x_821, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_821, 1);
lean_inc(x_830);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_831 = x_821;
} else {
 lean_dec_ref(x_821);
 x_831 = lean_box(0);
}
if (lean_is_scalar(x_831)) {
 x_832 = lean_alloc_ctor(1, 2, 0);
} else {
 x_832 = x_831;
}
lean_ctor_set(x_832, 0, x_829);
lean_ctor_set(x_832, 1, x_830);
return x_832;
}
}
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
lean_dec(x_806);
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_1);
x_833 = lean_ctor_get(x_808, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_808, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_808)) {
 lean_ctor_release(x_808, 0);
 lean_ctor_release(x_808, 1);
 x_835 = x_808;
} else {
 lean_dec_ref(x_808);
 x_835 = lean_box(0);
}
if (lean_is_scalar(x_835)) {
 x_836 = lean_alloc_ctor(1, 2, 0);
} else {
 x_836 = x_835;
}
lean_ctor_set(x_836, 0, x_833);
lean_ctor_set(x_836, 1, x_834);
return x_836;
}
}
else
{
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_1);
return x_805;
}
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
lean_inc_ref(x_777);
lean_dec_ref(x_1);
x_837 = lean_ctor_get(x_803, 0);
lean_inc(x_837);
lean_dec_ref(x_803);
x_838 = lean_ctor_get(x_802, 1);
lean_inc(x_838);
lean_dec_ref(x_802);
x_839 = lean_ctor_get(x_837, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_837, 1);
lean_inc(x_840);
lean_dec(x_837);
lean_inc(x_794);
x_841 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_794, x_840, x_779, x_784, x_783, x_782, x_838);
if (lean_obj_tag(x_841) == 0)
{
lean_object* x_842; lean_object* x_843; 
x_842 = lean_ctor_get(x_841, 1);
lean_inc(x_842);
lean_dec_ref(x_841);
x_843 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_780, x_779, x_784, x_842);
lean_dec_ref(x_780);
if (lean_obj_tag(x_843) == 0)
{
lean_object* x_844; lean_object* x_845; 
x_844 = lean_ctor_get(x_843, 1);
lean_inc(x_844);
lean_dec_ref(x_843);
lean_inc(x_782);
lean_inc_ref(x_783);
lean_inc(x_784);
lean_inc_ref(x_786);
lean_inc_ref(x_778);
lean_inc(x_779);
lean_inc_ref(x_781);
x_845 = l_Lean_Compiler_LCNF_Simp_simp(x_777, x_781, x_779, x_778, x_786, x_784, x_783, x_782, x_844);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
lean_dec_ref(x_845);
x_848 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_839, x_846, x_781, x_779, x_778, x_786, x_784, x_783, x_782, x_847);
lean_dec(x_782);
lean_dec_ref(x_783);
lean_dec(x_784);
lean_dec_ref(x_786);
lean_dec_ref(x_778);
lean_dec(x_779);
lean_dec_ref(x_781);
lean_dec(x_839);
return x_848;
}
else
{
lean_dec(x_839);
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec(x_779);
lean_dec_ref(x_778);
return x_845;
}
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; 
lean_dec(x_839);
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_777);
x_849 = lean_ctor_get(x_843, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_843, 1);
lean_inc(x_850);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 x_851 = x_843;
} else {
 lean_dec_ref(x_843);
 x_851 = lean_box(0);
}
if (lean_is_scalar(x_851)) {
 x_852 = lean_alloc_ctor(1, 2, 0);
} else {
 x_852 = x_851;
}
lean_ctor_set(x_852, 0, x_849);
lean_ctor_set(x_852, 1, x_850);
return x_852;
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_839);
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_777);
x_853 = lean_ctor_get(x_841, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_841, 1);
lean_inc(x_854);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 x_855 = x_841;
} else {
 lean_dec_ref(x_841);
 x_855 = lean_box(0);
}
if (lean_is_scalar(x_855)) {
 x_856 = lean_alloc_ctor(1, 2, 0);
} else {
 x_856 = x_855;
}
lean_ctor_set(x_856, 0, x_853);
lean_ctor_set(x_856, 1, x_854);
return x_856;
}
}
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_1);
x_857 = lean_ctor_get(x_802, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_802, 1);
lean_inc(x_858);
if (lean_is_exclusive(x_802)) {
 lean_ctor_release(x_802, 0);
 lean_ctor_release(x_802, 1);
 x_859 = x_802;
} else {
 lean_dec_ref(x_802);
 x_859 = lean_box(0);
}
if (lean_is_scalar(x_859)) {
 x_860 = lean_alloc_ctor(1, 2, 0);
} else {
 x_860 = x_859;
}
lean_ctor_set(x_860, 0, x_857);
lean_ctor_set(x_860, 1, x_858);
return x_860;
}
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; 
lean_dec_ref(x_786);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec_ref(x_778);
lean_dec_ref(x_1);
x_861 = lean_ctor_get(x_799, 1);
lean_inc(x_861);
lean_dec_ref(x_799);
x_862 = lean_ctor_get(x_800, 0);
lean_inc(x_862);
lean_dec_ref(x_800);
x_863 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_780, x_779, x_784, x_861);
lean_dec(x_784);
lean_dec(x_779);
lean_dec_ref(x_780);
if (lean_obj_tag(x_863) == 0)
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; 
x_864 = lean_ctor_get(x_863, 1);
lean_inc(x_864);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 lean_ctor_release(x_863, 1);
 x_865 = x_863;
} else {
 lean_dec_ref(x_863);
 x_865 = lean_box(0);
}
if (lean_is_scalar(x_865)) {
 x_866 = lean_alloc_ctor(0, 2, 0);
} else {
 x_866 = x_865;
}
lean_ctor_set(x_866, 0, x_862);
lean_ctor_set(x_866, 1, x_864);
return x_866;
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; 
lean_dec(x_862);
x_867 = lean_ctor_get(x_863, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_863, 1);
lean_inc(x_868);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 lean_ctor_release(x_863, 1);
 x_869 = x_863;
} else {
 lean_dec_ref(x_863);
 x_869 = lean_box(0);
}
if (lean_is_scalar(x_869)) {
 x_870 = lean_alloc_ctor(1, 2, 0);
} else {
 x_870 = x_869;
}
lean_ctor_set(x_870, 0, x_867);
lean_ctor_set(x_870, 1, x_868);
return x_870;
}
}
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_1);
x_871 = lean_ctor_get(x_799, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_799, 1);
lean_inc(x_872);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_873 = x_799;
} else {
 lean_dec_ref(x_799);
 x_873 = lean_box(0);
}
if (lean_is_scalar(x_873)) {
 x_874 = lean_alloc_ctor(1, 2, 0);
} else {
 x_874 = x_873;
}
lean_ctor_set(x_874, 0, x_871);
lean_ctor_set(x_874, 1, x_872);
return x_874;
}
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; 
lean_inc_ref(x_777);
lean_dec_ref(x_1);
x_875 = lean_ctor_get(x_796, 1);
lean_inc(x_875);
lean_dec_ref(x_796);
x_876 = lean_ctor_get(x_797, 0);
lean_inc(x_876);
lean_dec_ref(x_797);
lean_inc(x_794);
x_877 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_794, x_876, x_779, x_784, x_783, x_782, x_875);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; lean_object* x_879; 
x_878 = lean_ctor_get(x_877, 1);
lean_inc(x_878);
lean_dec_ref(x_877);
x_879 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_780, x_779, x_784, x_878);
lean_dec_ref(x_780);
if (lean_obj_tag(x_879) == 0)
{
lean_object* x_880; 
x_880 = lean_ctor_get(x_879, 1);
lean_inc(x_880);
lean_dec_ref(x_879);
x_1 = x_777;
x_2 = x_781;
x_3 = x_779;
x_4 = x_778;
x_5 = x_786;
x_6 = x_784;
x_7 = x_783;
x_8 = x_782;
x_9 = x_880;
goto _start;
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; 
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_777);
x_882 = lean_ctor_get(x_879, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_879, 1);
lean_inc(x_883);
if (lean_is_exclusive(x_879)) {
 lean_ctor_release(x_879, 0);
 lean_ctor_release(x_879, 1);
 x_884 = x_879;
} else {
 lean_dec_ref(x_879);
 x_884 = lean_box(0);
}
if (lean_is_scalar(x_884)) {
 x_885 = lean_alloc_ctor(1, 2, 0);
} else {
 x_885 = x_884;
}
lean_ctor_set(x_885, 0, x_882);
lean_ctor_set(x_885, 1, x_883);
return x_885;
}
}
else
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_777);
x_886 = lean_ctor_get(x_877, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_877, 1);
lean_inc(x_887);
if (lean_is_exclusive(x_877)) {
 lean_ctor_release(x_877, 0);
 lean_ctor_release(x_877, 1);
 x_888 = x_877;
} else {
 lean_dec_ref(x_877);
 x_888 = lean_box(0);
}
if (lean_is_scalar(x_888)) {
 x_889 = lean_alloc_ctor(1, 2, 0);
} else {
 x_889 = x_888;
}
lean_ctor_set(x_889, 0, x_886);
lean_ctor_set(x_889, 1, x_887);
return x_889;
}
}
}
else
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; 
lean_dec_ref(x_780);
lean_inc_ref(x_777);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_890 = x_1;
} else {
 lean_dec_ref(x_1);
 x_890 = lean_box(0);
}
x_891 = lean_ctor_get(x_791, 1);
lean_inc(x_891);
lean_dec_ref(x_791);
x_892 = lean_ctor_get(x_792, 0);
lean_inc(x_892);
lean_dec_ref(x_792);
if (lean_is_scalar(x_890)) {
 x_893 = lean_alloc_ctor(1, 2, 0);
} else {
 x_893 = x_890;
 lean_ctor_set_tag(x_893, 1);
}
lean_ctor_set(x_893, 0, x_892);
lean_ctor_set(x_893, 1, x_777);
x_1 = x_893;
x_2 = x_781;
x_3 = x_779;
x_4 = x_778;
x_5 = x_786;
x_6 = x_784;
x_7 = x_783;
x_8 = x_782;
x_9 = x_891;
goto _start;
}
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_1);
x_895 = lean_ctor_get(x_791, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_791, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_791)) {
 lean_ctor_release(x_791, 0);
 lean_ctor_release(x_791, 1);
 x_897 = x_791;
} else {
 lean_dec_ref(x_791);
 x_897 = lean_box(0);
}
if (lean_is_scalar(x_897)) {
 x_898 = lean_alloc_ctor(1, 2, 0);
} else {
 x_898 = x_897;
}
lean_ctor_set(x_898, 0, x_895);
lean_ctor_set(x_898, 1, x_896);
return x_898;
}
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; 
lean_dec_ref(x_780);
lean_inc_ref(x_777);
lean_dec_ref(x_1);
x_899 = lean_ctor_get(x_788, 1);
lean_inc(x_899);
lean_dec_ref(x_788);
x_900 = lean_ctor_get(x_789, 0);
lean_inc(x_900);
lean_dec_ref(x_789);
x_901 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_779, x_899);
if (lean_obj_tag(x_901) == 0)
{
lean_object* x_902; lean_object* x_903; 
x_902 = lean_ctor_get(x_901, 1);
lean_inc(x_902);
lean_dec_ref(x_901);
lean_inc(x_782);
lean_inc_ref(x_783);
lean_inc(x_784);
lean_inc_ref(x_786);
lean_inc_ref(x_778);
lean_inc(x_779);
lean_inc_ref(x_781);
x_903 = l_Lean_Compiler_LCNF_Simp_simp(x_777, x_781, x_779, x_778, x_786, x_784, x_783, x_782, x_902);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
x_905 = lean_ctor_get(x_903, 1);
lean_inc(x_905);
lean_dec_ref(x_903);
x_906 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_900, x_904, x_781, x_779, x_778, x_786, x_784, x_783, x_782, x_905);
lean_dec(x_782);
lean_dec_ref(x_783);
lean_dec(x_784);
lean_dec_ref(x_786);
lean_dec_ref(x_778);
lean_dec(x_779);
lean_dec_ref(x_781);
lean_dec(x_900);
return x_906;
}
else
{
lean_dec(x_900);
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec(x_779);
lean_dec_ref(x_778);
return x_903;
}
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_900);
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_777);
x_907 = lean_ctor_get(x_901, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_901, 1);
lean_inc(x_908);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 x_909 = x_901;
} else {
 lean_dec_ref(x_901);
 x_909 = lean_box(0);
}
if (lean_is_scalar(x_909)) {
 x_910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_910 = x_909;
}
lean_ctor_set(x_910, 0, x_907);
lean_ctor_set(x_910, 1, x_908);
return x_910;
}
}
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec_ref(x_780);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_1);
x_911 = lean_ctor_get(x_788, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_788, 1);
lean_inc(x_912);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 lean_ctor_release(x_788, 1);
 x_913 = x_788;
} else {
 lean_dec_ref(x_788);
 x_913 = lean_box(0);
}
if (lean_is_scalar(x_913)) {
 x_914 = lean_alloc_ctor(1, 2, 0);
} else {
 x_914 = x_913;
}
lean_ctor_set(x_914, 0, x_911);
lean_ctor_set(x_914, 1, x_912);
return x_914;
}
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; uint8_t x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
lean_inc_ref(x_777);
lean_dec_ref(x_1);
x_915 = lean_st_ref_take(x_779, x_785);
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec_ref(x_915);
x_918 = lean_ctor_get(x_780, 0);
x_919 = lean_ctor_get(x_916, 0);
lean_inc_ref(x_919);
x_920 = lean_ctor_get(x_916, 1);
lean_inc_ref(x_920);
x_921 = lean_ctor_get(x_916, 2);
lean_inc(x_921);
x_922 = lean_ctor_get(x_916, 3);
lean_inc_ref(x_922);
x_923 = lean_ctor_get_uint8(x_916, sizeof(void*)*7);
x_924 = lean_ctor_get(x_916, 4);
lean_inc(x_924);
x_925 = lean_ctor_get(x_916, 5);
lean_inc(x_925);
x_926 = lean_ctor_get(x_916, 6);
lean_inc(x_926);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 lean_ctor_release(x_916, 2);
 lean_ctor_release(x_916, 3);
 lean_ctor_release(x_916, 4);
 lean_ctor_release(x_916, 5);
 lean_ctor_release(x_916, 6);
 x_927 = x_916;
} else {
 lean_dec_ref(x_916);
 x_927 = lean_box(0);
}
x_928 = lean_box(0);
lean_inc(x_918);
x_929 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_919, x_918, x_928);
if (lean_is_scalar(x_927)) {
 x_930 = lean_alloc_ctor(0, 7, 1);
} else {
 x_930 = x_927;
}
lean_ctor_set(x_930, 0, x_929);
lean_ctor_set(x_930, 1, x_920);
lean_ctor_set(x_930, 2, x_921);
lean_ctor_set(x_930, 3, x_922);
lean_ctor_set(x_930, 4, x_924);
lean_ctor_set(x_930, 5, x_925);
lean_ctor_set(x_930, 6, x_926);
lean_ctor_set_uint8(x_930, sizeof(void*)*7, x_923);
x_931 = lean_st_ref_set(x_779, x_930, x_917);
x_932 = lean_ctor_get(x_931, 1);
lean_inc(x_932);
lean_dec_ref(x_931);
x_933 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_780, x_779, x_784, x_932);
lean_dec_ref(x_780);
if (lean_obj_tag(x_933) == 0)
{
lean_object* x_934; 
x_934 = lean_ctor_get(x_933, 1);
lean_inc(x_934);
lean_dec_ref(x_933);
x_1 = x_777;
x_2 = x_781;
x_3 = x_779;
x_4 = x_778;
x_5 = x_786;
x_6 = x_784;
x_7 = x_783;
x_8 = x_782;
x_9 = x_934;
goto _start;
}
else
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; 
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec_ref(x_783);
lean_dec(x_782);
lean_dec_ref(x_781);
lean_dec(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_777);
x_936 = lean_ctor_get(x_933, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_933, 1);
lean_inc(x_937);
if (lean_is_exclusive(x_933)) {
 lean_ctor_release(x_933, 0);
 lean_ctor_release(x_933, 1);
 x_938 = x_933;
} else {
 lean_dec_ref(x_933);
 x_938 = lean_box(0);
}
if (lean_is_scalar(x_938)) {
 x_939 = lean_alloc_ctor(1, 2, 0);
} else {
 x_939 = x_938;
}
lean_ctor_set(x_939, 0, x_936);
lean_ctor_set(x_939, 1, x_937);
return x_939;
}
}
}
block_955:
{
uint8_t x_952; 
x_952 = l_Lean_Expr_isErased(x_942);
lean_dec_ref(x_942);
if (x_952 == 0)
{
lean_dec(x_943);
x_778 = x_946;
x_779 = x_945;
x_780 = x_941;
x_781 = x_944;
x_782 = x_950;
x_783 = x_949;
x_784 = x_948;
x_785 = x_951;
x_786 = x_947;
x_787 = x_54;
goto block_940;
}
else
{
lean_object* x_953; uint8_t x_954; 
x_953 = lean_box(1);
x_954 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic_4164288206____hygCtx___hyg_104_(x_943, x_953);
lean_dec(x_943);
if (x_954 == 0)
{
x_778 = x_946;
x_779 = x_945;
x_780 = x_941;
x_781 = x_944;
x_782 = x_950;
x_783 = x_949;
x_784 = x_948;
x_785 = x_951;
x_786 = x_947;
x_787 = x_952;
goto block_940;
}
else
{
x_778 = x_946;
x_779 = x_945;
x_780 = x_941;
x_781 = x_944;
x_782 = x_950;
x_783 = x_949;
x_784 = x_948;
x_785 = x_951;
x_786 = x_947;
x_787 = x_54;
goto block_940;
}
}
}
}
case 3:
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1006 = lean_ctor_get(x_1, 0);
x_1007 = lean_ctor_get(x_1, 1);
x_1008 = lean_st_ref_get(x_3, x_710);
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_1008, 1);
lean_inc(x_1010);
lean_dec_ref(x_1008);
x_1011 = lean_ctor_get(x_1009, 0);
lean_inc_ref(x_1011);
lean_dec(x_1009);
lean_inc(x_1006);
x_1012 = l_Lean_Compiler_LCNF_normFVarImp(x_1011, x_1006, x_54);
lean_dec_ref(x_1011);
if (lean_obj_tag(x_1012) == 0)
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; uint8_t x_1019; lean_object* x_1025; lean_object* x_1031; 
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
lean_dec_ref(x_1012);
lean_inc_ref(x_1007);
x_1014 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_54, x_1007, x_3, x_1010);
x_1015 = lean_ctor_get(x_1014, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_1014, 1);
lean_inc(x_1016);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 lean_ctor_release(x_1014, 1);
 x_1017 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1017 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_775);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1015);
x_1031 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1013, x_1015, x_2, x_3, x_4, x_5, x_6, x_775, x_8, x_1016);
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; 
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; 
lean_dec_ref(x_775);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1033 = lean_ctor_get(x_1031, 1);
lean_inc(x_1033);
lean_dec_ref(x_1031);
lean_inc(x_1013);
x_1034 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1013, x_3, x_1033);
if (lean_obj_tag(x_1034) == 0)
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; uint8_t x_1038; 
x_1035 = lean_ctor_get(x_1034, 1);
lean_inc(x_1035);
lean_dec_ref(x_1034);
x_1036 = lean_unsigned_to_nat(0u);
x_1037 = lean_array_get_size(x_1015);
x_1038 = lean_nat_dec_lt(x_1036, x_1037);
if (x_1038 == 0)
{
lean_dec(x_1037);
lean_dec(x_3);
x_1025 = x_1035;
goto block_1030;
}
else
{
uint8_t x_1039; 
x_1039 = lean_nat_dec_le(x_1037, x_1037);
if (x_1039 == 0)
{
lean_dec(x_1037);
lean_dec(x_3);
x_1025 = x_1035;
goto block_1030;
}
else
{
lean_object* x_1040; size_t x_1041; size_t x_1042; lean_object* x_1043; 
x_1040 = lean_box(0);
x_1041 = 0;
x_1042 = lean_usize_of_nat(x_1037);
lean_dec(x_1037);
x_1043 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1015, x_1041, x_1042, x_1040, x_3, x_1035);
lean_dec(x_3);
if (lean_obj_tag(x_1043) == 0)
{
lean_object* x_1044; 
x_1044 = lean_ctor_get(x_1043, 1);
lean_inc(x_1044);
lean_dec_ref(x_1043);
x_1025 = x_1044;
goto block_1030;
}
else
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
lean_dec(x_1017);
lean_dec(x_1015);
lean_dec(x_1013);
lean_dec_ref(x_1);
x_1045 = lean_ctor_get(x_1043, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1043, 1);
lean_inc(x_1046);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1047 = x_1043;
} else {
 lean_dec_ref(x_1043);
 x_1047 = lean_box(0);
}
if (lean_is_scalar(x_1047)) {
 x_1048 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1048 = x_1047;
}
lean_ctor_set(x_1048, 0, x_1045);
lean_ctor_set(x_1048, 1, x_1046);
return x_1048;
}
}
}
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
lean_dec(x_1017);
lean_dec(x_1015);
lean_dec(x_1013);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1049 = lean_ctor_get(x_1034, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1034, 1);
lean_inc(x_1050);
if (lean_is_exclusive(x_1034)) {
 lean_ctor_release(x_1034, 0);
 lean_ctor_release(x_1034, 1);
 x_1051 = x_1034;
} else {
 lean_dec_ref(x_1034);
 x_1051 = lean_box(0);
}
if (lean_is_scalar(x_1051)) {
 x_1052 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1052 = x_1051;
}
lean_ctor_set(x_1052, 0, x_1049);
lean_ctor_set(x_1052, 1, x_1050);
return x_1052;
}
}
else
{
lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_1017);
lean_dec(x_1015);
lean_dec(x_1013);
lean_dec_ref(x_1);
x_1053 = lean_ctor_get(x_1031, 1);
lean_inc(x_1053);
lean_dec_ref(x_1031);
x_1054 = lean_ctor_get(x_1032, 0);
lean_inc(x_1054);
lean_dec_ref(x_1032);
x_1 = x_1054;
x_7 = x_775;
x_9 = x_1053;
goto _start;
}
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
lean_dec(x_1017);
lean_dec(x_1015);
lean_dec(x_1013);
lean_dec_ref(x_775);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1056 = lean_ctor_get(x_1031, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1031, 1);
lean_inc(x_1057);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 lean_ctor_release(x_1031, 1);
 x_1058 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1058 = lean_box(0);
}
if (lean_is_scalar(x_1058)) {
 x_1059 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1059 = x_1058;
}
lean_ctor_set(x_1059, 0, x_1056);
lean_ctor_set(x_1059, 1, x_1057);
return x_1059;
}
block_1024:
{
if (x_1019 == 0)
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1020 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1020 = lean_box(0);
}
if (lean_is_scalar(x_1020)) {
 x_1021 = lean_alloc_ctor(3, 2, 0);
} else {
 x_1021 = x_1020;
}
lean_ctor_set(x_1021, 0, x_1013);
lean_ctor_set(x_1021, 1, x_1015);
if (lean_is_scalar(x_1017)) {
 x_1022 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1022 = x_1017;
}
lean_ctor_set(x_1022, 0, x_1021);
lean_ctor_set(x_1022, 1, x_1018);
return x_1022;
}
else
{
lean_object* x_1023; 
lean_dec(x_1015);
lean_dec(x_1013);
if (lean_is_scalar(x_1017)) {
 x_1023 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1023 = x_1017;
}
lean_ctor_set(x_1023, 0, x_1);
lean_ctor_set(x_1023, 1, x_1018);
return x_1023;
}
}
block_1030:
{
uint8_t x_1026; 
x_1026 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_1006, x_1013);
if (x_1026 == 0)
{
x_1018 = x_1025;
x_1019 = x_1026;
goto block_1024;
}
else
{
size_t x_1027; size_t x_1028; uint8_t x_1029; 
x_1027 = lean_ptr_addr(x_1007);
x_1028 = lean_ptr_addr(x_1015);
x_1029 = lean_usize_dec_eq(x_1027, x_1028);
x_1018 = x_1025;
x_1019 = x_1029;
goto block_1024;
}
}
}
else
{
lean_object* x_1060; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1060 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_775, x_8, x_1010);
lean_dec(x_8);
lean_dec_ref(x_775);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1060;
}
}
case 4:
{
lean_object* x_1061; lean_object* x_1062; 
x_1061 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1061);
lean_inc(x_8);
lean_inc_ref(x_775);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1061);
x_1062 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1061, x_2, x_3, x_4, x_5, x_6, x_775, x_8, x_710);
if (lean_obj_tag(x_1062) == 0)
{
lean_object* x_1063; 
x_1063 = lean_ctor_get(x_1062, 0);
lean_inc(x_1063);
if (lean_obj_tag(x_1063) == 0)
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1064 = lean_ctor_get(x_1062, 1);
lean_inc(x_1064);
lean_dec_ref(x_1062);
x_1065 = lean_st_ref_get(x_3, x_1064);
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1065, 1);
lean_inc(x_1067);
lean_dec_ref(x_1065);
x_1068 = lean_ctor_get(x_1061, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1061, 1);
lean_inc_ref(x_1069);
x_1070 = lean_ctor_get(x_1061, 2);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1061, 3);
lean_inc_ref(x_1071);
if (lean_is_exclusive(x_1061)) {
 lean_ctor_release(x_1061, 0);
 lean_ctor_release(x_1061, 1);
 lean_ctor_release(x_1061, 2);
 lean_ctor_release(x_1061, 3);
 x_1072 = x_1061;
} else {
 lean_dec_ref(x_1061);
 x_1072 = lean_box(0);
}
x_1073 = lean_ctor_get(x_1066, 0);
lean_inc_ref(x_1073);
lean_dec(x_1066);
lean_inc(x_1070);
x_1074 = l_Lean_Compiler_LCNF_normFVarImp(x_1073, x_1070, x_54);
lean_dec_ref(x_1073);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 x_1076 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1076 = lean_box(0);
}
x_1077 = lean_st_ref_get(x_3, x_1067);
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1077, 1);
lean_inc(x_1079);
if (lean_is_exclusive(x_1077)) {
 lean_ctor_release(x_1077, 0);
 lean_ctor_release(x_1077, 1);
 x_1080 = x_1077;
} else {
 lean_dec_ref(x_1077);
 x_1080 = lean_box(0);
}
x_1081 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_775);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1071);
lean_inc(x_1075);
x_1082 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_1075, x_54, x_1081, x_1071, x_2, x_3, x_4, x_5, x_6, x_775, x_8, x_1079);
if (lean_obj_tag(x_1082) == 0)
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
x_1083 = lean_ctor_get(x_1082, 0);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1082, 1);
lean_inc(x_1084);
if (lean_is_exclusive(x_1082)) {
 lean_ctor_release(x_1082, 0);
 lean_ctor_release(x_1082, 1);
 x_1085 = x_1082;
} else {
 lean_dec_ref(x_1082);
 x_1085 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_1086 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1083, x_2, x_3, x_4, x_5, x_6, x_775, x_8, x_1084);
if (lean_obj_tag(x_1086) == 0)
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1097; uint8_t x_1098; lean_object* x_1102; lean_object* x_1103; lean_object* x_1117; uint8_t x_1118; 
x_1087 = lean_ctor_get(x_1086, 0);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1086, 1);
lean_inc(x_1088);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 lean_ctor_release(x_1086, 1);
 x_1089 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1089 = lean_box(0);
}
x_1090 = lean_ctor_get(x_1078, 0);
lean_inc_ref(x_1090);
lean_dec(x_1078);
lean_inc_ref(x_1069);
x_1091 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1090, x_54, x_1069);
lean_dec_ref(x_1090);
x_1117 = lean_array_get_size(x_1087);
x_1118 = lean_nat_dec_eq(x_1117, x_773);
lean_dec(x_1117);
if (x_1118 == 0)
{
lean_dec(x_1080);
lean_dec(x_6);
x_1102 = x_3;
x_1103 = x_1088;
goto block_1116;
}
else
{
lean_object* x_1119; 
x_1119 = lean_array_fget_borrowed(x_1087, x_1081);
if (lean_obj_tag(x_1119) == 0)
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1132; lean_object* x_1133; uint8_t x_1146; lean_object* x_1147; uint8_t x_1149; 
lean_dec(x_1080);
x_1120 = lean_ctor_get(x_1119, 1);
x_1121 = lean_ctor_get(x_1119, 2);
x_1132 = lean_array_get_size(x_1120);
x_1149 = lean_nat_dec_lt(x_1081, x_1132);
if (x_1149 == 0)
{
x_1146 = x_54;
x_1147 = x_1088;
goto block_1148;
}
else
{
if (x_1149 == 0)
{
x_1146 = x_54;
x_1147 = x_1088;
goto block_1148;
}
else
{
size_t x_1150; size_t x_1151; lean_object* x_1152; 
x_1150 = 0;
x_1151 = lean_usize_of_nat(x_1132);
x_1152 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1120, x_1150, x_1151, x_3, x_1088);
if (lean_obj_tag(x_1152) == 0)
{
lean_object* x_1153; lean_object* x_1154; uint8_t x_1155; 
x_1153 = lean_ctor_get(x_1152, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1152, 1);
lean_inc(x_1154);
lean_dec_ref(x_1152);
x_1155 = lean_unbox(x_1153);
lean_dec(x_1153);
x_1146 = x_1155;
x_1147 = x_1154;
goto block_1148;
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
lean_dec(x_1132);
lean_dec_ref(x_1091);
lean_dec(x_1089);
lean_dec(x_1087);
lean_dec(x_1085);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec_ref(x_1069);
lean_dec(x_1068);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1156 = lean_ctor_get(x_1152, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1152, 1);
lean_inc(x_1157);
if (lean_is_exclusive(x_1152)) {
 lean_ctor_release(x_1152, 0);
 lean_ctor_release(x_1152, 1);
 x_1158 = x_1152;
} else {
 lean_dec_ref(x_1152);
 x_1158 = lean_box(0);
}
if (lean_is_scalar(x_1158)) {
 x_1159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1159 = x_1158;
}
lean_ctor_set(x_1159, 0, x_1156);
lean_ctor_set(x_1159, 1, x_1157);
return x_1159;
}
}
}
block_1131:
{
lean_object* x_1123; 
x_1123 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_1122);
lean_dec(x_3);
if (lean_obj_tag(x_1123) == 0)
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
x_1124 = lean_ctor_get(x_1123, 1);
lean_inc(x_1124);
if (lean_is_exclusive(x_1123)) {
 lean_ctor_release(x_1123, 0);
 lean_ctor_release(x_1123, 1);
 x_1125 = x_1123;
} else {
 lean_dec_ref(x_1123);
 x_1125 = lean_box(0);
}
if (lean_is_scalar(x_1125)) {
 x_1126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1126 = x_1125;
}
lean_ctor_set(x_1126, 0, x_1121);
lean_ctor_set(x_1126, 1, x_1124);
return x_1126;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
lean_dec_ref(x_1121);
x_1127 = lean_ctor_get(x_1123, 0);
lean_inc(x_1127);
x_1128 = lean_ctor_get(x_1123, 1);
lean_inc(x_1128);
if (lean_is_exclusive(x_1123)) {
 lean_ctor_release(x_1123, 0);
 lean_ctor_release(x_1123, 1);
 x_1129 = x_1123;
} else {
 lean_dec_ref(x_1123);
 x_1129 = lean_box(0);
}
if (lean_is_scalar(x_1129)) {
 x_1130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1130 = x_1129;
}
lean_ctor_set(x_1130, 0, x_1127);
lean_ctor_set(x_1130, 1, x_1128);
return x_1130;
}
}
block_1145:
{
uint8_t x_1134; 
x_1134 = lean_nat_dec_lt(x_1081, x_1132);
if (x_1134 == 0)
{
lean_dec(x_1132);
lean_dec_ref(x_1120);
lean_dec(x_6);
x_1122 = x_1133;
goto block_1131;
}
else
{
uint8_t x_1135; 
x_1135 = lean_nat_dec_le(x_1132, x_1132);
if (x_1135 == 0)
{
lean_dec(x_1132);
lean_dec_ref(x_1120);
lean_dec(x_6);
x_1122 = x_1133;
goto block_1131;
}
else
{
lean_object* x_1136; size_t x_1137; size_t x_1138; lean_object* x_1139; 
x_1136 = lean_box(0);
x_1137 = 0;
x_1138 = lean_usize_of_nat(x_1132);
lean_dec(x_1132);
x_1139 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1120, x_1137, x_1138, x_1136, x_6, x_1133);
lean_dec(x_6);
lean_dec_ref(x_1120);
if (lean_obj_tag(x_1139) == 0)
{
lean_object* x_1140; 
x_1140 = lean_ctor_get(x_1139, 1);
lean_inc(x_1140);
lean_dec_ref(x_1139);
x_1122 = x_1140;
goto block_1131;
}
else
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
lean_dec_ref(x_1121);
lean_dec(x_3);
x_1141 = lean_ctor_get(x_1139, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1139, 1);
lean_inc(x_1142);
if (lean_is_exclusive(x_1139)) {
 lean_ctor_release(x_1139, 0);
 lean_ctor_release(x_1139, 1);
 x_1143 = x_1139;
} else {
 lean_dec_ref(x_1139);
 x_1143 = lean_box(0);
}
if (lean_is_scalar(x_1143)) {
 x_1144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1144 = x_1143;
}
lean_ctor_set(x_1144, 0, x_1141);
lean_ctor_set(x_1144, 1, x_1142);
return x_1144;
}
}
}
}
block_1148:
{
if (x_1146 == 0)
{
lean_inc_ref(x_1121);
lean_inc_ref(x_1120);
lean_dec_ref(x_1091);
lean_dec(x_1089);
lean_dec(x_1087);
lean_dec(x_1085);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec_ref(x_1069);
lean_dec(x_1068);
lean_dec_ref(x_1);
x_1133 = x_1147;
goto block_1145;
}
else
{
if (x_54 == 0)
{
lean_dec(x_1132);
lean_dec(x_6);
x_1102 = x_3;
x_1103 = x_1147;
goto block_1116;
}
else
{
lean_inc_ref(x_1121);
lean_inc_ref(x_1120);
lean_dec_ref(x_1091);
lean_dec(x_1089);
lean_dec(x_1087);
lean_dec(x_1085);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec_ref(x_1069);
lean_dec(x_1068);
lean_dec_ref(x_1);
x_1133 = x_1147;
goto block_1145;
}
}
}
}
else
{
lean_object* x_1160; lean_object* x_1161; 
lean_inc_ref(x_1119);
lean_dec_ref(x_1091);
lean_dec(x_1089);
lean_dec(x_1087);
lean_dec(x_1085);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec_ref(x_1069);
lean_dec(x_1068);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1160 = lean_ctor_get(x_1119, 0);
lean_inc_ref(x_1160);
lean_dec_ref(x_1119);
if (lean_is_scalar(x_1080)) {
 x_1161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1161 = x_1080;
}
lean_ctor_set(x_1161, 0, x_1160);
lean_ctor_set(x_1161, 1, x_1088);
return x_1161;
}
}
block_1096:
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
if (lean_is_scalar(x_1072)) {
 x_1093 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1093 = x_1072;
}
lean_ctor_set(x_1093, 0, x_1068);
lean_ctor_set(x_1093, 1, x_1091);
lean_ctor_set(x_1093, 2, x_1075);
lean_ctor_set(x_1093, 3, x_1087);
if (lean_is_scalar(x_1076)) {
 x_1094 = lean_alloc_ctor(4, 1, 0);
} else {
 x_1094 = x_1076;
 lean_ctor_set_tag(x_1094, 4);
}
lean_ctor_set(x_1094, 0, x_1093);
if (lean_is_scalar(x_1089)) {
 x_1095 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1095 = x_1089;
}
lean_ctor_set(x_1095, 0, x_1094);
lean_ctor_set(x_1095, 1, x_1092);
return x_1095;
}
block_1101:
{
if (x_1098 == 0)
{
lean_dec(x_1085);
lean_dec(x_1070);
lean_dec_ref(x_1);
x_1092 = x_1097;
goto block_1096;
}
else
{
uint8_t x_1099; 
x_1099 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_1070, x_1075);
lean_dec(x_1070);
if (x_1099 == 0)
{
lean_dec(x_1085);
lean_dec_ref(x_1);
x_1092 = x_1097;
goto block_1096;
}
else
{
lean_object* x_1100; 
lean_dec_ref(x_1091);
lean_dec(x_1089);
lean_dec(x_1087);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec(x_1068);
if (lean_is_scalar(x_1085)) {
 x_1100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1100 = x_1085;
}
lean_ctor_set(x_1100, 0, x_1);
lean_ctor_set(x_1100, 1, x_1097);
return x_1100;
}
}
}
block_1116:
{
lean_object* x_1104; 
lean_inc(x_1075);
x_1104 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1075, x_1102, x_1103);
lean_dec(x_1102);
if (lean_obj_tag(x_1104) == 0)
{
lean_object* x_1105; size_t x_1106; size_t x_1107; uint8_t x_1108; 
x_1105 = lean_ctor_get(x_1104, 1);
lean_inc(x_1105);
lean_dec_ref(x_1104);
x_1106 = lean_ptr_addr(x_1071);
lean_dec_ref(x_1071);
x_1107 = lean_ptr_addr(x_1087);
x_1108 = lean_usize_dec_eq(x_1106, x_1107);
if (x_1108 == 0)
{
lean_dec_ref(x_1069);
x_1097 = x_1105;
x_1098 = x_1108;
goto block_1101;
}
else
{
size_t x_1109; size_t x_1110; uint8_t x_1111; 
x_1109 = lean_ptr_addr(x_1069);
lean_dec_ref(x_1069);
x_1110 = lean_ptr_addr(x_1091);
x_1111 = lean_usize_dec_eq(x_1109, x_1110);
x_1097 = x_1105;
x_1098 = x_1111;
goto block_1101;
}
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
lean_dec_ref(x_1091);
lean_dec(x_1089);
lean_dec(x_1087);
lean_dec(x_1085);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec_ref(x_1069);
lean_dec(x_1068);
lean_dec_ref(x_1);
x_1112 = lean_ctor_get(x_1104, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1104, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 lean_ctor_release(x_1104, 1);
 x_1114 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1114 = lean_box(0);
}
if (lean_is_scalar(x_1114)) {
 x_1115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1115 = x_1114;
}
lean_ctor_set(x_1115, 0, x_1112);
lean_ctor_set(x_1115, 1, x_1113);
return x_1115;
}
}
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
lean_dec(x_1085);
lean_dec(x_1080);
lean_dec(x_1078);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec_ref(x_1069);
lean_dec(x_1068);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1162 = lean_ctor_get(x_1086, 0);
lean_inc(x_1162);
x_1163 = lean_ctor_get(x_1086, 1);
lean_inc(x_1163);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 lean_ctor_release(x_1086, 1);
 x_1164 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1164 = lean_box(0);
}
if (lean_is_scalar(x_1164)) {
 x_1165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1165 = x_1164;
}
lean_ctor_set(x_1165, 0, x_1162);
lean_ctor_set(x_1165, 1, x_1163);
return x_1165;
}
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; 
lean_dec(x_1080);
lean_dec(x_1078);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec_ref(x_1069);
lean_dec(x_1068);
lean_dec_ref(x_775);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1166 = lean_ctor_get(x_1082, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1082, 1);
lean_inc(x_1167);
if (lean_is_exclusive(x_1082)) {
 lean_ctor_release(x_1082, 0);
 lean_ctor_release(x_1082, 1);
 x_1168 = x_1082;
} else {
 lean_dec_ref(x_1082);
 x_1168 = lean_box(0);
}
if (lean_is_scalar(x_1168)) {
 x_1169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1169 = x_1168;
}
lean_ctor_set(x_1169, 0, x_1166);
lean_ctor_set(x_1169, 1, x_1167);
return x_1169;
}
}
else
{
lean_object* x_1170; 
lean_dec(x_1072);
lean_dec_ref(x_1071);
lean_dec(x_1070);
lean_dec_ref(x_1069);
lean_dec(x_1068);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1170 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_775, x_8, x_1067);
lean_dec(x_8);
lean_dec_ref(x_775);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1170;
}
}
else
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
lean_dec_ref(x_1061);
lean_dec_ref(x_775);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1171 = lean_ctor_get(x_1062, 1);
lean_inc(x_1171);
if (lean_is_exclusive(x_1062)) {
 lean_ctor_release(x_1062, 0);
 lean_ctor_release(x_1062, 1);
 x_1172 = x_1062;
} else {
 lean_dec_ref(x_1062);
 x_1172 = lean_box(0);
}
x_1173 = lean_ctor_get(x_1063, 0);
lean_inc(x_1173);
lean_dec_ref(x_1063);
if (lean_is_scalar(x_1172)) {
 x_1174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1174 = x_1172;
}
lean_ctor_set(x_1174, 0, x_1173);
lean_ctor_set(x_1174, 1, x_1171);
return x_1174;
}
}
else
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
lean_dec_ref(x_1061);
lean_dec_ref(x_775);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1175 = lean_ctor_get(x_1062, 0);
lean_inc(x_1175);
x_1176 = lean_ctor_get(x_1062, 1);
lean_inc(x_1176);
if (lean_is_exclusive(x_1062)) {
 lean_ctor_release(x_1062, 0);
 lean_ctor_release(x_1062, 1);
 x_1177 = x_1062;
} else {
 lean_dec_ref(x_1062);
 x_1177 = lean_box(0);
}
if (lean_is_scalar(x_1177)) {
 x_1178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1178 = x_1177;
}
lean_ctor_set(x_1178, 0, x_1175);
lean_ctor_set(x_1178, 1, x_1176);
return x_1178;
}
}
case 5:
{
lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1179 = lean_ctor_get(x_1, 0);
x_1180 = lean_st_ref_get(x_3, x_710);
x_1181 = lean_ctor_get(x_1180, 0);
lean_inc(x_1181);
x_1182 = lean_ctor_get(x_1180, 1);
lean_inc(x_1182);
lean_dec_ref(x_1180);
x_1183 = lean_ctor_get(x_1181, 0);
lean_inc_ref(x_1183);
lean_dec(x_1181);
lean_inc(x_1179);
x_1184 = l_Lean_Compiler_LCNF_normFVarImp(x_1183, x_1179, x_54);
lean_dec_ref(x_1183);
if (lean_obj_tag(x_1184) == 0)
{
lean_object* x_1185; lean_object* x_1186; 
lean_dec_ref(x_775);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1185 = lean_ctor_get(x_1184, 0);
lean_inc(x_1185);
lean_dec_ref(x_1184);
lean_inc(x_1185);
x_1186 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1185, x_3, x_1182);
lean_dec(x_3);
if (lean_obj_tag(x_1186) == 0)
{
lean_object* x_1187; lean_object* x_1188; uint8_t x_1189; 
x_1187 = lean_ctor_get(x_1186, 1);
lean_inc(x_1187);
if (lean_is_exclusive(x_1186)) {
 lean_ctor_release(x_1186, 0);
 lean_ctor_release(x_1186, 1);
 x_1188 = x_1186;
} else {
 lean_dec_ref(x_1186);
 x_1188 = lean_box(0);
}
x_1189 = l_Lean_beqFVarId____x40_Lean_Expr_2479116559____hygCtx___hyg_22_(x_1179, x_1185);
if (x_1189 == 0)
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1190 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1190 = lean_box(0);
}
if (lean_is_scalar(x_1190)) {
 x_1191 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1191 = x_1190;
}
lean_ctor_set(x_1191, 0, x_1185);
if (lean_is_scalar(x_1188)) {
 x_1192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1192 = x_1188;
}
lean_ctor_set(x_1192, 0, x_1191);
lean_ctor_set(x_1192, 1, x_1187);
return x_1192;
}
else
{
lean_object* x_1193; 
lean_dec(x_1185);
if (lean_is_scalar(x_1188)) {
 x_1193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1193 = x_1188;
}
lean_ctor_set(x_1193, 0, x_1);
lean_ctor_set(x_1193, 1, x_1187);
return x_1193;
}
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; 
lean_dec(x_1185);
lean_dec_ref(x_1);
x_1194 = lean_ctor_get(x_1186, 0);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1186, 1);
lean_inc(x_1195);
if (lean_is_exclusive(x_1186)) {
 lean_ctor_release(x_1186, 0);
 lean_ctor_release(x_1186, 1);
 x_1196 = x_1186;
} else {
 lean_dec_ref(x_1186);
 x_1196 = lean_box(0);
}
if (lean_is_scalar(x_1196)) {
 x_1197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1197 = x_1196;
}
lean_ctor_set(x_1197, 0, x_1194);
lean_ctor_set(x_1197, 1, x_1195);
return x_1197;
}
}
else
{
lean_object* x_1198; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1198 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_775, x_8, x_1182);
lean_dec(x_8);
lean_dec_ref(x_775);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1198;
}
}
case 6:
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; size_t x_1206; size_t x_1207; uint8_t x_1208; 
lean_dec_ref(x_775);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1199 = lean_ctor_get(x_1, 0);
x_1200 = lean_st_ref_get(x_3, x_710);
lean_dec(x_3);
x_1201 = lean_ctor_get(x_1200, 0);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1200, 1);
lean_inc(x_1202);
if (lean_is_exclusive(x_1200)) {
 lean_ctor_release(x_1200, 0);
 lean_ctor_release(x_1200, 1);
 x_1203 = x_1200;
} else {
 lean_dec_ref(x_1200);
 x_1203 = lean_box(0);
}
x_1204 = lean_ctor_get(x_1201, 0);
lean_inc_ref(x_1204);
lean_dec(x_1201);
lean_inc_ref(x_1199);
x_1205 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1204, x_54, x_1199);
lean_dec_ref(x_1204);
x_1206 = lean_ptr_addr(x_1199);
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
if (lean_is_scalar(x_1203)) {
 x_1211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1211 = x_1203;
}
lean_ctor_set(x_1211, 0, x_1210);
lean_ctor_set(x_1211, 1, x_1202);
return x_1211;
}
else
{
lean_object* x_1212; 
lean_dec_ref(x_1205);
if (lean_is_scalar(x_1203)) {
 x_1212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1212 = x_1203;
}
lean_ctor_set(x_1212, 0, x_1);
lean_ctor_set(x_1212, 1, x_1202);
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
x_711 = x_1213;
x_712 = x_1214;
x_713 = x_2;
x_714 = x_3;
x_715 = x_4;
x_716 = x_5;
x_717 = x_6;
x_718 = x_775;
x_719 = x_8;
goto block_772;
}
}
block_772:
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_720 = lean_ctor_get(x_711, 0);
x_721 = lean_ctor_get(x_711, 2);
x_722 = lean_ctor_get(x_711, 3);
x_723 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_720, x_714, x_710);
if (lean_obj_tag(x_723) == 0)
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; uint8_t x_727; 
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec_ref(x_723);
lean_inc(x_724);
lean_inc_ref(x_1);
lean_inc_ref(x_712);
x_726 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_726, 0, x_712);
lean_closure_set(x_726, 1, x_1);
lean_closure_set(x_726, 2, x_724);
x_727 = lean_unbox(x_724);
if (x_727 == 0)
{
uint8_t x_728; 
lean_dec(x_724);
lean_dec_ref(x_712);
x_728 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_728 == 0)
{
x_18 = x_726;
x_19 = x_711;
x_20 = x_713;
x_21 = x_714;
x_22 = x_715;
x_23 = x_716;
x_24 = x_717;
x_25 = x_718;
x_26 = x_719;
x_27 = x_725;
goto block_37;
}
else
{
uint8_t x_729; 
lean_inc_ref(x_722);
x_729 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_722, x_721);
if (x_729 == 0)
{
x_18 = x_726;
x_19 = x_711;
x_20 = x_713;
x_21 = x_714;
x_22 = x_715;
x_23 = x_716;
x_24 = x_717;
x_25 = x_718;
x_26 = x_719;
x_27 = x_725;
goto block_37;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_730 = lean_st_ref_get(x_714, x_725);
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec_ref(x_730);
x_733 = lean_ctor_get(x_731, 0);
lean_inc_ref(x_733);
lean_dec(x_731);
x_734 = l_Lean_Compiler_LCNF_normFunDeclImp(x_54, x_711, x_733, x_716, x_717, x_718, x_719, x_732);
lean_dec_ref(x_733);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec_ref(x_734);
lean_inc(x_719);
lean_inc_ref(x_718);
lean_inc(x_717);
lean_inc_ref(x_716);
x_737 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_735, x_716, x_717, x_718, x_719, x_736);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_738 = lean_ctor_get(x_737, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_737, 1);
lean_inc(x_739);
lean_dec_ref(x_737);
x_740 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_714, x_739);
if (lean_obj_tag(x_740) == 0)
{
lean_object* x_741; 
x_741 = lean_ctor_get(x_740, 1);
lean_inc(x_741);
lean_dec_ref(x_740);
x_18 = x_726;
x_19 = x_738;
x_20 = x_713;
x_21 = x_714;
x_22 = x_715;
x_23 = x_716;
x_24 = x_717;
x_25 = x_718;
x_26 = x_719;
x_27 = x_741;
goto block_37;
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_738);
lean_dec_ref(x_726);
lean_dec(x_719);
lean_dec_ref(x_718);
lean_dec(x_717);
lean_dec_ref(x_716);
lean_dec_ref(x_715);
lean_dec(x_714);
lean_dec_ref(x_713);
x_742 = lean_ctor_get(x_740, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_740, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 x_744 = x_740;
} else {
 lean_dec_ref(x_740);
 x_744 = lean_box(0);
}
if (lean_is_scalar(x_744)) {
 x_745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_745 = x_744;
}
lean_ctor_set(x_745, 0, x_742);
lean_ctor_set(x_745, 1, x_743);
return x_745;
}
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec_ref(x_726);
lean_dec(x_719);
lean_dec_ref(x_718);
lean_dec(x_717);
lean_dec_ref(x_716);
lean_dec_ref(x_715);
lean_dec(x_714);
lean_dec_ref(x_713);
x_746 = lean_ctor_get(x_737, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_737, 1);
lean_inc(x_747);
if (lean_is_exclusive(x_737)) {
 lean_ctor_release(x_737, 0);
 lean_ctor_release(x_737, 1);
 x_748 = x_737;
} else {
 lean_dec_ref(x_737);
 x_748 = lean_box(0);
}
if (lean_is_scalar(x_748)) {
 x_749 = lean_alloc_ctor(1, 2, 0);
} else {
 x_749 = x_748;
}
lean_ctor_set(x_749, 0, x_746);
lean_ctor_set(x_749, 1, x_747);
return x_749;
}
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec_ref(x_726);
lean_dec(x_719);
lean_dec_ref(x_718);
lean_dec(x_717);
lean_dec_ref(x_716);
lean_dec_ref(x_715);
lean_dec(x_714);
lean_dec_ref(x_713);
x_750 = lean_ctor_get(x_734, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_734, 1);
lean_inc(x_751);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 x_752 = x_734;
} else {
 lean_dec_ref(x_734);
 x_752 = lean_box(0);
}
if (lean_is_scalar(x_752)) {
 x_753 = lean_alloc_ctor(1, 2, 0);
} else {
 x_753 = x_752;
}
lean_ctor_set(x_753, 0, x_750);
lean_ctor_set(x_753, 1, x_751);
return x_753;
}
}
}
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec_ref(x_726);
x_754 = lean_st_ref_get(x_714, x_725);
x_755 = lean_ctor_get(x_754, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_754, 1);
lean_inc(x_756);
lean_dec_ref(x_754);
x_757 = lean_ctor_get(x_755, 0);
lean_inc_ref(x_757);
lean_dec(x_755);
x_758 = l_Lean_Compiler_LCNF_normFunDeclImp(x_54, x_711, x_757, x_716, x_717, x_718, x_719, x_756);
lean_dec_ref(x_757);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; uint8_t x_762; lean_object* x_763; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec_ref(x_758);
x_761 = lean_box(0);
x_762 = lean_unbox(x_724);
lean_dec(x_724);
x_763 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_712, x_1, x_762, x_759, x_761, x_713, x_714, x_715, x_716, x_717, x_718, x_719, x_760);
return x_763;
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; 
lean_dec(x_724);
lean_dec(x_719);
lean_dec_ref(x_718);
lean_dec(x_717);
lean_dec_ref(x_716);
lean_dec_ref(x_715);
lean_dec(x_714);
lean_dec_ref(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_1);
x_764 = lean_ctor_get(x_758, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_758, 1);
lean_inc(x_765);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_766 = x_758;
} else {
 lean_dec_ref(x_758);
 x_766 = lean_box(0);
}
if (lean_is_scalar(x_766)) {
 x_767 = lean_alloc_ctor(1, 2, 0);
} else {
 x_767 = x_766;
}
lean_ctor_set(x_767, 0, x_764);
lean_ctor_set(x_767, 1, x_765);
return x_767;
}
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_719);
lean_dec_ref(x_718);
lean_dec(x_717);
lean_dec_ref(x_716);
lean_dec_ref(x_715);
lean_dec(x_714);
lean_dec_ref(x_713);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_1);
x_768 = lean_ctor_get(x_723, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_723, 1);
lean_inc(x_769);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 lean_ctor_release(x_723, 1);
 x_770 = x_723;
} else {
 lean_dec_ref(x_723);
 x_770 = lean_box(0);
}
if (lean_is_scalar(x_770)) {
 x_771 = lean_alloc_ctor(1, 2, 0);
} else {
 x_771 = x_770;
}
lean_ctor_set(x_771, 0, x_768);
lean_ctor_set(x_771, 1, x_769);
return x_771;
}
}
}
else
{
lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
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
x_1215 = lean_ctor_get(x_709, 0);
lean_inc(x_1215);
x_1216 = lean_ctor_get(x_709, 1);
lean_inc(x_1216);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_1217 = x_709;
} else {
 lean_dec_ref(x_709);
 x_1217 = lean_box(0);
}
if (lean_is_scalar(x_1217)) {
 x_1218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1218 = x_1217;
}
lean_ctor_set(x_1218, 0, x_1215);
lean_ctor_set(x_1218, 1, x_1216);
return x_1218;
}
}
}
else
{
lean_object* x_1219; 
lean_dec_ref(x_1);
x_1219 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1219;
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
x_1 = l_Lean_Compiler_LCNF_defaultParam____x40_Lean_Compiler_LCNF_Basic_2211743917____hygCtx___hyg_43_;
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
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Compiler_ImplementedByAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDead(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Bind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___closed__0 = _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___closed__0();
lean_mark_persistent(l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__7___redArg___closed__0);
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
