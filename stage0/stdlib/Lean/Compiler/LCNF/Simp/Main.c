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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__16;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__3;
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__4;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__0;
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__4;
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_object* l_Std_Iterators_instIteratorMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__15;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2069_(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__12;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__20;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__11;
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__2;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_hasLocalInst(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1209_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PRange_instUpwardEnumerableNat;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__9;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getCode(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__5;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__18;
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21;
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__13;
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__19;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__17;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
lean_object* l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__5;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__6;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_11 = l_Lean_Compiler_LCNF_instInhabitedAlt;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_1, x_2, x_7);
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
x_13 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_10 = x_4;
} else {
 lean_dec_ref(x_4);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
if (lean_is_scalar(x_10)) {
 x_15 = lean_alloc_ctor(0, 2, 0);
} else {
 x_15 = x_10;
}
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_8, 2);
lean_dec(x_18);
x_19 = lean_ctor_get(x_8, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; size_t x_43; size_t x_44; size_t x_45; size_t x_46; size_t x_47; lean_object* x_48; uint8_t x_49; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
x_24 = lean_array_uget(x_1, x_3);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_array_fget(x_11, x_12);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_12, x_27);
lean_dec(x_12);
lean_ctor_set(x_8, 1, x_28);
x_35 = lean_array_get_size(x_23);
x_36 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_25);
x_37 = 32;
x_38 = lean_uint64_shift_right(x_36, x_37);
x_39 = lean_uint64_xor(x_36, x_38);
x_40 = 16;
x_41 = lean_uint64_shift_right(x_39, x_40);
x_42 = lean_uint64_xor(x_39, x_41);
x_43 = lean_uint64_to_usize(x_42);
x_44 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_45 = 1;
x_46 = lean_usize_sub(x_44, x_45);
x_47 = lean_usize_land(x_43, x_46);
x_48 = lean_array_uget(x_23, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_25, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_nat_add(x_22, x_27);
lean_dec(x_22);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_25);
lean_ctor_set(x_51, 1, x_26);
lean_ctor_set(x_51, 2, x_48);
x_52 = lean_array_uset(x_23, x_47, x_51);
x_53 = lean_unsigned_to_nat(4u);
x_54 = lean_nat_mul(x_50, x_53);
x_55 = lean_unsigned_to_nat(3u);
x_56 = lean_nat_div(x_54, x_55);
lean_dec(x_54);
x_57 = lean_array_get_size(x_52);
x_58 = lean_nat_dec_le(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_52);
lean_ctor_set(x_9, 1, x_59);
lean_ctor_set(x_9, 0, x_50);
x_29 = x_9;
goto block_34;
}
else
{
lean_ctor_set(x_9, 1, x_52);
lean_ctor_set(x_9, 0, x_50);
x_29 = x_9;
goto block_34;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_box(0);
x_61 = lean_array_uset(x_23, x_47, x_60);
x_62 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_25, x_26, x_48);
x_63 = lean_array_uset(x_61, x_47, x_62);
lean_ctor_set(x_9, 1, x_63);
x_29 = x_9;
goto block_34;
}
block_34:
{
lean_object* x_30; size_t x_31; size_t x_32; 
if (lean_is_scalar(x_10)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_10;
}
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_29);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_4 = x_30;
goto _start;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; size_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; lean_object* x_90; uint8_t x_91; 
x_64 = lean_ctor_get(x_9, 0);
x_65 = lean_ctor_get(x_9, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_9);
x_66 = lean_array_uget(x_1, x_3);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_array_fget(x_11, x_12);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_12, x_69);
lean_dec(x_12);
lean_ctor_set(x_8, 1, x_70);
x_77 = lean_array_get_size(x_65);
x_78 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_67);
x_79 = 32;
x_80 = lean_uint64_shift_right(x_78, x_79);
x_81 = lean_uint64_xor(x_78, x_80);
x_82 = 16;
x_83 = lean_uint64_shift_right(x_81, x_82);
x_84 = lean_uint64_xor(x_81, x_83);
x_85 = lean_uint64_to_usize(x_84);
x_86 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_87 = 1;
x_88 = lean_usize_sub(x_86, x_87);
x_89 = lean_usize_land(x_85, x_88);
x_90 = lean_array_uget(x_65, x_89);
x_91 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_67, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_92 = lean_nat_add(x_64, x_69);
lean_dec(x_64);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_67);
lean_ctor_set(x_93, 1, x_68);
lean_ctor_set(x_93, 2, x_90);
x_94 = lean_array_uset(x_65, x_89, x_93);
x_95 = lean_unsigned_to_nat(4u);
x_96 = lean_nat_mul(x_92, x_95);
x_97 = lean_unsigned_to_nat(3u);
x_98 = lean_nat_div(x_96, x_97);
lean_dec(x_96);
x_99 = lean_array_get_size(x_94);
x_100 = lean_nat_dec_le(x_98, x_99);
lean_dec(x_99);
lean_dec(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_94);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_92);
lean_ctor_set(x_102, 1, x_101);
x_71 = x_102;
goto block_76;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_92);
lean_ctor_set(x_103, 1, x_94);
x_71 = x_103;
goto block_76;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_box(0);
x_105 = lean_array_uset(x_65, x_89, x_104);
x_106 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_67, x_68, x_90);
x_107 = lean_array_uset(x_105, x_89, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_64);
lean_ctor_set(x_108, 1, x_107);
x_71 = x_108;
goto block_76;
}
block_76:
{
lean_object* x_72; size_t x_73; size_t x_74; 
if (lean_is_scalar(x_10)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_10;
}
lean_ctor_set(x_72, 0, x_8);
lean_ctor_set(x_72, 1, x_71);
x_73 = 1;
x_74 = lean_usize_add(x_3, x_73);
x_3 = x_74;
x_4 = x_72;
goto _start;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; size_t x_132; size_t x_133; size_t x_134; size_t x_135; size_t x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_8);
x_109 = lean_ctor_get(x_9, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_110);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_111 = x_9;
} else {
 lean_dec_ref(x_9);
 x_111 = lean_box(0);
}
x_112 = lean_array_uget(x_1, x_3);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_array_fget(x_11, x_12);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_add(x_12, x_115);
lean_dec(x_12);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_11);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_13);
x_124 = lean_array_get_size(x_110);
x_125 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_113);
x_126 = 32;
x_127 = lean_uint64_shift_right(x_125, x_126);
x_128 = lean_uint64_xor(x_125, x_127);
x_129 = 16;
x_130 = lean_uint64_shift_right(x_128, x_129);
x_131 = lean_uint64_xor(x_128, x_130);
x_132 = lean_uint64_to_usize(x_131);
x_133 = lean_usize_of_nat(x_124);
lean_dec(x_124);
x_134 = 1;
x_135 = lean_usize_sub(x_133, x_134);
x_136 = lean_usize_land(x_132, x_135);
x_137 = lean_array_uget(x_110, x_136);
x_138 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_113, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_139 = lean_nat_add(x_109, x_115);
lean_dec(x_109);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_113);
lean_ctor_set(x_140, 1, x_114);
lean_ctor_set(x_140, 2, x_137);
x_141 = lean_array_uset(x_110, x_136, x_140);
x_142 = lean_unsigned_to_nat(4u);
x_143 = lean_nat_mul(x_139, x_142);
x_144 = lean_unsigned_to_nat(3u);
x_145 = lean_nat_div(x_143, x_144);
lean_dec(x_143);
x_146 = lean_array_get_size(x_141);
x_147 = lean_nat_dec_le(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_141);
if (lean_is_scalar(x_111)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_111;
}
lean_ctor_set(x_149, 0, x_139);
lean_ctor_set(x_149, 1, x_148);
x_118 = x_149;
goto block_123;
}
else
{
lean_object* x_150; 
if (lean_is_scalar(x_111)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_111;
}
lean_ctor_set(x_150, 0, x_139);
lean_ctor_set(x_150, 1, x_141);
x_118 = x_150;
goto block_123;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_box(0);
x_152 = lean_array_uset(x_110, x_136, x_151);
x_153 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_113, x_114, x_137);
x_154 = lean_array_uset(x_152, x_136, x_153);
if (lean_is_scalar(x_111)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_111;
}
lean_ctor_set(x_155, 0, x_109);
lean_ctor_set(x_155, 1, x_154);
x_118 = x_155;
goto block_123;
}
block_123:
{
lean_object* x_119; size_t x_120; size_t x_121; 
if (lean_is_scalar(x_10)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_10;
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = 1;
x_121 = lean_usize_add(x_3, x_120);
x_3 = x_121;
x_4 = x_119;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5___redArg(x_3, x_4, x_5, x_6, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_1);
x_9 = lean_apply_1(x_1, x_2);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_14 = x_3;
} else {
 lean_dec_ref(x_3);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_16);
lean_dec(x_10);
x_17 = 1;
x_18 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_16, x_13, x_17, x_8);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = 0;
x_22 = l_Lean_Compiler_LCNF_mkAuxParam(x_19, x_21, x_4, x_5, x_6, x_7, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; size_t x_43; size_t x_44; size_t x_45; size_t x_46; size_t x_47; lean_object* x_48; uint8_t x_49; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_array_push(x_12, x_23);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_28);
x_35 = lean_array_get_size(x_27);
x_36 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_15);
x_37 = 32;
x_38 = lean_uint64_shift_right(x_36, x_37);
x_39 = lean_uint64_xor(x_36, x_38);
x_40 = 16;
x_41 = lean_uint64_shift_right(x_39, x_40);
x_42 = lean_uint64_xor(x_39, x_41);
x_43 = lean_uint64_to_usize(x_42);
x_44 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_45 = 1;
x_46 = lean_usize_sub(x_44, x_45);
x_47 = lean_usize_land(x_43, x_46);
x_48 = lean_array_uget(x_27, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_15, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_26, x_50);
lean_dec(x_26);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_15);
lean_ctor_set(x_52, 1, x_34);
lean_ctor_set(x_52, 2, x_48);
x_53 = lean_array_uset(x_27, x_47, x_52);
x_54 = lean_unsigned_to_nat(4u);
x_55 = lean_nat_mul(x_51, x_54);
x_56 = lean_unsigned_to_nat(3u);
x_57 = lean_nat_div(x_55, x_56);
lean_dec(x_55);
x_58 = lean_array_get_size(x_53);
x_59 = lean_nat_dec_le(x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_53);
lean_ctor_set(x_13, 1, x_60);
lean_ctor_set(x_13, 0, x_51);
x_30 = x_13;
goto block_33;
}
else
{
lean_ctor_set(x_13, 1, x_53);
lean_ctor_set(x_13, 0, x_51);
x_30 = x_13;
goto block_33;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_box(0);
x_62 = lean_array_uset(x_27, x_47, x_61);
x_63 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_15, x_34, x_48);
x_64 = lean_array_uset(x_62, x_47, x_63);
lean_ctor_set(x_13, 1, x_64);
x_30 = x_13;
goto block_33;
}
block_33:
{
lean_object* x_31; 
if (lean_is_scalar(x_14)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_14;
}
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_2 = x_11;
x_3 = x_31;
x_8 = x_24;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_73; lean_object* x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; size_t x_82; size_t x_83; size_t x_84; size_t x_85; size_t x_86; lean_object* x_87; uint8_t x_88; 
x_65 = lean_ctor_get(x_13, 0);
x_66 = lean_ctor_get(x_13, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_13);
x_67 = lean_ctor_get(x_23, 0);
lean_inc(x_67);
x_68 = lean_array_push(x_12, x_23);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_67);
x_74 = lean_array_get_size(x_66);
x_75 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_15);
x_76 = 32;
x_77 = lean_uint64_shift_right(x_75, x_76);
x_78 = lean_uint64_xor(x_75, x_77);
x_79 = 16;
x_80 = lean_uint64_shift_right(x_78, x_79);
x_81 = lean_uint64_xor(x_78, x_80);
x_82 = lean_uint64_to_usize(x_81);
x_83 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_84 = 1;
x_85 = lean_usize_sub(x_83, x_84);
x_86 = lean_usize_land(x_82, x_85);
x_87 = lean_array_uget(x_66, x_86);
x_88 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_15, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_65, x_89);
lean_dec(x_65);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_15);
lean_ctor_set(x_91, 1, x_73);
lean_ctor_set(x_91, 2, x_87);
x_92 = lean_array_uset(x_66, x_86, x_91);
x_93 = lean_unsigned_to_nat(4u);
x_94 = lean_nat_mul(x_90, x_93);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_nat_div(x_94, x_95);
lean_dec(x_94);
x_97 = lean_array_get_size(x_92);
x_98 = lean_nat_dec_le(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_99);
x_69 = x_100;
goto block_72;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_92);
x_69 = x_101;
goto block_72;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_box(0);
x_103 = lean_array_uset(x_66, x_86, x_102);
x_104 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_15, x_73, x_87);
x_105 = lean_array_uset(x_103, x_86, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_65);
lean_ctor_set(x_106, 1, x_105);
x_69 = x_106;
goto block_72;
}
block_72:
{
lean_object* x_70; 
if (lean_is_scalar(x_14)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_14;
}
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_2 = x_11;
x_3 = x_70;
x_8 = x_24;
goto _start;
}
}
}
case 1:
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_9, 0);
lean_inc(x_107);
lean_dec_ref(x_9);
x_2 = x_107;
goto _start;
}
default: 
{
lean_object* x_109; 
lean_dec_ref(x_1);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_3);
lean_ctor_set(x_109, 1, x_8);
return x_109;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_1, x_6, x_7, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_fget(x_3, x_2);
return x_4;
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
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_2 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PRange_instUpwardEnumerableNat;
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_3 = lean_alloc_closure((void*)(l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__10;
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__14;
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__13;
x_3 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__12;
x_4 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__11;
x_5 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__16;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__15;
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__17;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__8;
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__18;
x_3 = l_Std_Iterators_Types_Attach_instIterator___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_f", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__20;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_59; uint8_t x_60; 
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
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5___redArg(x_10, x_18, x_19, x_17, x_9);
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
x_26 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__0___boxed), 2, 0);
x_27 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
x_59 = lean_array_get_size(x_10);
x_60 = lean_nat_dec_le(x_15, x_13);
if (x_60 == 0)
{
x_28 = x_15;
x_29 = x_59;
goto block_58;
}
else
{
lean_dec(x_15);
x_28 = x_13;
x_29 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_30 = l_Array_toSubarray___redArg(x_10, x_28, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__2___boxed), 2, 1);
lean_closure_set(x_33, 0, x_30);
if (lean_is_scalar(x_25)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_25;
}
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_24);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_31);
if (lean_is_scalar(x_23)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_23;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__18;
x_38 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__19;
lean_inc_ref(x_26);
x_39 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_26, x_38, x_37);
x_40 = l_Std_Iterators_instIteratorMap___redArg(x_37, x_39, x_26, x_33);
x_41 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_40, x_36, x_34, x_5, x_6, x_7, x_8, x_22);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l_Lean_Compiler_LCNF_Code_internalize(x_11, x_45, x_5, x_6, x_7, x_8, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = 0;
lean_inc(x_47);
x_50 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_47, x_49, x_3, x_5, x_6, x_7, x_8, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21;
x_53 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_44, x_47, x_52, x_5, x_6, x_7, x_8, x_51);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_47);
lean_dec(x_44);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__5(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6___boxed(lean_object** _args) {
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
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(x_1, x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_21, x_4, x_6, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_free_object(x_12);
lean_dec(x_21);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec_ref(x_22);
x_32 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4, x_31);
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
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_12, 0);
lean_inc(x_47);
lean_dec(x_12);
x_48 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_47, x_4, x_6, x_19);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_47);
lean_dec_ref(x_2);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec_ref(x_48);
x_56 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4, x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_47, 2);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_47, 4);
lean_inc_ref(x_59);
lean_dec(x_47);
x_60 = 0;
x_61 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_58, x_59, x_2, x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
lean_dec_ref(x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_62);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
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
lean_dec_ref(x_15);
lean_dec(x_14);
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = l_Lean_ConstantInfo_type(x_29);
lean_dec(x_29);
x_31 = l_Lean_Compiler_LCNF_hasLocalInst(x_30);
lean_dec_ref(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_32 = lean_box(0);
lean_ctor_set(x_20, 0, x_32);
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_40; 
lean_free_object(x_20);
x_33 = l_Lean_Meta_isInstance___redArg(x_17, x_7, x_23);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_40 = lean_unbox(x_34);
lean_dec(x_34);
if (x_40 == 0)
{
if (x_31 == 0)
{
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
goto block_39;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_inc(x_17);
x_41 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7, x_35);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_41, 1);
x_51 = lean_ctor_get(x_41, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_array_get_size(x_19);
x_55 = l_Lean_Compiler_LCNF_Decl_getArity(x_53);
lean_dec(x_53);
x_56 = lean_nat_dec_lt(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
lean_free_object(x_42);
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_57 = lean_box(0);
lean_ctor_set(x_41, 0, x_57);
return x_41;
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_free_object(x_41);
x_58 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_50);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_array_size(x_60);
x_63 = 0;
lean_inc(x_60);
x_64 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_62, x_63, x_60);
x_65 = l_Array_append___redArg(x_19, x_64);
lean_dec_ref(x_64);
lean_ctor_set(x_13, 2, x_65);
x_66 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_67 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_66, x_4, x_5, x_6, x_7, x_61);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_70);
lean_ctor_set(x_58, 1, x_26);
lean_ctor_set(x_58, 0, x_68);
x_71 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21;
x_72 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_60, x_58, x_71, x_4, x_5, x_6, x_7, x_69);
lean_dec_ref(x_4);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_75, x_3, x_5, x_6, x_7, x_74);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_77);
lean_dec(x_5);
lean_dec_ref(x_1);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
lean_ctor_set(x_42, 0, x_73);
lean_ctor_set(x_78, 0, x_42);
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
lean_ctor_set(x_42, 0, x_73);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_42);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_73);
lean_free_object(x_42);
lean_dec(x_5);
lean_dec_ref(x_1);
x_83 = !lean_is_exclusive(x_76);
if (x_83 == 0)
{
return x_76;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_76, 0);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_76);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_free_object(x_42);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_87 = !lean_is_exclusive(x_72);
if (x_87 == 0)
{
return x_72;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_72, 0);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_72);
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
lean_free_object(x_58);
lean_dec(x_60);
lean_free_object(x_42);
lean_free_object(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_91 = !lean_is_exclusive(x_67);
if (x_91 == 0)
{
return x_67;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_67, 0);
x_93 = lean_ctor_get(x_67, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_67);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get(x_58, 0);
x_96 = lean_ctor_get(x_58, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_58);
x_97 = lean_array_size(x_95);
x_98 = 0;
lean_inc(x_95);
x_99 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_97, x_98, x_95);
x_100 = l_Array_append___redArg(x_19, x_99);
lean_dec_ref(x_99);
lean_ctor_set(x_13, 2, x_100);
x_101 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_102 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_101, x_4, x_5, x_6, x_7, x_96);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_105);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_26);
x_107 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21;
x_108 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_95, x_106, x_107, x_4, x_5, x_6, x_7, x_104);
lean_dec_ref(x_4);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec_ref(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_111, x_3, x_5, x_6, x_7, x_110);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_113);
lean_dec(x_5);
lean_dec_ref(x_1);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
lean_ctor_set(x_42, 0, x_109);
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_42);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_109);
lean_free_object(x_42);
lean_dec(x_5);
lean_dec_ref(x_1);
x_118 = lean_ctor_get(x_112, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_120 = x_112;
} else {
 lean_dec_ref(x_112);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_free_object(x_42);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_122 = lean_ctor_get(x_108, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_108, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_124 = x_108;
} else {
 lean_dec_ref(x_108);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_95);
lean_free_object(x_42);
lean_free_object(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_126 = lean_ctor_get(x_102, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_102, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_128 = x_102;
} else {
 lean_dec_ref(x_102);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_42, 0);
lean_inc(x_130);
lean_dec(x_42);
x_131 = lean_array_get_size(x_19);
x_132 = l_Lean_Compiler_LCNF_Decl_getArity(x_130);
lean_dec(x_130);
x_133 = lean_nat_dec_lt(x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
if (x_133 == 0)
{
lean_object* x_134; 
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_134 = lean_box(0);
lean_ctor_set(x_41, 0, x_134);
return x_41;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; size_t x_139; size_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_free_object(x_41);
x_135 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_50);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = lean_array_size(x_136);
x_140 = 0;
lean_inc(x_136);
x_141 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_139, x_140, x_136);
x_142 = l_Array_append___redArg(x_19, x_141);
lean_dec_ref(x_141);
lean_ctor_set(x_13, 2, x_142);
x_143 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_144 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_143, x_4, x_5, x_6, x_7, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec_ref(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_147);
if (lean_is_scalar(x_138)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_138;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_26);
x_149 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21;
x_150 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_136, x_148, x_149, x_4, x_5, x_6, x_7, x_146);
lean_dec_ref(x_4);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec_ref(x_150);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_153, x_3, x_5, x_6, x_7, x_152);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec_ref(x_154);
x_156 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_155);
lean_dec(x_5);
lean_dec_ref(x_1);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_151);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_151);
lean_dec(x_5);
lean_dec_ref(x_1);
x_161 = lean_ctor_get(x_154, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_154, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_163 = x_154;
} else {
 lean_dec_ref(x_154);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_165 = lean_ctor_get(x_150, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_150, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_167 = x_150;
} else {
 lean_dec_ref(x_150);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_138);
lean_dec(x_136);
lean_free_object(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_169 = lean_ctor_get(x_144, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_144, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_171 = x_144;
} else {
 lean_dec_ref(x_144);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_41, 1);
lean_inc(x_173);
lean_dec(x_41);
x_174 = lean_ctor_get(x_42, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_175 = x_42;
} else {
 lean_dec_ref(x_42);
 x_175 = lean_box(0);
}
x_176 = lean_array_get_size(x_19);
x_177 = l_Lean_Compiler_LCNF_Decl_getArity(x_174);
lean_dec(x_174);
x_178 = lean_nat_dec_lt(x_176, x_177);
lean_dec(x_177);
lean_dec(x_176);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_175);
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_173);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; size_t x_185; size_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_181 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_173);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_184 = x_181;
} else {
 lean_dec_ref(x_181);
 x_184 = lean_box(0);
}
x_185 = lean_array_size(x_182);
x_186 = 0;
lean_inc(x_182);
x_187 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_185, x_186, x_182);
x_188 = l_Array_append___redArg(x_19, x_187);
lean_dec_ref(x_187);
lean_ctor_set(x_13, 2, x_188);
x_189 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_190 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_189, x_4, x_5, x_6, x_7, x_183);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec_ref(x_190);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_193);
if (lean_is_scalar(x_184)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_184;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_26);
x_195 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21;
x_196 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_182, x_194, x_195, x_4, x_5, x_6, x_7, x_192);
lean_dec_ref(x_4);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec_ref(x_196);
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
x_200 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_199, x_3, x_5, x_6, x_7, x_198);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec_ref(x_200);
x_202 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_201);
lean_dec(x_5);
lean_dec_ref(x_1);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_204 = x_202;
} else {
 lean_dec_ref(x_202);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_205 = lean_alloc_ctor(1, 1, 0);
} else {
 x_205 = x_175;
}
lean_ctor_set(x_205, 0, x_197);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_204;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_203);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_197);
lean_dec(x_175);
lean_dec(x_5);
lean_dec_ref(x_1);
x_207 = lean_ctor_get(x_200, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_200, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_209 = x_200;
} else {
 lean_dec_ref(x_200);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_175);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_211 = lean_ctor_get(x_196, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_196, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_213 = x_196;
} else {
 lean_dec_ref(x_196);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_184);
lean_dec(x_182);
lean_dec(x_175);
lean_free_object(x_26);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_215 = lean_ctor_get(x_190, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_190, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_217 = x_190;
} else {
 lean_dec_ref(x_190);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
}
}
}
}
else
{
lean_free_object(x_26);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
goto block_39;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_219 = lean_ctor_get(x_26, 0);
lean_inc(x_219);
lean_dec(x_26);
x_220 = l_Lean_ConstantInfo_type(x_219);
lean_dec(x_219);
x_221 = l_Lean_Compiler_LCNF_hasLocalInst(x_220);
lean_dec_ref(x_220);
if (x_221 == 0)
{
lean_object* x_222; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_222 = lean_box(0);
lean_ctor_set(x_20, 0, x_222);
return x_20;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_230; 
lean_free_object(x_20);
x_223 = l_Lean_Meta_isInstance___redArg(x_17, x_7, x_23);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_230 = lean_unbox(x_224);
lean_dec(x_224);
if (x_230 == 0)
{
if (x_221 == 0)
{
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
goto block_229;
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_226);
lean_inc(x_17);
x_231 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7, x_225);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_237 = lean_ctor_get(x_231, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_238 = x_231;
} else {
 lean_dec_ref(x_231);
 x_238 = lean_box(0);
}
x_239 = lean_ctor_get(x_232, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 x_240 = x_232;
} else {
 lean_dec_ref(x_232);
 x_240 = lean_box(0);
}
x_241 = lean_array_get_size(x_19);
x_242 = l_Lean_Compiler_LCNF_Decl_getArity(x_239);
lean_dec(x_239);
x_243 = lean_nat_dec_lt(x_241, x_242);
lean_dec(x_242);
lean_dec(x_241);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_240);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_244 = lean_box(0);
if (lean_is_scalar(x_238)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_238;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_237);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; size_t x_250; size_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_238);
x_246 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_237);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = lean_array_size(x_247);
x_251 = 0;
lean_inc(x_247);
x_252 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_250, x_251, x_247);
x_253 = l_Array_append___redArg(x_19, x_252);
lean_dec_ref(x_252);
lean_ctor_set(x_13, 2, x_253);
x_254 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_255 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_254, x_4, x_5, x_6, x_7, x_248);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec_ref(x_255);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
x_259 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_259, 0, x_258);
if (lean_is_scalar(x_249)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_249;
}
lean_ctor_set(x_260, 0, x_256);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21;
x_262 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_247, x_260, x_261, x_4, x_5, x_6, x_7, x_257);
lean_dec_ref(x_4);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec_ref(x_262);
x_265 = lean_ctor_get(x_263, 0);
lean_inc(x_265);
x_266 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_265, x_3, x_5, x_6, x_7, x_264);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec_ref(x_266);
x_268 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_267);
lean_dec(x_5);
lean_dec_ref(x_1);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_270 = x_268;
} else {
 lean_dec_ref(x_268);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_271 = lean_alloc_ctor(1, 1, 0);
} else {
 x_271 = x_240;
}
lean_ctor_set(x_271, 0, x_263);
if (lean_is_scalar(x_270)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_270;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_269);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_263);
lean_dec(x_240);
lean_dec(x_5);
lean_dec_ref(x_1);
x_273 = lean_ctor_get(x_266, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_266, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_275 = x_266;
} else {
 lean_dec_ref(x_266);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_240);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_277 = lean_ctor_get(x_262, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_262, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_279 = x_262;
} else {
 lean_dec_ref(x_262);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_249);
lean_dec(x_247);
lean_dec(x_240);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_281 = lean_ctor_get(x_255, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_255, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_283 = x_255;
} else {
 lean_dec_ref(x_255);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
}
}
}
else
{
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
goto block_229;
}
block_229:
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_box(0);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
}
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; 
x_285 = lean_ctor_get(x_20, 0);
x_286 = lean_ctor_get(x_20, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_20);
x_287 = lean_ctor_get(x_285, 0);
lean_inc_ref(x_287);
lean_dec(x_285);
x_288 = 0;
lean_inc(x_17);
x_289 = l_Lean_Environment_find_x3f(x_287, x_17, x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; 
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_290 = lean_box(0);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_286);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_292 = lean_ctor_get(x_289, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 x_293 = x_289;
} else {
 lean_dec_ref(x_289);
 x_293 = lean_box(0);
}
x_294 = l_Lean_ConstantInfo_type(x_292);
lean_dec(x_292);
x_295 = l_Lean_Compiler_LCNF_hasLocalInst(x_294);
lean_dec_ref(x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_293);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_296 = lean_box(0);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_286);
return x_297;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_305; 
x_298 = l_Lean_Meta_isInstance___redArg(x_17, x_7, x_286);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_301 = x_298;
} else {
 lean_dec_ref(x_298);
 x_301 = lean_box(0);
}
x_305 = lean_unbox(x_299);
lean_dec(x_299);
if (x_305 == 0)
{
if (x_295 == 0)
{
lean_dec(x_293);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
goto block_304;
}
else
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_301);
lean_inc(x_17);
x_306 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7, x_300);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_293);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_309 = x_306;
} else {
 lean_dec_ref(x_306);
 x_309 = lean_box(0);
}
x_310 = lean_box(0);
if (lean_is_scalar(x_309)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_309;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_308);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_312 = lean_ctor_get(x_306, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_313 = x_306;
} else {
 lean_dec_ref(x_306);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_307, 0);
lean_inc(x_314);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_315 = x_307;
} else {
 lean_dec_ref(x_307);
 x_315 = lean_box(0);
}
x_316 = lean_array_get_size(x_19);
x_317 = l_Lean_Compiler_LCNF_Decl_getArity(x_314);
lean_dec(x_314);
x_318 = lean_nat_dec_lt(x_316, x_317);
lean_dec(x_317);
lean_dec(x_316);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_315);
lean_dec(x_293);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_319 = lean_box(0);
if (lean_is_scalar(x_313)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_313;
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_312);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; size_t x_325; size_t x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_313);
x_321 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_312);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_324 = x_321;
} else {
 lean_dec_ref(x_321);
 x_324 = lean_box(0);
}
x_325 = lean_array_size(x_322);
x_326 = 0;
lean_inc(x_322);
x_327 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_325, x_326, x_322);
x_328 = l_Array_append___redArg(x_19, x_327);
lean_dec_ref(x_327);
lean_ctor_set(x_13, 2, x_328);
x_329 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_330 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_329, x_4, x_5, x_6, x_7, x_323);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec_ref(x_330);
x_333 = lean_ctor_get(x_331, 0);
lean_inc(x_333);
if (lean_is_scalar(x_293)) {
 x_334 = lean_alloc_ctor(5, 1, 0);
} else {
 x_334 = x_293;
 lean_ctor_set_tag(x_334, 5);
}
lean_ctor_set(x_334, 0, x_333);
if (lean_is_scalar(x_324)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_324;
}
lean_ctor_set(x_335, 0, x_331);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21;
x_337 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_322, x_335, x_336, x_4, x_5, x_6, x_7, x_332);
lean_dec_ref(x_4);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec_ref(x_337);
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
x_341 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_340, x_3, x_5, x_6, x_7, x_339);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_342 = lean_ctor_get(x_341, 1);
lean_inc(x_342);
lean_dec_ref(x_341);
x_343 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_342);
lean_dec(x_5);
lean_dec_ref(x_1);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_345 = x_343;
} else {
 lean_dec_ref(x_343);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_346 = lean_alloc_ctor(1, 1, 0);
} else {
 x_346 = x_315;
}
lean_ctor_set(x_346, 0, x_338);
if (lean_is_scalar(x_345)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_345;
}
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_344);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_338);
lean_dec(x_315);
lean_dec(x_5);
lean_dec_ref(x_1);
x_348 = lean_ctor_get(x_341, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_341, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_350 = x_341;
} else {
 lean_dec_ref(x_341);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_315);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_352 = lean_ctor_get(x_337, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_337, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_354 = x_337;
} else {
 lean_dec_ref(x_337);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 2, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_324);
lean_dec(x_322);
lean_dec(x_315);
lean_dec(x_293);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_356 = lean_ctor_get(x_330, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_330, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_358 = x_330;
} else {
 lean_dec_ref(x_330);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
}
}
}
else
{
lean_dec(x_293);
lean_free_object(x_13);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
goto block_304;
}
block_304:
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_box(0);
if (lean_is_scalar(x_301)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_301;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_300);
return x_303;
}
}
}
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; 
x_360 = lean_ctor_get(x_13, 0);
x_361 = lean_ctor_get(x_13, 1);
x_362 = lean_ctor_get(x_13, 2);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_13);
x_363 = lean_st_ref_get(x_7, x_8);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_366 = x_363;
} else {
 lean_dec_ref(x_363);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_364, 0);
lean_inc_ref(x_367);
lean_dec(x_364);
x_368 = 0;
lean_inc(x_360);
x_369 = l_Lean_Environment_find_x3f(x_367, x_360, x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; 
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_370 = lean_box(0);
if (lean_is_scalar(x_366)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_366;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_365);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; 
x_372 = lean_ctor_get(x_369, 0);
lean_inc(x_372);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 x_373 = x_369;
} else {
 lean_dec_ref(x_369);
 x_373 = lean_box(0);
}
x_374 = l_Lean_ConstantInfo_type(x_372);
lean_dec(x_372);
x_375 = l_Lean_Compiler_LCNF_hasLocalInst(x_374);
lean_dec_ref(x_374);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; 
lean_dec(x_373);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_376 = lean_box(0);
if (lean_is_scalar(x_366)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_366;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_365);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_385; 
lean_dec(x_366);
x_378 = l_Lean_Meta_isInstance___redArg(x_360, x_7, x_365);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_381 = x_378;
} else {
 lean_dec_ref(x_378);
 x_381 = lean_box(0);
}
x_385 = lean_unbox(x_379);
lean_dec(x_379);
if (x_385 == 0)
{
if (x_375 == 0)
{
lean_dec(x_373);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
goto block_384;
}
else
{
lean_object* x_386; lean_object* x_387; 
lean_dec(x_381);
lean_inc(x_360);
x_386 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_360, x_4, x_7, x_380);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_373);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_389 = x_386;
} else {
 lean_dec_ref(x_386);
 x_389 = lean_box(0);
}
x_390 = lean_box(0);
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_388);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_392 = lean_ctor_get(x_386, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_393 = x_386;
} else {
 lean_dec_ref(x_386);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_387, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 x_395 = x_387;
} else {
 lean_dec_ref(x_387);
 x_395 = lean_box(0);
}
x_396 = lean_array_get_size(x_362);
x_397 = l_Lean_Compiler_LCNF_Decl_getArity(x_394);
lean_dec(x_394);
x_398 = lean_nat_dec_lt(x_396, x_397);
lean_dec(x_397);
lean_dec(x_396);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; 
lean_dec(x_395);
lean_dec(x_373);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_399 = lean_box(0);
if (lean_is_scalar(x_393)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_393;
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_392);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; size_t x_405; size_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_393);
x_401 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_392);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_404 = x_401;
} else {
 lean_dec_ref(x_401);
 x_404 = lean_box(0);
}
x_405 = lean_array_size(x_402);
x_406 = 0;
lean_inc(x_402);
x_407 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_405, x_406, x_402);
x_408 = l_Array_append___redArg(x_362, x_407);
lean_dec_ref(x_407);
x_409 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_409, 0, x_360);
lean_ctor_set(x_409, 1, x_361);
lean_ctor_set(x_409, 2, x_408);
x_410 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_411 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_409, x_410, x_4, x_5, x_6, x_7, x_403);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec_ref(x_411);
x_414 = lean_ctor_get(x_412, 0);
lean_inc(x_414);
if (lean_is_scalar(x_373)) {
 x_415 = lean_alloc_ctor(5, 1, 0);
} else {
 x_415 = x_373;
 lean_ctor_set_tag(x_415, 5);
}
lean_ctor_set(x_415, 0, x_414);
if (lean_is_scalar(x_404)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_404;
}
lean_ctor_set(x_416, 0, x_412);
lean_ctor_set(x_416, 1, x_415);
x_417 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21;
x_418 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_402, x_416, x_417, x_4, x_5, x_6, x_7, x_413);
lean_dec_ref(x_4);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec_ref(x_418);
x_421 = lean_ctor_get(x_419, 0);
lean_inc(x_421);
x_422 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_421, x_3, x_5, x_6, x_7, x_420);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
lean_dec_ref(x_422);
x_424 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_423);
lean_dec(x_5);
lean_dec_ref(x_1);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_426 = x_424;
} else {
 lean_dec_ref(x_424);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_427 = lean_alloc_ctor(1, 1, 0);
} else {
 x_427 = x_395;
}
lean_ctor_set(x_427, 0, x_419);
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_426;
}
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_425);
return x_428;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_419);
lean_dec(x_395);
lean_dec(x_5);
lean_dec_ref(x_1);
x_429 = lean_ctor_get(x_422, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_422, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_431 = x_422;
} else {
 lean_dec_ref(x_422);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_395);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_433 = lean_ctor_get(x_418, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_418, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_435 = x_418;
} else {
 lean_dec_ref(x_418);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_434);
return x_436;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_404);
lean_dec(x_402);
lean_dec(x_395);
lean_dec(x_373);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_437 = lean_ctor_get(x_411, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_411, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_439 = x_411;
} else {
 lean_dec_ref(x_411);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(1, 2, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_437);
lean_ctor_set(x_440, 1, x_438);
return x_440;
}
}
}
}
}
else
{
lean_dec(x_373);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
goto block_384;
}
block_384:
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_box(0);
if (lean_is_scalar(x_381)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_381;
}
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_380);
return x_383;
}
}
}
}
}
else
{
lean_object* x_441; lean_object* x_442; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_441 = lean_box(0);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_8);
return x_442;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_4, x_5, x_3);
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
x_11 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_9, x_5, x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_12, x_2);
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
x_20 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_18, x_5, x_19);
lean_dec_ref(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_21, x_2);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_5);
x_11 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_5, x_1, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_apply_9(x_2, x_5, x_3, x_1, x_4, x_6, x_7, x_8, x_9, x_12);
return x_13;
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___override___boxed), 1, 0);
return x_1;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
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
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_21, 2);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_21, 3);
lean_inc_ref(x_27);
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
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_12, 0);
lean_inc(x_269);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_269);
x_270 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_28, x_269, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec_ref(x_270);
x_273 = !lean_is_exclusive(x_3);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_274 = lean_ctor_get(x_3, 2);
x_275 = lean_ctor_get(x_3, 3);
x_276 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__4;
x_277 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__5;
lean_inc(x_269);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_269);
lean_ctor_set(x_278, 1, x_274);
x_279 = l_Lean_PersistentHashMap_insert___redArg(x_276, x_277, x_275, x_269, x_271);
lean_ctor_set(x_3, 3, x_279);
lean_ctor_set(x_3, 2, x_278);
x_215 = x_3;
x_216 = x_4;
x_217 = x_5;
x_218 = x_6;
x_219 = x_7;
x_220 = x_8;
x_221 = x_9;
x_222 = x_272;
goto block_268;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_280 = lean_ctor_get(x_3, 0);
x_281 = lean_ctor_get(x_3, 1);
x_282 = lean_ctor_get(x_3, 2);
x_283 = lean_ctor_get(x_3, 3);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_3);
x_284 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__4;
x_285 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__5;
lean_inc(x_269);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_269);
lean_ctor_set(x_286, 1, x_282);
x_287 = l_Lean_PersistentHashMap_insert___redArg(x_284, x_285, x_283, x_269, x_271);
x_288 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_288, 0, x_280);
lean_ctor_set(x_288, 1, x_281);
lean_ctor_set(x_288, 2, x_286);
lean_ctor_set(x_288, 3, x_287);
x_215 = x_288;
x_216 = x_4;
x_217 = x_5;
x_218 = x_6;
x_219 = x_7;
x_220 = x_8;
x_221 = x_9;
x_222 = x_272;
goto block_268;
}
}
else
{
uint8_t x_289; 
lean_dec(x_269);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
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
x_289 = !lean_is_exclusive(x_270);
if (x_289 == 0)
{
return x_270;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_270, 0);
x_291 = lean_ctor_get(x_270, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_270);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
lean_dec(x_12);
x_215 = x_3;
x_216 = x_4;
x_217 = x_5;
x_218 = x_6;
x_219 = x_7;
x_220 = x_8;
x_221 = x_9;
x_222 = x_23;
goto block_268;
}
block_177:
{
lean_object* x_44; 
lean_inc(x_34);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_37);
lean_inc_ref(x_40);
lean_inc(x_35);
lean_inc_ref(x_41);
x_44 = l_Lean_Compiler_LCNF_Simp_simp(x_36, x_41, x_35, x_40, x_37, x_42, x_43, x_34, x_38);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
lean_inc(x_45);
x_47 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec_ref(x_33);
x_48 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_35, x_46);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Lean_Compiler_LCNF_inferAppType(x_26, x_39, x_37, x_42, x_43, x_34, x_49);
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
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Compiler_LCNF_mkAuxParam(x_51, x_32, x_37, x_42, x_43, x_34, x_52);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_inc(x_34);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_37);
x_60 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_30, x_29, x_11, x_2, x_27, x_59, x_41, x_35, x_40, x_37, x_42, x_43, x_34, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_unsigned_to_nat(1u);
x_64 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_65 = lean_array_push(x_64, x_57);
x_66 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_67 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_65, x_61, x_66, x_37, x_42, x_43, x_34, x_62);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
lean_inc(x_68);
x_70 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_70, 0, x_68);
lean_closure_set(x_70, 1, x_63);
x_71 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_45, x_70, x_37, x_42, x_43, x_34, x_69);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_ctor_set_tag(x_55, 2);
lean_ctor_set(x_55, 1, x_73);
lean_ctor_set(x_55, 0, x_68);
if (lean_is_scalar(x_22)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_22;
}
lean_ctor_set(x_74, 0, x_55);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_71);
lean_ctor_set_tag(x_55, 2);
lean_ctor_set(x_55, 1, x_75);
lean_ctor_set(x_55, 0, x_68);
if (lean_is_scalar(x_22)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_22;
}
lean_ctor_set(x_77, 0, x_55);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_68);
lean_free_object(x_55);
lean_dec(x_22);
x_79 = !lean_is_exclusive(x_71);
if (x_79 == 0)
{
return x_71;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_71, 0);
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_71);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_free_object(x_55);
lean_dec(x_45);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec(x_22);
x_83 = !lean_is_exclusive(x_67);
if (x_83 == 0)
{
return x_67;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_67, 0);
x_85 = lean_ctor_get(x_67, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_67);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_free_object(x_55);
lean_dec(x_57);
lean_dec(x_45);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec(x_22);
x_87 = !lean_is_exclusive(x_60);
if (x_87 == 0)
{
return x_60;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_60, 0);
x_89 = lean_ctor_get(x_60, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_60);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_55, 0);
x_92 = lean_ctor_get(x_55, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_55);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_inc(x_34);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_37);
x_94 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_30, x_29, x_11, x_2, x_27, x_93, x_41, x_35, x_40, x_37, x_42, x_43, x_34, x_92);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = lean_unsigned_to_nat(1u);
x_98 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_99 = lean_array_push(x_98, x_91);
x_100 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_101 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_99, x_95, x_100, x_37, x_42, x_43, x_34, x_96);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
lean_inc(x_102);
x_104 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_104, 0, x_102);
lean_closure_set(x_104, 1, x_97);
x_105 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_45, x_104, x_37, x_42, x_43, x_34, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_106);
if (lean_is_scalar(x_22)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_22;
}
lean_ctor_set(x_110, 0, x_109);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_107);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_102);
lean_dec(x_22);
x_112 = lean_ctor_get(x_105, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_105, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_114 = x_105;
} else {
 lean_dec_ref(x_105);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_45);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec(x_22);
x_116 = lean_ctor_get(x_101, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_101, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_118 = x_101;
} else {
 lean_dec_ref(x_101);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_91);
lean_dec(x_45);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec(x_22);
x_120 = lean_ctor_get(x_94, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_94, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_122 = x_94;
} else {
 lean_dec_ref(x_94);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_51);
x_124 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
x_125 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21;
x_126 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_124, x_45, x_125, x_37, x_42, x_43, x_34, x_52);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
lean_inc(x_34);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_37);
x_129 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_127, x_37, x_42, x_43, x_34, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_inc(x_34);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_37);
lean_inc_ref(x_40);
lean_inc(x_35);
lean_inc_ref(x_41);
x_133 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_30, x_29, x_11, x_2, x_27, x_132, x_41, x_35, x_40, x_37, x_42, x_43, x_34, x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_130);
x_137 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_138 = lean_array_push(x_137, x_136);
x_139 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_138, x_134, x_41, x_35, x_40, x_37, x_42, x_43, x_34, x_135);
lean_dec(x_34);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_37);
lean_dec_ref(x_40);
lean_dec(x_35);
lean_dec_ref(x_41);
lean_dec_ref(x_138);
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
lean_dec(x_130);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_22);
x_147 = !lean_is_exclusive(x_133);
if (x_147 == 0)
{
return x_133;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_133, 0);
x_149 = lean_ctor_get(x_133, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_133);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_151 = !lean_is_exclusive(x_129);
if (x_151 == 0)
{
return x_129;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_129, 0);
x_153 = lean_ctor_get(x_129, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_129);
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
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_155 = !lean_is_exclusive(x_126);
if (x_155 == 0)
{
return x_126;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_126, 0);
x_157 = lean_ctor_get(x_126, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_126);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_11);
lean_dec_ref(x_2);
x_159 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_35, x_46);
lean_dec(x_35);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec_ref(x_159);
x_161 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_45, x_33, x_37, x_42, x_43, x_34, x_160);
if (lean_obj_tag(x_161) == 0)
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_161, 0);
if (lean_is_scalar(x_22)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_22;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_161, 0, x_164);
return x_161;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_161, 0);
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_161);
if (lean_is_scalar(x_22)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_22;
}
lean_ctor_set(x_167, 0, x_165);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
uint8_t x_169; 
lean_dec(x_22);
x_169 = !lean_is_exclusive(x_161);
if (x_169 == 0)
{
return x_161;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_161, 0);
x_171 = lean_ctor_get(x_161, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_161);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
uint8_t x_173; 
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_173 = !lean_is_exclusive(x_44);
if (x_173 == 0)
{
return x_44;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_44, 0);
x_175 = lean_ctor_get(x_44, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_44);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
block_214:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_inc_ref(x_27);
x_189 = l_Array_toSubarray___redArg(x_27, x_187, x_188);
x_190 = l_Array_ofSubarray___redArg(x_189);
lean_dec_ref(x_189);
lean_inc_ref(x_190);
x_191 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_24, x_25, x_190, x_32, x_184, x_180, x_183, x_182, x_185, x_186, x_179, x_181);
lean_dec_ref(x_24);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec_ref(x_191);
x_194 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_11);
if (x_194 == 0)
{
x_33 = x_178;
x_34 = x_179;
x_35 = x_180;
x_36 = x_192;
x_37 = x_182;
x_38 = x_193;
x_39 = x_190;
x_40 = x_183;
x_41 = x_184;
x_42 = x_185;
x_43 = x_186;
goto block_177;
}
else
{
uint8_t x_195; 
x_195 = lean_nat_dec_eq(x_29, x_30);
if (x_195 == 0)
{
x_33 = x_178;
x_34 = x_179;
x_35 = x_180;
x_36 = x_192;
x_37 = x_182;
x_38 = x_193;
x_39 = x_190;
x_40 = x_183;
x_41 = x_184;
x_42 = x_185;
x_43 = x_186;
goto block_177;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_190);
lean_dec_ref(x_178);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_196 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_180, x_193);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = l_Lean_Compiler_LCNF_Simp_simp(x_192, x_184, x_180, x_183, x_182, x_185, x_186, x_179, x_197);
if (lean_obj_tag(x_198) == 0)
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_198, 0);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_198, 0, x_201);
return x_198;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_198, 0);
x_203 = lean_ctor_get(x_198, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_198);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_202);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
else
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_198);
if (x_206 == 0)
{
return x_198;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_198, 0);
x_208 = lean_ctor_get(x_198, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_198);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
}
else
{
uint8_t x_210; 
lean_dec_ref(x_190);
lean_dec_ref(x_186);
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec(x_180);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_2);
x_210 = !lean_is_exclusive(x_191);
if (x_210 == 0)
{
return x_191;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_191, 0);
x_212 = lean_ctor_get(x_191, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_191);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
block_268:
{
if (x_32 == 0)
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
lean_dec(x_21);
lean_inc_ref(x_217);
lean_inc_ref(x_215);
lean_inc(x_216);
x_223 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2), 10, 4);
lean_closure_set(x_223, 0, x_216);
lean_closure_set(x_223, 1, x_31);
lean_closure_set(x_223, 2, x_215);
lean_closure_set(x_223, 3, x_217);
x_224 = lean_unsigned_to_nat(0u);
x_225 = lean_nat_dec_le(x_30, x_29);
if (x_225 == 0)
{
lean_inc(x_29);
x_178 = x_223;
x_179 = x_221;
x_180 = x_216;
x_181 = x_222;
x_182 = x_218;
x_183 = x_217;
x_184 = x_215;
x_185 = x_219;
x_186 = x_220;
x_187 = x_224;
x_188 = x_29;
goto block_214;
}
else
{
lean_inc(x_30);
x_178 = x_223;
x_179 = x_221;
x_180 = x_216;
x_181 = x_222;
x_182 = x_218;
x_183 = x_217;
x_184 = x_215;
x_185 = x_219;
x_186 = x_220;
x_187 = x_224;
x_188 = x_30;
goto block_214;
}
}
else
{
lean_object* x_226; 
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_22);
x_226 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_215, x_216, x_217, x_218, x_219, x_220, x_221, x_222);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec_ref(x_226);
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_229);
x_230 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_229, x_216, x_219, x_220, x_221, x_228);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec_ref(x_230);
x_232 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_216, x_231);
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_232, 1);
x_235 = lean_ctor_get(x_232, 0);
lean_dec(x_235);
lean_ctor_set_tag(x_232, 1);
lean_ctor_set(x_232, 1, x_2);
lean_ctor_set(x_232, 0, x_227);
x_236 = l_Lean_Compiler_LCNF_Simp_simp(x_232, x_215, x_216, x_217, x_218, x_219, x_220, x_221, x_234);
if (lean_obj_tag(x_236) == 0)
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_236, 0);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_236, 0, x_239);
return x_236;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_240 = lean_ctor_get(x_236, 0);
x_241 = lean_ctor_get(x_236, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_236);
x_242 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_242, 0, x_240);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
else
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_236);
if (x_244 == 0)
{
return x_236;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_236, 0);
x_246 = lean_ctor_get(x_236, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_236);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_232, 1);
lean_inc(x_248);
lean_dec(x_232);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_227);
lean_ctor_set(x_249, 1, x_2);
x_250 = l_Lean_Compiler_LCNF_Simp_simp(x_249, x_215, x_216, x_217, x_218, x_219, x_220, x_221, x_248);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_253 = x_250;
} else {
 lean_dec_ref(x_250);
 x_253 = lean_box(0);
}
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_251);
if (lean_is_scalar(x_253)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_253;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_252);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_250, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_250, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_258 = x_250;
} else {
 lean_dec_ref(x_250);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_227);
lean_dec(x_221);
lean_dec_ref(x_220);
lean_dec(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_217);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec_ref(x_2);
x_260 = !lean_is_exclusive(x_230);
if (x_260 == 0)
{
return x_230;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_230, 0);
x_262 = lean_ctor_get(x_230, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_230);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_221);
lean_dec_ref(x_220);
lean_dec(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_217);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_11);
lean_dec_ref(x_2);
x_264 = !lean_is_exclusive(x_226);
if (x_264 == 0)
{
return x_226;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_226, 0);
x_266 = lean_ctor_get(x_226, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_226);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
}
}
}
else
{
uint8_t x_293; 
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
x_293 = !lean_is_exclusive(x_13);
if (x_293 == 0)
{
return x_13;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_13, 0);
x_295 = lean_ctor_get(x_13, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_13);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
x_11 = lean_st_ref_get(x_3, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_3, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_14, x_1, x_9);
lean_dec_ref(x_14);
x_20 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_18, x_10, x_1);
lean_dec_ref(x_18);
x_21 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(x_2, x_19, x_20, x_4, x_5, x_6, x_7, x_17);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_1, x_2, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(x_8, x_5, x_6);
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
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1, x_2, x_3, x_4, x_6, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(x_8, x_4, x_5);
lean_dec_ref(x_8);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1, x_2, x_3, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_8, x_5, x_6);
lean_dec_ref(x_8);
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
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_2, x_3, x_4, x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_8, x_4, x_5);
lean_dec(x_8);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1, x_2, x_3, x_5, x_11);
return x_12;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
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
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
x_23 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_22, x_7, x_16);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec_ref(x_23);
x_27 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(x_4, x_7, x_10, x_26);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_15);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
if (x_3 == 0)
{
lean_object* x_32; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec_ref(x_23);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_dec_ref(x_23);
lean_inc_ref(x_4);
x_34 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_18 = x_35;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_2, x_4, x_15);
if (lean_is_scalar(x_17)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_17;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
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
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_36; uint8_t x_37; uint8_t x_57; lean_object* x_58; uint8_t x_60; lean_object* x_61; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_14);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_array_get_size(x_13);
x_65 = lean_nat_dec_lt(x_63, x_64);
if (x_65 == 0)
{
lean_dec(x_64);
x_60 = x_2;
x_61 = x_11;
goto block_62;
}
else
{
if (x_65 == 0)
{
lean_dec(x_64);
x_60 = x_2;
x_61 = x_11;
goto block_62;
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_68 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_13, x_66, x_67, x_10, x_11);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_60 = x_71;
x_61 = x_70;
goto block_62;
}
}
block_35:
{
lean_object* x_16; 
lean_inc_ref(x_9);
x_16 = l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_Compiler_LCNF_Simp_simp(x_14, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_3, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_3, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_3);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
block_56:
{
if (x_37 == 0)
{
x_15 = x_36;
goto block_35;
}
else
{
lean_object* x_38; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_1);
lean_inc_ref(x_14);
x_38 = l_Lean_Compiler_LCNF_Code_inferType(x_14, x_7, x_8, x_9, x_10, x_36);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_14, x_8, x_40);
lean_dec(x_8);
lean_dec_ref(x_14);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_5, x_42);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_46, 0, x_39);
x_47 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_3, x_46);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_49, 0, x_39);
x_50 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_3, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec_ref(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_3);
x_52 = !lean_is_exclusive(x_38);
if (x_52 == 0)
{
return x_38;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_38, 0);
x_54 = lean_ctor_get(x_38, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_38);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
block_59:
{
if (x_2 == 0)
{
x_15 = x_58;
goto block_35;
}
else
{
x_36 = x_58;
x_37 = x_57;
goto block_56;
}
}
block_62:
{
if (lean_obj_tag(x_14) == 6)
{
x_57 = x_60;
x_58 = x_61;
goto block_59;
}
else
{
if (x_2 == 0)
{
x_36 = x_61;
x_37 = x_60;
goto block_56;
}
else
{
x_57 = x_60;
x_58 = x_61;
goto block_59;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_72 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_72);
x_73 = l_Lean_Compiler_LCNF_Simp_simp(x_72, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_3, x_75);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_3, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec_ref(x_3);
x_81 = !lean_is_exclusive(x_73);
if (x_81 == 0)
{
return x_73;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_73, 0);
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_73);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_simp___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1), 12, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Compiler_LCNF_Simp_simp___closed__1;
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 2);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_39 = lean_ctor_get(x_32, 1);
lean_dec(x_39);
x_40 = l_Lean_Compiler_LCNF_Simp_simp___closed__2;
x_41 = l_Lean_Compiler_LCNF_Simp_simp___closed__3;
lean_inc_ref(x_35);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_42, 0, x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_38);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_37);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_47, 0, x_36);
lean_ctor_set(x_32, 4, x_45);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_47);
lean_ctor_set(x_32, 1, x_40);
lean_ctor_set(x_32, 0, x_44);
lean_ctor_set(x_30, 1, x_41);
x_48 = l_ReaderT_instMonad___redArg(x_30);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_50, 2);
x_55 = lean_ctor_get(x_50, 3);
x_56 = lean_ctor_get(x_50, 4);
x_57 = lean_ctor_get(x_50, 1);
lean_dec(x_57);
x_58 = l_Lean_Compiler_LCNF_Simp_simp___closed__4;
x_59 = l_Lean_Compiler_LCNF_Simp_simp___closed__5;
lean_inc_ref(x_53);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_60, 0, x_53);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_53);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_63, 0, x_56);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_64, 0, x_55);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_65, 0, x_54);
lean_ctor_set(x_50, 4, x_63);
lean_ctor_set(x_50, 3, x_64);
lean_ctor_set(x_50, 2, x_65);
lean_ctor_set(x_50, 1, x_58);
lean_ctor_set(x_50, 0, x_62);
lean_ctor_set(x_48, 1, x_59);
x_66 = l_ReaderT_instMonad___redArg(x_48);
x_67 = l_ReaderT_instMonad___redArg(x_66);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; uint8_t x_100; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_ctor_get(x_69, 2);
x_74 = lean_ctor_get(x_69, 3);
x_75 = lean_ctor_get(x_69, 4);
x_76 = lean_ctor_get(x_69, 1);
lean_dec(x_76);
x_77 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_78 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_72);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_79, 0, x_72);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_80, 0, x_72);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_82, 0, x_75);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_83, 0, x_74);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_84, 0, x_73);
lean_ctor_set(x_69, 4, x_82);
lean_ctor_set(x_69, 3, x_83);
lean_ctor_set(x_69, 2, x_84);
lean_ctor_set(x_69, 1, x_77);
lean_ctor_set(x_69, 0, x_81);
lean_ctor_set(x_67, 1, x_78);
x_85 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_7, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_7, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_7, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_7, 5);
lean_inc(x_90);
x_91 = lean_ctor_get(x_7, 6);
lean_inc(x_91);
x_92 = lean_ctor_get(x_7, 7);
lean_inc(x_92);
x_93 = lean_ctor_get(x_7, 8);
lean_inc(x_93);
x_94 = lean_ctor_get(x_7, 9);
lean_inc(x_94);
x_95 = lean_ctor_get(x_7, 10);
lean_inc(x_95);
x_96 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_97 = lean_ctor_get(x_7, 11);
lean_inc(x_97);
x_98 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_99 = lean_ctor_get(x_7, 12);
lean_inc_ref(x_99);
x_100 = lean_nat_dec_eq(x_88, x_89);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_7);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_171; lean_object* x_172; 
x_102 = lean_ctor_get(x_7, 12);
lean_dec(x_102);
x_103 = lean_ctor_get(x_7, 11);
lean_dec(x_103);
x_104 = lean_ctor_get(x_7, 10);
lean_dec(x_104);
x_105 = lean_ctor_get(x_7, 9);
lean_dec(x_105);
x_106 = lean_ctor_get(x_7, 8);
lean_dec(x_106);
x_107 = lean_ctor_get(x_7, 7);
lean_dec(x_107);
x_108 = lean_ctor_get(x_7, 6);
lean_dec(x_108);
x_109 = lean_ctor_get(x_7, 5);
lean_dec(x_109);
x_110 = lean_ctor_get(x_7, 4);
lean_dec(x_110);
x_111 = lean_ctor_get(x_7, 3);
lean_dec(x_111);
x_112 = lean_ctor_get(x_7, 2);
lean_dec(x_112);
x_113 = lean_ctor_get(x_7, 1);
lean_dec(x_113);
x_114 = lean_ctor_get(x_7, 0);
lean_dec(x_114);
x_115 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec_ref(x_115);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_add(x_88, x_171);
lean_dec(x_88);
lean_ctor_set(x_7, 3, x_172);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_444; 
lean_dec_ref(x_67);
x_173 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_174);
lean_inc_ref(x_173);
x_411 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_100, x_173, x_3, x_5, x_6, x_7, x_8, x_116);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec_ref(x_411);
x_444 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2069_(x_173, x_412);
lean_dec_ref(x_173);
if (x_444 == 0)
{
goto block_443;
}
else
{
if (x_100 == 0)
{
x_414 = x_2;
x_415 = x_3;
x_416 = x_4;
x_417 = x_5;
x_418 = x_6;
x_419 = x_7;
x_420 = x_8;
x_421 = x_413;
goto block_440;
}
else
{
goto block_443;
}
}
block_198:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_180);
lean_ctor_set(x_192, 2, x_181);
lean_ctor_set(x_192, 3, x_182);
lean_ctor_set(x_192, 4, x_184);
lean_ctor_set(x_192, 5, x_185);
lean_ctor_set(x_192, 6, x_186);
lean_ctor_set_uint8(x_192, sizeof(void*)*7, x_183);
x_193 = lean_st_ref_set(x_178, x_192, x_189);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_179, x_178, x_175, x_194);
lean_dec_ref(x_179);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec_ref(x_195);
x_1 = x_174;
x_2 = x_188;
x_3 = x_178;
x_4 = x_190;
x_5 = x_187;
x_6 = x_175;
x_7 = x_177;
x_8 = x_176;
x_9 = x_196;
goto _start;
}
block_395:
{
if (x_208 == 0)
{
lean_object* x_209; 
lean_inc(x_201);
lean_inc_ref(x_203);
lean_inc(x_199);
lean_inc_ref(x_206);
lean_inc_ref(x_204);
x_209 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_204, x_206, x_199, x_203, x_201, x_200);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec_ref(x_209);
lean_inc(x_201);
lean_inc_ref(x_203);
lean_inc(x_199);
lean_inc_ref(x_206);
lean_inc_ref(x_204);
x_212 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_204, x_205, x_202, x_206, x_199, x_203, x_201, x_211);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec_ref(x_212);
x_215 = lean_ctor_get(x_204, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_204, 3);
lean_inc(x_216);
lean_inc(x_216);
x_217 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_216, x_214);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec_ref(x_217);
lean_inc(x_201);
lean_inc_ref(x_203);
lean_inc(x_199);
lean_inc_ref(x_206);
lean_inc_ref(x_207);
lean_inc(x_202);
lean_inc_ref(x_205);
lean_inc_ref(x_174);
lean_inc_ref(x_204);
x_220 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_204, x_174, x_205, x_202, x_207, x_206, x_199, x_203, x_201, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec_ref(x_220);
lean_inc(x_201);
lean_inc_ref(x_203);
lean_inc(x_199);
lean_inc_ref(x_206);
lean_inc_ref(x_207);
lean_inc(x_202);
lean_inc_ref(x_205);
x_223 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_216, x_205, x_202, x_207, x_206, x_199, x_203, x_201, x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec_ref(x_223);
lean_inc(x_201);
lean_inc_ref(x_203);
lean_inc(x_199);
lean_inc_ref(x_206);
lean_inc_ref(x_207);
lean_inc(x_202);
lean_inc_ref(x_205);
x_226 = l_Lean_Compiler_LCNF_Simp_simp(x_174, x_205, x_202, x_207, x_206, x_199, x_203, x_201, x_225);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec_ref(x_226);
x_229 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_215, x_202, x_228);
lean_dec(x_215);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_unbox(x_230);
lean_dec(x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; 
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_203);
lean_dec(x_201);
lean_dec_ref(x_1);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec_ref(x_229);
x_233 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_204, x_202, x_199, x_232);
lean_dec(x_199);
lean_dec(x_202);
lean_dec_ref(x_204);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_233, 0);
lean_dec(x_235);
lean_ctor_set(x_233, 0, x_227);
return x_233;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_227);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_229, 1);
lean_inc(x_238);
lean_dec_ref(x_229);
lean_inc_ref(x_204);
x_239 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_204, x_205, x_202, x_207, x_206, x_199, x_203, x_201, x_238);
lean_dec(x_201);
lean_dec_ref(x_203);
lean_dec(x_199);
lean_dec_ref(x_206);
lean_dec_ref(x_207);
lean_dec(x_202);
lean_dec_ref(x_205);
x_240 = !lean_is_exclusive(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_239, 0);
lean_dec(x_241);
x_242 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_204, x_227);
lean_dec_ref(x_1);
lean_ctor_set(x_239, 0, x_242);
return x_239;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_239, 1);
lean_inc(x_243);
lean_dec(x_239);
x_244 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_204, x_227);
lean_dec_ref(x_1);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
else
{
lean_dec(x_215);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_1);
return x_226;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec_ref(x_1);
x_246 = lean_ctor_get(x_224, 0);
lean_inc(x_246);
lean_dec_ref(x_224);
x_247 = lean_ctor_get(x_223, 1);
lean_inc(x_247);
lean_dec_ref(x_223);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_250 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_215, x_249, x_202, x_199, x_203, x_201, x_247);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec_ref(x_250);
x_252 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_204, x_202, x_199, x_251);
lean_dec_ref(x_204);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec_ref(x_252);
lean_inc(x_201);
lean_inc_ref(x_203);
lean_inc(x_199);
lean_inc_ref(x_206);
lean_inc_ref(x_207);
lean_inc(x_202);
lean_inc_ref(x_205);
x_254 = l_Lean_Compiler_LCNF_Simp_simp(x_174, x_205, x_202, x_207, x_206, x_199, x_203, x_201, x_253);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec_ref(x_254);
x_257 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_248, x_255, x_205, x_202, x_207, x_206, x_199, x_203, x_201, x_256);
lean_dec(x_201);
lean_dec_ref(x_203);
lean_dec(x_199);
lean_dec_ref(x_206);
lean_dec_ref(x_207);
lean_dec(x_202);
lean_dec_ref(x_205);
lean_dec(x_248);
return x_257;
}
else
{
lean_dec(x_248);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
return x_254;
}
}
else
{
uint8_t x_258; 
lean_dec(x_248);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_174);
x_258 = !lean_is_exclusive(x_250);
if (x_258 == 0)
{
return x_250;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_250, 0);
x_260 = lean_ctor_get(x_250, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_250);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_215);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_174);
lean_dec_ref(x_1);
x_262 = !lean_is_exclusive(x_223);
if (x_262 == 0)
{
return x_223;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_223, 0);
x_264 = lean_ctor_get(x_223, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_223);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
lean_dec(x_216);
lean_dec(x_215);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_203);
lean_dec(x_201);
lean_dec_ref(x_174);
lean_dec_ref(x_1);
x_266 = lean_ctor_get(x_220, 1);
lean_inc(x_266);
lean_dec_ref(x_220);
x_267 = lean_ctor_get(x_221, 0);
lean_inc(x_267);
lean_dec_ref(x_221);
x_268 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_204, x_202, x_199, x_266);
lean_dec(x_199);
lean_dec(x_202);
lean_dec_ref(x_204);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_268, 0);
lean_dec(x_270);
lean_ctor_set(x_268, 0, x_267);
return x_268;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec(x_268);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_267);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
uint8_t x_273; 
lean_dec(x_216);
lean_dec(x_215);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_174);
lean_dec_ref(x_1);
x_273 = !lean_is_exclusive(x_220);
if (x_273 == 0)
{
return x_220;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_220, 0);
x_275 = lean_ctor_get(x_220, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_220);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_216);
lean_dec_ref(x_1);
x_277 = lean_ctor_get(x_217, 1);
lean_inc(x_277);
lean_dec_ref(x_217);
x_278 = lean_ctor_get(x_218, 0);
lean_inc(x_278);
lean_dec_ref(x_218);
x_279 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_215, x_278, x_202, x_199, x_203, x_201, x_277);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec_ref(x_279);
x_281 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_204, x_202, x_199, x_280);
lean_dec_ref(x_204);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec_ref(x_281);
x_1 = x_174;
x_2 = x_205;
x_3 = x_202;
x_4 = x_207;
x_5 = x_206;
x_6 = x_199;
x_7 = x_203;
x_8 = x_201;
x_9 = x_282;
goto _start;
}
else
{
uint8_t x_284; 
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_174);
x_284 = !lean_is_exclusive(x_279);
if (x_284 == 0)
{
return x_279;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_279, 0);
x_286 = lean_ctor_get(x_279, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_279);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
}
else
{
uint8_t x_288; 
lean_dec_ref(x_204);
x_288 = !lean_is_exclusive(x_1);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_1, 1);
lean_dec(x_289);
x_290 = lean_ctor_get(x_1, 0);
lean_dec(x_290);
x_291 = lean_ctor_get(x_212, 1);
lean_inc(x_291);
lean_dec_ref(x_212);
x_292 = lean_ctor_get(x_213, 0);
lean_inc(x_292);
lean_dec_ref(x_213);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_292);
x_2 = x_205;
x_3 = x_202;
x_4 = x_207;
x_5 = x_206;
x_6 = x_199;
x_7 = x_203;
x_8 = x_201;
x_9 = x_291;
goto _start;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_1);
x_294 = lean_ctor_get(x_212, 1);
lean_inc(x_294);
lean_dec_ref(x_212);
x_295 = lean_ctor_get(x_213, 0);
lean_inc(x_295);
lean_dec_ref(x_213);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_174);
x_1 = x_296;
x_2 = x_205;
x_3 = x_202;
x_4 = x_207;
x_5 = x_206;
x_6 = x_199;
x_7 = x_203;
x_8 = x_201;
x_9 = x_294;
goto _start;
}
}
}
else
{
uint8_t x_298; 
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_174);
lean_dec_ref(x_1);
x_298 = !lean_is_exclusive(x_212);
if (x_298 == 0)
{
return x_212;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_212, 0);
x_300 = lean_ctor_get(x_212, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_212);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec_ref(x_204);
lean_dec_ref(x_1);
x_302 = lean_ctor_get(x_209, 1);
lean_inc(x_302);
lean_dec_ref(x_209);
x_303 = lean_ctor_get(x_210, 0);
lean_inc(x_303);
lean_dec_ref(x_210);
x_304 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_202, x_302);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec_ref(x_304);
lean_inc(x_201);
lean_inc_ref(x_203);
lean_inc(x_199);
lean_inc_ref(x_206);
lean_inc_ref(x_207);
lean_inc(x_202);
lean_inc_ref(x_205);
x_306 = l_Lean_Compiler_LCNF_Simp_simp(x_174, x_205, x_202, x_207, x_206, x_199, x_203, x_201, x_305);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec_ref(x_306);
x_309 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_303, x_307, x_205, x_202, x_207, x_206, x_199, x_203, x_201, x_308);
lean_dec(x_201);
lean_dec_ref(x_203);
lean_dec(x_199);
lean_dec_ref(x_206);
lean_dec_ref(x_207);
lean_dec(x_202);
lean_dec_ref(x_205);
lean_dec(x_303);
return x_309;
}
else
{
lean_dec(x_303);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
return x_306;
}
}
}
else
{
uint8_t x_310; 
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_174);
lean_dec_ref(x_1);
x_310 = !lean_is_exclusive(x_209);
if (x_310 == 0)
{
return x_209;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_209, 0);
x_312 = lean_ctor_get(x_209, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_209);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
lean_dec_ref(x_1);
x_314 = lean_st_ref_take(x_202, x_200);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_315, 0);
lean_inc_ref(x_316);
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec_ref(x_314);
x_318 = lean_ctor_get(x_315, 1);
lean_inc_ref(x_318);
x_319 = lean_ctor_get(x_315, 2);
lean_inc(x_319);
x_320 = lean_ctor_get(x_315, 3);
lean_inc_ref(x_320);
x_321 = lean_ctor_get_uint8(x_315, sizeof(void*)*7);
x_322 = lean_ctor_get(x_315, 4);
lean_inc(x_322);
x_323 = lean_ctor_get(x_315, 5);
lean_inc(x_323);
x_324 = lean_ctor_get(x_315, 6);
lean_inc(x_324);
lean_dec(x_315);
x_325 = !lean_is_exclusive(x_316);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint64_t x_331; uint64_t x_332; uint64_t x_333; uint64_t x_334; uint64_t x_335; uint64_t x_336; uint64_t x_337; size_t x_338; size_t x_339; size_t x_340; size_t x_341; size_t x_342; lean_object* x_343; uint8_t x_344; 
x_326 = lean_ctor_get(x_316, 0);
x_327 = lean_ctor_get(x_316, 1);
x_328 = lean_ctor_get(x_204, 0);
lean_inc(x_328);
x_329 = lean_box(0);
x_330 = lean_array_get_size(x_327);
x_331 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_328);
x_332 = 32;
x_333 = lean_uint64_shift_right(x_331, x_332);
x_334 = lean_uint64_xor(x_331, x_333);
x_335 = 16;
x_336 = lean_uint64_shift_right(x_334, x_335);
x_337 = lean_uint64_xor(x_334, x_336);
x_338 = lean_uint64_to_usize(x_337);
x_339 = lean_usize_of_nat(x_330);
lean_dec(x_330);
x_340 = 1;
x_341 = lean_usize_sub(x_339, x_340);
x_342 = lean_usize_land(x_338, x_341);
x_343 = lean_array_uget(x_327, x_342);
x_344 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_328, x_343);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_345 = lean_nat_add(x_326, x_171);
lean_dec(x_326);
x_346 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_346, 0, x_328);
lean_ctor_set(x_346, 1, x_329);
lean_ctor_set(x_346, 2, x_343);
x_347 = lean_array_uset(x_327, x_342, x_346);
x_348 = lean_unsigned_to_nat(4u);
x_349 = lean_nat_mul(x_345, x_348);
x_350 = lean_unsigned_to_nat(3u);
x_351 = lean_nat_div(x_349, x_350);
lean_dec(x_349);
x_352 = lean_array_get_size(x_347);
x_353 = lean_nat_dec_le(x_351, x_352);
lean_dec(x_352);
lean_dec(x_351);
if (x_353 == 0)
{
lean_object* x_354; 
x_354 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_347);
lean_ctor_set(x_316, 1, x_354);
lean_ctor_set(x_316, 0, x_345);
x_175 = x_199;
x_176 = x_201;
x_177 = x_203;
x_178 = x_202;
x_179 = x_204;
x_180 = x_318;
x_181 = x_319;
x_182 = x_320;
x_183 = x_321;
x_184 = x_322;
x_185 = x_323;
x_186 = x_324;
x_187 = x_206;
x_188 = x_205;
x_189 = x_317;
x_190 = x_207;
x_191 = x_316;
goto block_198;
}
else
{
lean_ctor_set(x_316, 1, x_347);
lean_ctor_set(x_316, 0, x_345);
x_175 = x_199;
x_176 = x_201;
x_177 = x_203;
x_178 = x_202;
x_179 = x_204;
x_180 = x_318;
x_181 = x_319;
x_182 = x_320;
x_183 = x_321;
x_184 = x_322;
x_185 = x_323;
x_186 = x_324;
x_187 = x_206;
x_188 = x_205;
x_189 = x_317;
x_190 = x_207;
x_191 = x_316;
goto block_198;
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = lean_box(0);
x_356 = lean_array_uset(x_327, x_342, x_355);
x_357 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_328, x_329, x_343);
x_358 = lean_array_uset(x_356, x_342, x_357);
lean_ctor_set(x_316, 1, x_358);
x_175 = x_199;
x_176 = x_201;
x_177 = x_203;
x_178 = x_202;
x_179 = x_204;
x_180 = x_318;
x_181 = x_319;
x_182 = x_320;
x_183 = x_321;
x_184 = x_322;
x_185 = x_323;
x_186 = x_324;
x_187 = x_206;
x_188 = x_205;
x_189 = x_317;
x_190 = x_207;
x_191 = x_316;
goto block_198;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint64_t x_364; uint64_t x_365; uint64_t x_366; uint64_t x_367; uint64_t x_368; uint64_t x_369; uint64_t x_370; size_t x_371; size_t x_372; size_t x_373; size_t x_374; size_t x_375; lean_object* x_376; uint8_t x_377; 
x_359 = lean_ctor_get(x_316, 0);
x_360 = lean_ctor_get(x_316, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_316);
x_361 = lean_ctor_get(x_204, 0);
lean_inc(x_361);
x_362 = lean_box(0);
x_363 = lean_array_get_size(x_360);
x_364 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_361);
x_365 = 32;
x_366 = lean_uint64_shift_right(x_364, x_365);
x_367 = lean_uint64_xor(x_364, x_366);
x_368 = 16;
x_369 = lean_uint64_shift_right(x_367, x_368);
x_370 = lean_uint64_xor(x_367, x_369);
x_371 = lean_uint64_to_usize(x_370);
x_372 = lean_usize_of_nat(x_363);
lean_dec(x_363);
x_373 = 1;
x_374 = lean_usize_sub(x_372, x_373);
x_375 = lean_usize_land(x_371, x_374);
x_376 = lean_array_uget(x_360, x_375);
x_377 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_361, x_376);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; 
x_378 = lean_nat_add(x_359, x_171);
lean_dec(x_359);
x_379 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_379, 0, x_361);
lean_ctor_set(x_379, 1, x_362);
lean_ctor_set(x_379, 2, x_376);
x_380 = lean_array_uset(x_360, x_375, x_379);
x_381 = lean_unsigned_to_nat(4u);
x_382 = lean_nat_mul(x_378, x_381);
x_383 = lean_unsigned_to_nat(3u);
x_384 = lean_nat_div(x_382, x_383);
lean_dec(x_382);
x_385 = lean_array_get_size(x_380);
x_386 = lean_nat_dec_le(x_384, x_385);
lean_dec(x_385);
lean_dec(x_384);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; 
x_387 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_380);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_378);
lean_ctor_set(x_388, 1, x_387);
x_175 = x_199;
x_176 = x_201;
x_177 = x_203;
x_178 = x_202;
x_179 = x_204;
x_180 = x_318;
x_181 = x_319;
x_182 = x_320;
x_183 = x_321;
x_184 = x_322;
x_185 = x_323;
x_186 = x_324;
x_187 = x_206;
x_188 = x_205;
x_189 = x_317;
x_190 = x_207;
x_191 = x_388;
goto block_198;
}
else
{
lean_object* x_389; 
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_378);
lean_ctor_set(x_389, 1, x_380);
x_175 = x_199;
x_176 = x_201;
x_177 = x_203;
x_178 = x_202;
x_179 = x_204;
x_180 = x_318;
x_181 = x_319;
x_182 = x_320;
x_183 = x_321;
x_184 = x_322;
x_185 = x_323;
x_186 = x_324;
x_187 = x_206;
x_188 = x_205;
x_189 = x_317;
x_190 = x_207;
x_191 = x_389;
goto block_198;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_390 = lean_box(0);
x_391 = lean_array_uset(x_360, x_375, x_390);
x_392 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_361, x_362, x_376);
x_393 = lean_array_uset(x_391, x_375, x_392);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_359);
lean_ctor_set(x_394, 1, x_393);
x_175 = x_199;
x_176 = x_201;
x_177 = x_203;
x_178 = x_202;
x_179 = x_204;
x_180 = x_318;
x_181 = x_319;
x_182 = x_320;
x_183 = x_321;
x_184 = x_322;
x_185 = x_323;
x_186 = x_324;
x_187 = x_206;
x_188 = x_205;
x_189 = x_317;
x_190 = x_207;
x_191 = x_394;
goto block_198;
}
}
}
}
block_410:
{
uint8_t x_407; 
x_407 = l_Lean_Expr_isErased(x_397);
lean_dec_ref(x_397);
if (x_407 == 0)
{
lean_dec(x_398);
x_199 = x_403;
x_200 = x_406;
x_201 = x_405;
x_202 = x_400;
x_203 = x_404;
x_204 = x_396;
x_205 = x_399;
x_206 = x_402;
x_207 = x_401;
x_208 = x_100;
goto block_395;
}
else
{
lean_object* x_408; uint8_t x_409; 
x_408 = lean_box(1);
x_409 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1209_(x_398, x_408);
lean_dec(x_398);
if (x_409 == 0)
{
x_199 = x_403;
x_200 = x_406;
x_201 = x_405;
x_202 = x_400;
x_203 = x_404;
x_204 = x_396;
x_205 = x_399;
x_206 = x_402;
x_207 = x_401;
x_208 = x_407;
goto block_395;
}
else
{
x_199 = x_403;
x_200 = x_406;
x_201 = x_405;
x_202 = x_400;
x_203 = x_404;
x_204 = x_396;
x_205 = x_399;
x_206 = x_402;
x_207 = x_401;
x_208 = x_100;
goto block_395;
}
}
}
block_440:
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_412, 2);
lean_inc_ref(x_422);
x_423 = lean_ctor_get(x_412, 3);
lean_inc(x_423);
lean_inc(x_420);
lean_inc_ref(x_419);
lean_inc(x_418);
lean_inc_ref(x_417);
lean_inc_ref(x_416);
lean_inc(x_423);
x_424 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_423, x_414, x_416, x_417, x_418, x_419, x_420, x_421);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec_ref(x_424);
x_396 = x_412;
x_397 = x_422;
x_398 = x_423;
x_399 = x_414;
x_400 = x_415;
x_401 = x_416;
x_402 = x_417;
x_403 = x_418;
x_404 = x_419;
x_405 = x_420;
x_406 = x_426;
goto block_410;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_423);
lean_dec_ref(x_422);
x_427 = lean_ctor_get(x_424, 1);
lean_inc(x_427);
lean_dec_ref(x_424);
x_428 = lean_ctor_get(x_425, 0);
lean_inc(x_428);
lean_dec_ref(x_425);
x_429 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_415, x_427);
x_430 = lean_ctor_get(x_429, 1);
lean_inc(x_430);
lean_dec_ref(x_429);
x_431 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_412, x_428, x_418, x_430);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec_ref(x_431);
x_434 = lean_ctor_get(x_432, 2);
lean_inc_ref(x_434);
x_435 = lean_ctor_get(x_432, 3);
lean_inc(x_435);
x_396 = x_432;
x_397 = x_434;
x_398 = x_435;
x_399 = x_414;
x_400 = x_415;
x_401 = x_416;
x_402 = x_417;
x_403 = x_418;
x_404 = x_419;
x_405 = x_420;
x_406 = x_433;
goto block_410;
}
}
else
{
uint8_t x_436; 
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec(x_420);
lean_dec_ref(x_419);
lean_dec(x_418);
lean_dec_ref(x_417);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_412);
lean_dec_ref(x_174);
lean_dec_ref(x_1);
x_436 = !lean_is_exclusive(x_424);
if (x_436 == 0)
{
return x_424;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_424, 0);
x_438 = lean_ctor_get(x_424, 1);
lean_inc(x_438);
lean_inc(x_437);
lean_dec(x_424);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
block_443:
{
lean_object* x_441; lean_object* x_442; 
x_441 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_413);
x_442 = lean_ctor_get(x_441, 1);
lean_inc(x_442);
lean_dec_ref(x_441);
x_414 = x_2;
x_415 = x_3;
x_416 = x_4;
x_417 = x_5;
x_418 = x_6;
x_419 = x_7;
x_420 = x_8;
x_421 = x_442;
goto block_440;
}
}
case 3:
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec_ref(x_67);
x_445 = lean_ctor_get(x_1, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_446);
x_447 = lean_st_ref_get(x_3, x_116);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec_ref(x_447);
x_450 = lean_ctor_get(x_448, 0);
lean_inc_ref(x_450);
lean_dec(x_448);
x_451 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_450, x_445, x_100);
lean_dec_ref(x_450);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_461; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
lean_dec_ref(x_451);
x_453 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_100, x_446, x_3, x_449);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_456 = x_453;
} else {
 lean_dec_ref(x_453);
 x_456 = lean_box(0);
}
lean_inc(x_454);
x_461 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_452, x_454, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_455);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; uint8_t x_468; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec_ref(x_461);
lean_inc(x_452);
x_464 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_452, x_3, x_463);
x_465 = lean_ctor_get(x_464, 1);
lean_inc(x_465);
lean_dec_ref(x_464);
x_466 = lean_unsigned_to_nat(0u);
x_467 = lean_array_get_size(x_454);
x_468 = lean_nat_dec_lt(x_466, x_467);
if (x_468 == 0)
{
lean_dec(x_467);
lean_dec(x_3);
x_457 = x_465;
goto block_460;
}
else
{
uint8_t x_469; 
x_469 = lean_nat_dec_le(x_467, x_467);
if (x_469 == 0)
{
lean_dec(x_467);
lean_dec(x_3);
x_457 = x_465;
goto block_460;
}
else
{
lean_object* x_470; size_t x_471; size_t x_472; lean_object* x_473; lean_object* x_474; 
x_470 = lean_box(0);
x_471 = 0;
x_472 = lean_usize_of_nat(x_467);
lean_dec(x_467);
x_473 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_454, x_471, x_472, x_470, x_3, x_465);
lean_dec(x_3);
x_474 = lean_ctor_get(x_473, 1);
lean_inc(x_474);
lean_dec_ref(x_473);
x_457 = x_474;
goto block_460;
}
}
}
else
{
lean_object* x_475; lean_object* x_476; 
lean_dec(x_456);
lean_dec(x_454);
lean_dec(x_452);
lean_dec_ref(x_1);
x_475 = lean_ctor_get(x_461, 1);
lean_inc(x_475);
lean_dec_ref(x_461);
x_476 = lean_ctor_get(x_462, 0);
lean_inc(x_476);
lean_dec_ref(x_462);
x_1 = x_476;
x_9 = x_475;
goto _start;
}
}
else
{
uint8_t x_478; 
lean_dec(x_456);
lean_dec(x_454);
lean_dec(x_452);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_478 = !lean_is_exclusive(x_461);
if (x_478 == 0)
{
return x_461;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_461, 0);
x_480 = lean_ctor_get(x_461, 1);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_461);
x_481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
return x_481;
}
}
block_460:
{
lean_object* x_458; lean_object* x_459; 
x_458 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_1, x_452, x_454);
lean_dec_ref(x_1);
if (lean_is_scalar(x_456)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_456;
}
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_457);
return x_459;
}
}
else
{
lean_object* x_482; 
lean_dec_ref(x_446);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_482 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_449);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_482;
}
}
case 4:
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_483);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_483);
x_484 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_483, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_116);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec_ref(x_484);
x_487 = lean_st_ref_get(x_3, x_486);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_487, 1);
lean_inc(x_489);
lean_dec_ref(x_487);
x_490 = lean_ctor_get(x_483, 1);
lean_inc_ref(x_490);
x_491 = lean_ctor_get(x_483, 2);
lean_inc(x_491);
x_492 = lean_ctor_get(x_483, 3);
lean_inc_ref(x_492);
lean_dec_ref(x_483);
x_493 = lean_ctor_get(x_488, 0);
lean_inc_ref(x_493);
lean_dec(x_488);
x_494 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_493, x_491, x_100);
lean_dec_ref(x_493);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
lean_dec_ref(x_494);
x_496 = lean_st_ref_get(x_3, x_489);
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec_ref(x_496);
x_499 = lean_box(x_100);
lean_inc(x_495);
x_500 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__1___boxed), 11, 2);
lean_closure_set(x_500, 0, x_495);
lean_closure_set(x_500, 1, x_499);
x_501 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_67, x_492, x_500);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_502 = lean_apply_8(x_501, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_498);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec_ref(x_502);
lean_inc(x_6);
lean_inc(x_3);
x_505 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_503, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_504);
if (lean_obj_tag(x_505) == 0)
{
uint8_t x_506; 
x_506 = !lean_is_exclusive(x_505);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_521; uint8_t x_522; 
x_507 = lean_ctor_get(x_505, 0);
x_508 = lean_ctor_get(x_505, 1);
x_509 = lean_ctor_get(x_497, 0);
lean_inc_ref(x_509);
lean_dec(x_497);
x_510 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_509, x_100, x_490);
lean_dec_ref(x_509);
x_521 = lean_array_get_size(x_507);
x_522 = lean_nat_dec_eq(x_521, x_171);
lean_dec(x_521);
if (x_522 == 0)
{
lean_free_object(x_505);
lean_dec(x_6);
x_511 = x_3;
x_512 = x_508;
goto block_520;
}
else
{
lean_object* x_523; lean_object* x_524; 
x_523 = lean_unsigned_to_nat(0u);
x_524 = lean_array_fget(x_507, x_523);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_534; lean_object* x_535; uint8_t x_544; lean_object* x_545; uint8_t x_547; 
lean_free_object(x_505);
x_525 = lean_ctor_get(x_524, 1);
lean_inc_ref(x_525);
x_526 = lean_ctor_get(x_524, 2);
lean_inc_ref(x_526);
lean_dec_ref(x_524);
x_534 = lean_array_get_size(x_525);
x_547 = lean_nat_dec_lt(x_523, x_534);
if (x_547 == 0)
{
x_544 = x_100;
x_545 = x_508;
goto block_546;
}
else
{
if (x_547 == 0)
{
x_544 = x_100;
x_545 = x_508;
goto block_546;
}
else
{
size_t x_548; size_t x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; 
x_548 = 0;
x_549 = lean_usize_of_nat(x_534);
x_550 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_525, x_548, x_549, x_3, x_508);
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
lean_dec_ref(x_550);
x_553 = lean_unbox(x_551);
lean_dec(x_551);
x_544 = x_553;
x_545 = x_552;
goto block_546;
}
}
block_533:
{
lean_object* x_528; uint8_t x_529; 
x_528 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_527);
lean_dec(x_3);
x_529 = !lean_is_exclusive(x_528);
if (x_529 == 0)
{
lean_object* x_530; 
x_530 = lean_ctor_get(x_528, 0);
lean_dec(x_530);
lean_ctor_set(x_528, 0, x_526);
return x_528;
}
else
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_ctor_get(x_528, 1);
lean_inc(x_531);
lean_dec(x_528);
x_532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_532, 0, x_526);
lean_ctor_set(x_532, 1, x_531);
return x_532;
}
}
block_543:
{
uint8_t x_536; 
x_536 = lean_nat_dec_lt(x_523, x_534);
if (x_536 == 0)
{
lean_dec(x_534);
lean_dec_ref(x_525);
lean_dec(x_6);
x_527 = x_535;
goto block_533;
}
else
{
uint8_t x_537; 
x_537 = lean_nat_dec_le(x_534, x_534);
if (x_537 == 0)
{
lean_dec(x_534);
lean_dec_ref(x_525);
lean_dec(x_6);
x_527 = x_535;
goto block_533;
}
else
{
lean_object* x_538; size_t x_539; size_t x_540; lean_object* x_541; lean_object* x_542; 
x_538 = lean_box(0);
x_539 = 0;
x_540 = lean_usize_of_nat(x_534);
lean_dec(x_534);
x_541 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_525, x_539, x_540, x_538, x_6, x_535);
lean_dec(x_6);
lean_dec_ref(x_525);
x_542 = lean_ctor_get(x_541, 1);
lean_inc(x_542);
lean_dec_ref(x_541);
x_527 = x_542;
goto block_533;
}
}
}
block_546:
{
if (x_544 == 0)
{
lean_dec_ref(x_510);
lean_dec(x_507);
lean_dec(x_495);
lean_dec_ref(x_1);
x_535 = x_545;
goto block_543;
}
else
{
if (x_100 == 0)
{
lean_dec(x_534);
lean_dec_ref(x_526);
lean_dec_ref(x_525);
lean_dec(x_6);
x_511 = x_3;
x_512 = x_545;
goto block_520;
}
else
{
lean_dec_ref(x_510);
lean_dec(x_507);
lean_dec(x_495);
lean_dec_ref(x_1);
x_535 = x_545;
goto block_543;
}
}
}
}
else
{
lean_object* x_554; 
lean_dec_ref(x_510);
lean_dec(x_507);
lean_dec(x_495);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_554 = lean_ctor_get(x_524, 0);
lean_inc_ref(x_554);
lean_dec_ref(x_524);
lean_ctor_set(x_505, 0, x_554);
return x_505;
}
}
block_520:
{
lean_object* x_513; uint8_t x_514; 
lean_inc(x_495);
x_513 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_495, x_511, x_512);
lean_dec(x_511);
x_514 = !lean_is_exclusive(x_513);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_ctor_get(x_513, 0);
lean_dec(x_515);
x_516 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_1, x_510, x_495, x_507);
lean_ctor_set(x_513, 0, x_516);
return x_513;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_513, 1);
lean_inc(x_517);
lean_dec(x_513);
x_518 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_1, x_510, x_495, x_507);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_517);
return x_519;
}
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_567; uint8_t x_568; 
x_555 = lean_ctor_get(x_505, 0);
x_556 = lean_ctor_get(x_505, 1);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_505);
x_557 = lean_ctor_get(x_497, 0);
lean_inc_ref(x_557);
lean_dec(x_497);
x_558 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_557, x_100, x_490);
lean_dec_ref(x_557);
x_567 = lean_array_get_size(x_555);
x_568 = lean_nat_dec_eq(x_567, x_171);
lean_dec(x_567);
if (x_568 == 0)
{
lean_dec(x_6);
x_559 = x_3;
x_560 = x_556;
goto block_566;
}
else
{
lean_object* x_569; lean_object* x_570; 
x_569 = lean_unsigned_to_nat(0u);
x_570 = lean_array_fget(x_555, x_569);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_579; lean_object* x_580; uint8_t x_589; lean_object* x_590; uint8_t x_592; 
x_571 = lean_ctor_get(x_570, 1);
lean_inc_ref(x_571);
x_572 = lean_ctor_get(x_570, 2);
lean_inc_ref(x_572);
lean_dec_ref(x_570);
x_579 = lean_array_get_size(x_571);
x_592 = lean_nat_dec_lt(x_569, x_579);
if (x_592 == 0)
{
x_589 = x_100;
x_590 = x_556;
goto block_591;
}
else
{
if (x_592 == 0)
{
x_589 = x_100;
x_590 = x_556;
goto block_591;
}
else
{
size_t x_593; size_t x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; 
x_593 = 0;
x_594 = lean_usize_of_nat(x_579);
x_595 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_571, x_593, x_594, x_3, x_556);
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec_ref(x_595);
x_598 = lean_unbox(x_596);
lean_dec(x_596);
x_589 = x_598;
x_590 = x_597;
goto block_591;
}
}
block_578:
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_574 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_573);
lean_dec(x_3);
x_575 = lean_ctor_get(x_574, 1);
lean_inc(x_575);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_576 = x_574;
} else {
 lean_dec_ref(x_574);
 x_576 = lean_box(0);
}
if (lean_is_scalar(x_576)) {
 x_577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_577 = x_576;
}
lean_ctor_set(x_577, 0, x_572);
lean_ctor_set(x_577, 1, x_575);
return x_577;
}
block_588:
{
uint8_t x_581; 
x_581 = lean_nat_dec_lt(x_569, x_579);
if (x_581 == 0)
{
lean_dec(x_579);
lean_dec_ref(x_571);
lean_dec(x_6);
x_573 = x_580;
goto block_578;
}
else
{
uint8_t x_582; 
x_582 = lean_nat_dec_le(x_579, x_579);
if (x_582 == 0)
{
lean_dec(x_579);
lean_dec_ref(x_571);
lean_dec(x_6);
x_573 = x_580;
goto block_578;
}
else
{
lean_object* x_583; size_t x_584; size_t x_585; lean_object* x_586; lean_object* x_587; 
x_583 = lean_box(0);
x_584 = 0;
x_585 = lean_usize_of_nat(x_579);
lean_dec(x_579);
x_586 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_571, x_584, x_585, x_583, x_6, x_580);
lean_dec(x_6);
lean_dec_ref(x_571);
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
lean_dec_ref(x_586);
x_573 = x_587;
goto block_578;
}
}
}
block_591:
{
if (x_589 == 0)
{
lean_dec_ref(x_558);
lean_dec(x_555);
lean_dec(x_495);
lean_dec_ref(x_1);
x_580 = x_590;
goto block_588;
}
else
{
if (x_100 == 0)
{
lean_dec(x_579);
lean_dec_ref(x_572);
lean_dec_ref(x_571);
lean_dec(x_6);
x_559 = x_3;
x_560 = x_590;
goto block_566;
}
else
{
lean_dec_ref(x_558);
lean_dec(x_555);
lean_dec(x_495);
lean_dec_ref(x_1);
x_580 = x_590;
goto block_588;
}
}
}
}
else
{
lean_object* x_599; lean_object* x_600; 
lean_dec_ref(x_558);
lean_dec(x_555);
lean_dec(x_495);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_599 = lean_ctor_get(x_570, 0);
lean_inc_ref(x_599);
lean_dec_ref(x_570);
x_600 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_556);
return x_600;
}
}
block_566:
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_inc(x_495);
x_561 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_495, x_559, x_560);
lean_dec(x_559);
x_562 = lean_ctor_get(x_561, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 x_563 = x_561;
} else {
 lean_dec_ref(x_561);
 x_563 = lean_box(0);
}
x_564 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_1, x_558, x_495, x_555);
if (lean_is_scalar(x_563)) {
 x_565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_565 = x_563;
}
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_562);
return x_565;
}
}
}
else
{
uint8_t x_601; 
lean_dec(x_497);
lean_dec(x_495);
lean_dec_ref(x_490);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_601 = !lean_is_exclusive(x_505);
if (x_601 == 0)
{
return x_505;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_505, 0);
x_603 = lean_ctor_get(x_505, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_505);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
else
{
uint8_t x_605; 
lean_dec(x_497);
lean_dec(x_495);
lean_dec_ref(x_490);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_605 = !lean_is_exclusive(x_502);
if (x_605 == 0)
{
return x_502;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_502, 0);
x_607 = lean_ctor_get(x_502, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_502);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_606);
lean_ctor_set(x_608, 1, x_607);
return x_608;
}
}
}
else
{
lean_object* x_609; 
lean_dec_ref(x_492);
lean_dec_ref(x_490);
lean_dec_ref(x_67);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_609 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_489);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_609;
}
}
else
{
uint8_t x_610; 
lean_dec_ref(x_483);
lean_dec_ref(x_7);
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_610 = !lean_is_exclusive(x_484);
if (x_610 == 0)
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_ctor_get(x_484, 0);
lean_dec(x_611);
x_612 = lean_ctor_get(x_485, 0);
lean_inc(x_612);
lean_dec_ref(x_485);
lean_ctor_set(x_484, 0, x_612);
return x_484;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_484, 1);
lean_inc(x_613);
lean_dec(x_484);
x_614 = lean_ctor_get(x_485, 0);
lean_inc(x_614);
lean_dec_ref(x_485);
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_614);
lean_ctor_set(x_615, 1, x_613);
return x_615;
}
}
}
else
{
uint8_t x_616; 
lean_dec_ref(x_483);
lean_dec_ref(x_7);
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_616 = !lean_is_exclusive(x_484);
if (x_616 == 0)
{
return x_484;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_617 = lean_ctor_get(x_484, 0);
x_618 = lean_ctor_get(x_484, 1);
lean_inc(x_618);
lean_inc(x_617);
lean_dec(x_484);
x_619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_619, 0, x_617);
lean_ctor_set(x_619, 1, x_618);
return x_619;
}
}
}
case 5:
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec_ref(x_67);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_620 = lean_ctor_get(x_1, 0);
lean_inc(x_620);
x_621 = lean_st_ref_get(x_3, x_116);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec_ref(x_621);
x_624 = lean_ctor_get(x_622, 0);
lean_inc_ref(x_624);
lean_dec(x_622);
x_625 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_624, x_620, x_100);
lean_dec_ref(x_624);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; uint8_t x_628; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
lean_dec_ref(x_625);
lean_inc(x_626);
x_627 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_626, x_3, x_623);
lean_dec(x_3);
x_628 = !lean_is_exclusive(x_627);
if (x_628 == 0)
{
lean_object* x_629; lean_object* x_630; 
x_629 = lean_ctor_get(x_627, 0);
lean_dec(x_629);
x_630 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_1, x_626);
lean_ctor_set(x_627, 0, x_630);
return x_627;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_631 = lean_ctor_get(x_627, 1);
lean_inc(x_631);
lean_dec(x_627);
x_632 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_1, x_626);
x_633 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_631);
return x_633;
}
}
else
{
lean_object* x_634; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_634 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_623);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_634;
}
}
case 6:
{
lean_object* x_635; lean_object* x_636; uint8_t x_637; 
lean_dec_ref(x_7);
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_635 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_635);
x_636 = lean_st_ref_get(x_3, x_116);
lean_dec(x_3);
x_637 = !lean_is_exclusive(x_636);
if (x_637 == 0)
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_638 = lean_ctor_get(x_636, 0);
x_639 = lean_ctor_get(x_638, 0);
lean_inc_ref(x_639);
lean_dec(x_638);
x_640 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_639, x_100, x_635);
lean_dec_ref(x_639);
x_641 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(x_1, x_640);
lean_ctor_set(x_636, 0, x_641);
return x_636;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_642 = lean_ctor_get(x_636, 0);
x_643 = lean_ctor_get(x_636, 1);
lean_inc(x_643);
lean_inc(x_642);
lean_dec(x_636);
x_644 = lean_ctor_get(x_642, 0);
lean_inc_ref(x_644);
lean_dec(x_642);
x_645 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_644, x_100, x_635);
lean_dec_ref(x_644);
x_646 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(x_1, x_645);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_643);
return x_647;
}
}
default: 
{
lean_object* x_648; lean_object* x_649; 
lean_dec_ref(x_67);
x_648 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_648);
x_649 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_649);
x_117 = x_648;
x_118 = x_649;
x_119 = x_2;
x_120 = x_3;
x_121 = x_4;
x_122 = x_5;
x_123 = x_6;
x_124 = x_7;
x_125 = x_8;
goto block_170;
}
}
block_170:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_126 = lean_ctor_get(x_117, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_117, 2);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_117, 3);
lean_inc_ref(x_128);
x_129 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_126, x_120, x_116);
lean_dec(x_126);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
lean_inc(x_130);
lean_inc_ref(x_1);
lean_inc_ref(x_118);
x_132 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_132, 0, x_118);
lean_closure_set(x_132, 1, x_1);
lean_closure_set(x_132, 2, x_130);
x_133 = lean_unbox(x_130);
if (x_133 == 0)
{
uint8_t x_134; 
lean_dec(x_130);
lean_dec_ref(x_118);
x_134 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_134 == 0)
{
lean_dec_ref(x_128);
lean_dec_ref(x_127);
x_10 = x_132;
x_11 = x_117;
x_12 = x_119;
x_13 = x_120;
x_14 = x_121;
x_15 = x_122;
x_16 = x_123;
x_17 = x_124;
x_18 = x_125;
x_19 = x_131;
goto block_29;
}
else
{
uint8_t x_135; 
x_135 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_128, x_127);
lean_dec_ref(x_127);
if (x_135 == 0)
{
x_10 = x_132;
x_11 = x_117;
x_12 = x_119;
x_13 = x_120;
x_14 = x_121;
x_15 = x_122;
x_16 = x_123;
x_17 = x_124;
x_18 = x_125;
x_19 = x_131;
goto block_29;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_st_ref_get(x_120, x_131);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec_ref(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc_ref(x_139);
lean_dec(x_137);
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc(x_123);
lean_inc_ref(x_122);
x_140 = l_Lean_Compiler_LCNF_normFunDeclImp(x_100, x_117, x_139, x_122, x_123, x_124, x_125, x_138);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec_ref(x_140);
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc(x_123);
lean_inc_ref(x_122);
x_143 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_141, x_122, x_123, x_124, x_125, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec_ref(x_143);
x_146 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_120, x_145);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec_ref(x_146);
x_10 = x_132;
x_11 = x_144;
x_12 = x_119;
x_13 = x_120;
x_14 = x_121;
x_15 = x_122;
x_16 = x_123;
x_17 = x_124;
x_18 = x_125;
x_19 = x_147;
goto block_29;
}
else
{
uint8_t x_148; 
lean_dec_ref(x_132);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
x_148 = !lean_is_exclusive(x_143);
if (x_148 == 0)
{
return x_143;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_143, 0);
x_150 = lean_ctor_get(x_143, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_143);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec_ref(x_132);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
x_152 = !lean_is_exclusive(x_140);
if (x_152 == 0)
{
return x_140;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_140, 0);
x_154 = lean_ctor_get(x_140, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_140);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec_ref(x_132);
lean_dec_ref(x_128);
lean_dec_ref(x_127);
x_156 = lean_st_ref_get(x_120, x_131);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec_ref(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc_ref(x_159);
lean_dec(x_157);
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc(x_123);
lean_inc_ref(x_122);
x_160 = l_Lean_Compiler_LCNF_normFunDeclImp(x_100, x_117, x_159, x_122, x_123, x_124, x_125, x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = lean_box(0);
x_164 = lean_unbox(x_130);
lean_dec(x_130);
x_165 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_118, x_1, x_164, x_161, x_163, x_119, x_120, x_121, x_122, x_123, x_124, x_125, x_162);
lean_dec_ref(x_1);
return x_165;
}
else
{
uint8_t x_166; 
lean_dec(x_130);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_1);
x_166 = !lean_is_exclusive(x_160);
if (x_166 == 0)
{
return x_160;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_160, 0);
x_168 = lean_ctor_get(x_160, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_160);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
lean_dec(x_7);
x_650 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
x_651 = lean_ctor_get(x_650, 1);
lean_inc(x_651);
lean_dec_ref(x_650);
x_706 = lean_unsigned_to_nat(1u);
x_707 = lean_nat_add(x_88, x_706);
lean_dec(x_88);
x_708 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_708, 0, x_85);
lean_ctor_set(x_708, 1, x_86);
lean_ctor_set(x_708, 2, x_87);
lean_ctor_set(x_708, 3, x_707);
lean_ctor_set(x_708, 4, x_89);
lean_ctor_set(x_708, 5, x_90);
lean_ctor_set(x_708, 6, x_91);
lean_ctor_set(x_708, 7, x_92);
lean_ctor_set(x_708, 8, x_93);
lean_ctor_set(x_708, 9, x_94);
lean_ctor_set(x_708, 10, x_95);
lean_ctor_set(x_708, 11, x_97);
lean_ctor_set(x_708, 12, x_99);
lean_ctor_set_uint8(x_708, sizeof(void*)*13, x_96);
lean_ctor_set_uint8(x_708, sizeof(void*)*13 + 1, x_98);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; uint8_t x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; uint8_t x_744; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; uint8_t x_938; 
lean_dec_ref(x_67);
x_709 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_709);
x_710 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_710);
lean_inc_ref(x_709);
x_905 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_100, x_709, x_3, x_5, x_6, x_708, x_8, x_651);
x_906 = lean_ctor_get(x_905, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_905, 1);
lean_inc(x_907);
lean_dec_ref(x_905);
x_938 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2069_(x_709, x_906);
lean_dec_ref(x_709);
if (x_938 == 0)
{
goto block_937;
}
else
{
if (x_100 == 0)
{
x_908 = x_2;
x_909 = x_3;
x_910 = x_4;
x_911 = x_5;
x_912 = x_6;
x_913 = x_708;
x_914 = x_8;
x_915 = x_907;
goto block_934;
}
else
{
goto block_937;
}
}
block_734:
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_728 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_728, 0, x_727);
lean_ctor_set(x_728, 1, x_716);
lean_ctor_set(x_728, 2, x_717);
lean_ctor_set(x_728, 3, x_718);
lean_ctor_set(x_728, 4, x_720);
lean_ctor_set(x_728, 5, x_721);
lean_ctor_set(x_728, 6, x_722);
lean_ctor_set_uint8(x_728, sizeof(void*)*7, x_719);
x_729 = lean_st_ref_set(x_714, x_728, x_725);
x_730 = lean_ctor_get(x_729, 1);
lean_inc(x_730);
lean_dec_ref(x_729);
x_731 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_715, x_714, x_711, x_730);
lean_dec_ref(x_715);
x_732 = lean_ctor_get(x_731, 1);
lean_inc(x_732);
lean_dec_ref(x_731);
x_1 = x_710;
x_2 = x_724;
x_3 = x_714;
x_4 = x_726;
x_5 = x_723;
x_6 = x_711;
x_7 = x_713;
x_8 = x_712;
x_9 = x_732;
goto _start;
}
block_889:
{
if (x_744 == 0)
{
lean_object* x_745; 
lean_inc(x_737);
lean_inc_ref(x_739);
lean_inc(x_735);
lean_inc_ref(x_742);
lean_inc_ref(x_740);
x_745 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_740, x_742, x_735, x_739, x_737, x_736);
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_746; 
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
if (lean_obj_tag(x_746) == 0)
{
lean_object* x_747; lean_object* x_748; 
x_747 = lean_ctor_get(x_745, 1);
lean_inc(x_747);
lean_dec_ref(x_745);
lean_inc(x_737);
lean_inc_ref(x_739);
lean_inc(x_735);
lean_inc_ref(x_742);
lean_inc_ref(x_740);
x_748 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_740, x_741, x_738, x_742, x_735, x_739, x_737, x_747);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
if (lean_obj_tag(x_749) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
lean_dec_ref(x_748);
x_751 = lean_ctor_get(x_740, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_740, 3);
lean_inc(x_752);
lean_inc(x_752);
x_753 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_752, x_750);
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
if (lean_obj_tag(x_754) == 0)
{
lean_object* x_755; lean_object* x_756; 
x_755 = lean_ctor_get(x_753, 1);
lean_inc(x_755);
lean_dec_ref(x_753);
lean_inc(x_737);
lean_inc_ref(x_739);
lean_inc(x_735);
lean_inc_ref(x_742);
lean_inc_ref(x_743);
lean_inc(x_738);
lean_inc_ref(x_741);
lean_inc_ref(x_710);
lean_inc_ref(x_740);
x_756 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_740, x_710, x_741, x_738, x_743, x_742, x_735, x_739, x_737, x_755);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; 
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
if (lean_obj_tag(x_757) == 0)
{
lean_object* x_758; lean_object* x_759; 
x_758 = lean_ctor_get(x_756, 1);
lean_inc(x_758);
lean_dec_ref(x_756);
lean_inc(x_737);
lean_inc_ref(x_739);
lean_inc(x_735);
lean_inc_ref(x_742);
lean_inc_ref(x_743);
lean_inc(x_738);
lean_inc_ref(x_741);
x_759 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_752, x_741, x_738, x_743, x_742, x_735, x_739, x_737, x_758);
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_760; 
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
if (lean_obj_tag(x_760) == 0)
{
lean_object* x_761; lean_object* x_762; 
x_761 = lean_ctor_get(x_759, 1);
lean_inc(x_761);
lean_dec_ref(x_759);
lean_inc(x_737);
lean_inc_ref(x_739);
lean_inc(x_735);
lean_inc_ref(x_742);
lean_inc_ref(x_743);
lean_inc(x_738);
lean_inc_ref(x_741);
x_762 = l_Lean_Compiler_LCNF_Simp_simp(x_710, x_741, x_738, x_743, x_742, x_735, x_739, x_737, x_761);
if (lean_obj_tag(x_762) == 0)
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; uint8_t x_767; 
x_763 = lean_ctor_get(x_762, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_762, 1);
lean_inc(x_764);
lean_dec_ref(x_762);
x_765 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_751, x_738, x_764);
lean_dec(x_751);
x_766 = lean_ctor_get(x_765, 0);
lean_inc(x_766);
x_767 = lean_unbox(x_766);
lean_dec(x_766);
if (x_767 == 0)
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; 
lean_dec_ref(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_741);
lean_dec_ref(x_739);
lean_dec(x_737);
lean_dec_ref(x_1);
x_768 = lean_ctor_get(x_765, 1);
lean_inc(x_768);
lean_dec_ref(x_765);
x_769 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_740, x_738, x_735, x_768);
lean_dec(x_735);
lean_dec(x_738);
lean_dec_ref(x_740);
x_770 = lean_ctor_get(x_769, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_769)) {
 lean_ctor_release(x_769, 0);
 lean_ctor_release(x_769, 1);
 x_771 = x_769;
} else {
 lean_dec_ref(x_769);
 x_771 = lean_box(0);
}
if (lean_is_scalar(x_771)) {
 x_772 = lean_alloc_ctor(0, 2, 0);
} else {
 x_772 = x_771;
}
lean_ctor_set(x_772, 0, x_763);
lean_ctor_set(x_772, 1, x_770);
return x_772;
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_773 = lean_ctor_get(x_765, 1);
lean_inc(x_773);
lean_dec_ref(x_765);
lean_inc_ref(x_740);
x_774 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_740, x_741, x_738, x_743, x_742, x_735, x_739, x_737, x_773);
lean_dec(x_737);
lean_dec_ref(x_739);
lean_dec(x_735);
lean_dec_ref(x_742);
lean_dec_ref(x_743);
lean_dec(x_738);
lean_dec_ref(x_741);
x_775 = lean_ctor_get(x_774, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_776 = x_774;
} else {
 lean_dec_ref(x_774);
 x_776 = lean_box(0);
}
x_777 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_740, x_763);
lean_dec_ref(x_1);
if (lean_is_scalar(x_776)) {
 x_778 = lean_alloc_ctor(0, 2, 0);
} else {
 x_778 = x_776;
}
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_778, 1, x_775);
return x_778;
}
}
else
{
lean_dec(x_751);
lean_dec_ref(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_735);
lean_dec_ref(x_1);
return x_762;
}
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec_ref(x_1);
x_779 = lean_ctor_get(x_760, 0);
lean_inc(x_779);
lean_dec_ref(x_760);
x_780 = lean_ctor_get(x_759, 1);
lean_inc(x_780);
lean_dec_ref(x_759);
x_781 = lean_ctor_get(x_779, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_779, 1);
lean_inc(x_782);
lean_dec(x_779);
x_783 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_751, x_782, x_738, x_735, x_739, x_737, x_780);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_784 = lean_ctor_get(x_783, 1);
lean_inc(x_784);
lean_dec_ref(x_783);
x_785 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_740, x_738, x_735, x_784);
lean_dec_ref(x_740);
x_786 = lean_ctor_get(x_785, 1);
lean_inc(x_786);
lean_dec_ref(x_785);
lean_inc(x_737);
lean_inc_ref(x_739);
lean_inc(x_735);
lean_inc_ref(x_742);
lean_inc_ref(x_743);
lean_inc(x_738);
lean_inc_ref(x_741);
x_787 = l_Lean_Compiler_LCNF_Simp_simp(x_710, x_741, x_738, x_743, x_742, x_735, x_739, x_737, x_786);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_787, 1);
lean_inc(x_789);
lean_dec_ref(x_787);
x_790 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_781, x_788, x_741, x_738, x_743, x_742, x_735, x_739, x_737, x_789);
lean_dec(x_737);
lean_dec_ref(x_739);
lean_dec(x_735);
lean_dec_ref(x_742);
lean_dec_ref(x_743);
lean_dec(x_738);
lean_dec_ref(x_741);
lean_dec(x_781);
return x_790;
}
else
{
lean_dec(x_781);
lean_dec_ref(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_741);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_735);
return x_787;
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_781);
lean_dec_ref(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_735);
lean_dec_ref(x_710);
x_791 = lean_ctor_get(x_783, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_783, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 lean_ctor_release(x_783, 1);
 x_793 = x_783;
} else {
 lean_dec_ref(x_783);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_791);
lean_ctor_set(x_794, 1, x_792);
return x_794;
}
}
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec(x_751);
lean_dec_ref(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_735);
lean_dec_ref(x_710);
lean_dec_ref(x_1);
x_795 = lean_ctor_get(x_759, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_759, 1);
lean_inc(x_796);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 lean_ctor_release(x_759, 1);
 x_797 = x_759;
} else {
 lean_dec_ref(x_759);
 x_797 = lean_box(0);
}
if (lean_is_scalar(x_797)) {
 x_798 = lean_alloc_ctor(1, 2, 0);
} else {
 x_798 = x_797;
}
lean_ctor_set(x_798, 0, x_795);
lean_ctor_set(x_798, 1, x_796);
return x_798;
}
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
lean_dec(x_752);
lean_dec(x_751);
lean_dec_ref(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_741);
lean_dec_ref(x_739);
lean_dec(x_737);
lean_dec_ref(x_710);
lean_dec_ref(x_1);
x_799 = lean_ctor_get(x_756, 1);
lean_inc(x_799);
lean_dec_ref(x_756);
x_800 = lean_ctor_get(x_757, 0);
lean_inc(x_800);
lean_dec_ref(x_757);
x_801 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_740, x_738, x_735, x_799);
lean_dec(x_735);
lean_dec(x_738);
lean_dec_ref(x_740);
x_802 = lean_ctor_get(x_801, 1);
lean_inc(x_802);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 lean_ctor_release(x_801, 1);
 x_803 = x_801;
} else {
 lean_dec_ref(x_801);
 x_803 = lean_box(0);
}
if (lean_is_scalar(x_803)) {
 x_804 = lean_alloc_ctor(0, 2, 0);
} else {
 x_804 = x_803;
}
lean_ctor_set(x_804, 0, x_800);
lean_ctor_set(x_804, 1, x_802);
return x_804;
}
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
lean_dec(x_752);
lean_dec(x_751);
lean_dec_ref(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_735);
lean_dec_ref(x_710);
lean_dec_ref(x_1);
x_805 = lean_ctor_get(x_756, 0);
lean_inc(x_805);
x_806 = lean_ctor_get(x_756, 1);
lean_inc(x_806);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 lean_ctor_release(x_756, 1);
 x_807 = x_756;
} else {
 lean_dec_ref(x_756);
 x_807 = lean_box(0);
}
if (lean_is_scalar(x_807)) {
 x_808 = lean_alloc_ctor(1, 2, 0);
} else {
 x_808 = x_807;
}
lean_ctor_set(x_808, 0, x_805);
lean_ctor_set(x_808, 1, x_806);
return x_808;
}
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec(x_752);
lean_dec_ref(x_1);
x_809 = lean_ctor_get(x_753, 1);
lean_inc(x_809);
lean_dec_ref(x_753);
x_810 = lean_ctor_get(x_754, 0);
lean_inc(x_810);
lean_dec_ref(x_754);
x_811 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_751, x_810, x_738, x_735, x_739, x_737, x_809);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_812 = lean_ctor_get(x_811, 1);
lean_inc(x_812);
lean_dec_ref(x_811);
x_813 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_740, x_738, x_735, x_812);
lean_dec_ref(x_740);
x_814 = lean_ctor_get(x_813, 1);
lean_inc(x_814);
lean_dec_ref(x_813);
x_1 = x_710;
x_2 = x_741;
x_3 = x_738;
x_4 = x_743;
x_5 = x_742;
x_6 = x_735;
x_7 = x_739;
x_8 = x_737;
x_9 = x_814;
goto _start;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
lean_dec_ref(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_735);
lean_dec_ref(x_710);
x_816 = lean_ctor_get(x_811, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_811, 1);
lean_inc(x_817);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 x_818 = x_811;
} else {
 lean_dec_ref(x_811);
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
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_dec_ref(x_740);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_820 = x_1;
} else {
 lean_dec_ref(x_1);
 x_820 = lean_box(0);
}
x_821 = lean_ctor_get(x_748, 1);
lean_inc(x_821);
lean_dec_ref(x_748);
x_822 = lean_ctor_get(x_749, 0);
lean_inc(x_822);
lean_dec_ref(x_749);
if (lean_is_scalar(x_820)) {
 x_823 = lean_alloc_ctor(1, 2, 0);
} else {
 x_823 = x_820;
 lean_ctor_set_tag(x_823, 1);
}
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_823, 1, x_710);
x_1 = x_823;
x_2 = x_741;
x_3 = x_738;
x_4 = x_743;
x_5 = x_742;
x_6 = x_735;
x_7 = x_739;
x_8 = x_737;
x_9 = x_821;
goto _start;
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
lean_dec_ref(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_735);
lean_dec_ref(x_710);
lean_dec_ref(x_1);
x_825 = lean_ctor_get(x_748, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_748, 1);
lean_inc(x_826);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_827 = x_748;
} else {
 lean_dec_ref(x_748);
 x_827 = lean_box(0);
}
if (lean_is_scalar(x_827)) {
 x_828 = lean_alloc_ctor(1, 2, 0);
} else {
 x_828 = x_827;
}
lean_ctor_set(x_828, 0, x_825);
lean_ctor_set(x_828, 1, x_826);
return x_828;
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
lean_dec_ref(x_740);
lean_dec_ref(x_1);
x_829 = lean_ctor_get(x_745, 1);
lean_inc(x_829);
lean_dec_ref(x_745);
x_830 = lean_ctor_get(x_746, 0);
lean_inc(x_830);
lean_dec_ref(x_746);
x_831 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_738, x_829);
x_832 = lean_ctor_get(x_831, 1);
lean_inc(x_832);
lean_dec_ref(x_831);
lean_inc(x_737);
lean_inc_ref(x_739);
lean_inc(x_735);
lean_inc_ref(x_742);
lean_inc_ref(x_743);
lean_inc(x_738);
lean_inc_ref(x_741);
x_833 = l_Lean_Compiler_LCNF_Simp_simp(x_710, x_741, x_738, x_743, x_742, x_735, x_739, x_737, x_832);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
lean_dec_ref(x_833);
x_836 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_830, x_834, x_741, x_738, x_743, x_742, x_735, x_739, x_737, x_835);
lean_dec(x_737);
lean_dec_ref(x_739);
lean_dec(x_735);
lean_dec_ref(x_742);
lean_dec_ref(x_743);
lean_dec(x_738);
lean_dec_ref(x_741);
lean_dec(x_830);
return x_836;
}
else
{
lean_dec(x_830);
lean_dec_ref(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_741);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_735);
return x_833;
}
}
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; 
lean_dec_ref(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_741);
lean_dec_ref(x_740);
lean_dec_ref(x_739);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_735);
lean_dec_ref(x_710);
lean_dec_ref(x_1);
x_837 = lean_ctor_get(x_745, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_745, 1);
lean_inc(x_838);
if (lean_is_exclusive(x_745)) {
 lean_ctor_release(x_745, 0);
 lean_ctor_release(x_745, 1);
 x_839 = x_745;
} else {
 lean_dec_ref(x_745);
 x_839 = lean_box(0);
}
if (lean_is_scalar(x_839)) {
 x_840 = lean_alloc_ctor(1, 2, 0);
} else {
 x_840 = x_839;
}
lean_ctor_set(x_840, 0, x_837);
lean_ctor_set(x_840, 1, x_838);
return x_840;
}
}
else
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; uint8_t x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; uint64_t x_858; uint64_t x_859; uint64_t x_860; uint64_t x_861; uint64_t x_862; uint64_t x_863; uint64_t x_864; size_t x_865; size_t x_866; size_t x_867; size_t x_868; size_t x_869; lean_object* x_870; uint8_t x_871; 
lean_dec_ref(x_1);
x_841 = lean_st_ref_take(x_738, x_736);
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_842, 0);
lean_inc_ref(x_843);
x_844 = lean_ctor_get(x_841, 1);
lean_inc(x_844);
lean_dec_ref(x_841);
x_845 = lean_ctor_get(x_842, 1);
lean_inc_ref(x_845);
x_846 = lean_ctor_get(x_842, 2);
lean_inc(x_846);
x_847 = lean_ctor_get(x_842, 3);
lean_inc_ref(x_847);
x_848 = lean_ctor_get_uint8(x_842, sizeof(void*)*7);
x_849 = lean_ctor_get(x_842, 4);
lean_inc(x_849);
x_850 = lean_ctor_get(x_842, 5);
lean_inc(x_850);
x_851 = lean_ctor_get(x_842, 6);
lean_inc(x_851);
lean_dec(x_842);
x_852 = lean_ctor_get(x_843, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_843, 1);
lean_inc_ref(x_853);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 x_854 = x_843;
} else {
 lean_dec_ref(x_843);
 x_854 = lean_box(0);
}
x_855 = lean_ctor_get(x_740, 0);
lean_inc(x_855);
x_856 = lean_box(0);
x_857 = lean_array_get_size(x_853);
x_858 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_855);
x_859 = 32;
x_860 = lean_uint64_shift_right(x_858, x_859);
x_861 = lean_uint64_xor(x_858, x_860);
x_862 = 16;
x_863 = lean_uint64_shift_right(x_861, x_862);
x_864 = lean_uint64_xor(x_861, x_863);
x_865 = lean_uint64_to_usize(x_864);
x_866 = lean_usize_of_nat(x_857);
lean_dec(x_857);
x_867 = 1;
x_868 = lean_usize_sub(x_866, x_867);
x_869 = lean_usize_land(x_865, x_868);
x_870 = lean_array_uget(x_853, x_869);
x_871 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_855, x_870);
if (x_871 == 0)
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; uint8_t x_880; 
x_872 = lean_nat_add(x_852, x_706);
lean_dec(x_852);
x_873 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_873, 0, x_855);
lean_ctor_set(x_873, 1, x_856);
lean_ctor_set(x_873, 2, x_870);
x_874 = lean_array_uset(x_853, x_869, x_873);
x_875 = lean_unsigned_to_nat(4u);
x_876 = lean_nat_mul(x_872, x_875);
x_877 = lean_unsigned_to_nat(3u);
x_878 = lean_nat_div(x_876, x_877);
lean_dec(x_876);
x_879 = lean_array_get_size(x_874);
x_880 = lean_nat_dec_le(x_878, x_879);
lean_dec(x_879);
lean_dec(x_878);
if (x_880 == 0)
{
lean_object* x_881; lean_object* x_882; 
x_881 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_874);
if (lean_is_scalar(x_854)) {
 x_882 = lean_alloc_ctor(0, 2, 0);
} else {
 x_882 = x_854;
}
lean_ctor_set(x_882, 0, x_872);
lean_ctor_set(x_882, 1, x_881);
x_711 = x_735;
x_712 = x_737;
x_713 = x_739;
x_714 = x_738;
x_715 = x_740;
x_716 = x_845;
x_717 = x_846;
x_718 = x_847;
x_719 = x_848;
x_720 = x_849;
x_721 = x_850;
x_722 = x_851;
x_723 = x_742;
x_724 = x_741;
x_725 = x_844;
x_726 = x_743;
x_727 = x_882;
goto block_734;
}
else
{
lean_object* x_883; 
if (lean_is_scalar(x_854)) {
 x_883 = lean_alloc_ctor(0, 2, 0);
} else {
 x_883 = x_854;
}
lean_ctor_set(x_883, 0, x_872);
lean_ctor_set(x_883, 1, x_874);
x_711 = x_735;
x_712 = x_737;
x_713 = x_739;
x_714 = x_738;
x_715 = x_740;
x_716 = x_845;
x_717 = x_846;
x_718 = x_847;
x_719 = x_848;
x_720 = x_849;
x_721 = x_850;
x_722 = x_851;
x_723 = x_742;
x_724 = x_741;
x_725 = x_844;
x_726 = x_743;
x_727 = x_883;
goto block_734;
}
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_884 = lean_box(0);
x_885 = lean_array_uset(x_853, x_869, x_884);
x_886 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_855, x_856, x_870);
x_887 = lean_array_uset(x_885, x_869, x_886);
if (lean_is_scalar(x_854)) {
 x_888 = lean_alloc_ctor(0, 2, 0);
} else {
 x_888 = x_854;
}
lean_ctor_set(x_888, 0, x_852);
lean_ctor_set(x_888, 1, x_887);
x_711 = x_735;
x_712 = x_737;
x_713 = x_739;
x_714 = x_738;
x_715 = x_740;
x_716 = x_845;
x_717 = x_846;
x_718 = x_847;
x_719 = x_848;
x_720 = x_849;
x_721 = x_850;
x_722 = x_851;
x_723 = x_742;
x_724 = x_741;
x_725 = x_844;
x_726 = x_743;
x_727 = x_888;
goto block_734;
}
}
}
block_904:
{
uint8_t x_901; 
x_901 = l_Lean_Expr_isErased(x_891);
lean_dec_ref(x_891);
if (x_901 == 0)
{
lean_dec(x_892);
x_735 = x_897;
x_736 = x_900;
x_737 = x_899;
x_738 = x_894;
x_739 = x_898;
x_740 = x_890;
x_741 = x_893;
x_742 = x_896;
x_743 = x_895;
x_744 = x_100;
goto block_889;
}
else
{
lean_object* x_902; uint8_t x_903; 
x_902 = lean_box(1);
x_903 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1209_(x_892, x_902);
lean_dec(x_892);
if (x_903 == 0)
{
x_735 = x_897;
x_736 = x_900;
x_737 = x_899;
x_738 = x_894;
x_739 = x_898;
x_740 = x_890;
x_741 = x_893;
x_742 = x_896;
x_743 = x_895;
x_744 = x_901;
goto block_889;
}
else
{
x_735 = x_897;
x_736 = x_900;
x_737 = x_899;
x_738 = x_894;
x_739 = x_898;
x_740 = x_890;
x_741 = x_893;
x_742 = x_896;
x_743 = x_895;
x_744 = x_100;
goto block_889;
}
}
}
block_934:
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_916 = lean_ctor_get(x_906, 2);
lean_inc_ref(x_916);
x_917 = lean_ctor_get(x_906, 3);
lean_inc(x_917);
lean_inc(x_914);
lean_inc_ref(x_913);
lean_inc(x_912);
lean_inc_ref(x_911);
lean_inc_ref(x_910);
lean_inc(x_917);
x_918 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_917, x_908, x_910, x_911, x_912, x_913, x_914, x_915);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
if (lean_obj_tag(x_919) == 0)
{
lean_object* x_920; 
x_920 = lean_ctor_get(x_918, 1);
lean_inc(x_920);
lean_dec_ref(x_918);
x_890 = x_906;
x_891 = x_916;
x_892 = x_917;
x_893 = x_908;
x_894 = x_909;
x_895 = x_910;
x_896 = x_911;
x_897 = x_912;
x_898 = x_913;
x_899 = x_914;
x_900 = x_920;
goto block_904;
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
lean_dec(x_917);
lean_dec_ref(x_916);
x_921 = lean_ctor_get(x_918, 1);
lean_inc(x_921);
lean_dec_ref(x_918);
x_922 = lean_ctor_get(x_919, 0);
lean_inc(x_922);
lean_dec_ref(x_919);
x_923 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_909, x_921);
x_924 = lean_ctor_get(x_923, 1);
lean_inc(x_924);
lean_dec_ref(x_923);
x_925 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_906, x_922, x_912, x_924);
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_925, 1);
lean_inc(x_927);
lean_dec_ref(x_925);
x_928 = lean_ctor_get(x_926, 2);
lean_inc_ref(x_928);
x_929 = lean_ctor_get(x_926, 3);
lean_inc(x_929);
x_890 = x_926;
x_891 = x_928;
x_892 = x_929;
x_893 = x_908;
x_894 = x_909;
x_895 = x_910;
x_896 = x_911;
x_897 = x_912;
x_898 = x_913;
x_899 = x_914;
x_900 = x_927;
goto block_904;
}
}
else
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
lean_dec(x_917);
lean_dec_ref(x_916);
lean_dec(x_914);
lean_dec_ref(x_913);
lean_dec(x_912);
lean_dec_ref(x_911);
lean_dec_ref(x_910);
lean_dec(x_909);
lean_dec_ref(x_908);
lean_dec(x_906);
lean_dec_ref(x_710);
lean_dec_ref(x_1);
x_930 = lean_ctor_get(x_918, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_918, 1);
lean_inc(x_931);
if (lean_is_exclusive(x_918)) {
 lean_ctor_release(x_918, 0);
 lean_ctor_release(x_918, 1);
 x_932 = x_918;
} else {
 lean_dec_ref(x_918);
 x_932 = lean_box(0);
}
if (lean_is_scalar(x_932)) {
 x_933 = lean_alloc_ctor(1, 2, 0);
} else {
 x_933 = x_932;
}
lean_ctor_set(x_933, 0, x_930);
lean_ctor_set(x_933, 1, x_931);
return x_933;
}
}
block_937:
{
lean_object* x_935; lean_object* x_936; 
x_935 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_907);
x_936 = lean_ctor_get(x_935, 1);
lean_inc(x_936);
lean_dec_ref(x_935);
x_908 = x_2;
x_909 = x_3;
x_910 = x_4;
x_911 = x_5;
x_912 = x_6;
x_913 = x_708;
x_914 = x_8;
x_915 = x_936;
goto block_934;
}
}
case 3:
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; 
lean_dec_ref(x_67);
x_939 = lean_ctor_get(x_1, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_940);
x_941 = lean_st_ref_get(x_3, x_651);
x_942 = lean_ctor_get(x_941, 0);
lean_inc(x_942);
x_943 = lean_ctor_get(x_941, 1);
lean_inc(x_943);
lean_dec_ref(x_941);
x_944 = lean_ctor_get(x_942, 0);
lean_inc_ref(x_944);
lean_dec(x_942);
x_945 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_944, x_939, x_100);
lean_dec_ref(x_944);
if (lean_obj_tag(x_945) == 0)
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_955; 
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
lean_dec_ref(x_945);
x_947 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_100, x_940, x_3, x_943);
x_948 = lean_ctor_get(x_947, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_947, 1);
lean_inc(x_949);
if (lean_is_exclusive(x_947)) {
 lean_ctor_release(x_947, 0);
 lean_ctor_release(x_947, 1);
 x_950 = x_947;
} else {
 lean_dec_ref(x_947);
 x_950 = lean_box(0);
}
lean_inc(x_948);
x_955 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_946, x_948, x_2, x_3, x_4, x_5, x_6, x_708, x_8, x_949);
if (lean_obj_tag(x_955) == 0)
{
lean_object* x_956; 
x_956 = lean_ctor_get(x_955, 0);
lean_inc(x_956);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; uint8_t x_962; 
lean_dec_ref(x_708);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_957 = lean_ctor_get(x_955, 1);
lean_inc(x_957);
lean_dec_ref(x_955);
lean_inc(x_946);
x_958 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_946, x_3, x_957);
x_959 = lean_ctor_get(x_958, 1);
lean_inc(x_959);
lean_dec_ref(x_958);
x_960 = lean_unsigned_to_nat(0u);
x_961 = lean_array_get_size(x_948);
x_962 = lean_nat_dec_lt(x_960, x_961);
if (x_962 == 0)
{
lean_dec(x_961);
lean_dec(x_3);
x_951 = x_959;
goto block_954;
}
else
{
uint8_t x_963; 
x_963 = lean_nat_dec_le(x_961, x_961);
if (x_963 == 0)
{
lean_dec(x_961);
lean_dec(x_3);
x_951 = x_959;
goto block_954;
}
else
{
lean_object* x_964; size_t x_965; size_t x_966; lean_object* x_967; lean_object* x_968; 
x_964 = lean_box(0);
x_965 = 0;
x_966 = lean_usize_of_nat(x_961);
lean_dec(x_961);
x_967 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_948, x_965, x_966, x_964, x_3, x_959);
lean_dec(x_3);
x_968 = lean_ctor_get(x_967, 1);
lean_inc(x_968);
lean_dec_ref(x_967);
x_951 = x_968;
goto block_954;
}
}
}
else
{
lean_object* x_969; lean_object* x_970; 
lean_dec(x_950);
lean_dec(x_948);
lean_dec(x_946);
lean_dec_ref(x_1);
x_969 = lean_ctor_get(x_955, 1);
lean_inc(x_969);
lean_dec_ref(x_955);
x_970 = lean_ctor_get(x_956, 0);
lean_inc(x_970);
lean_dec_ref(x_956);
x_1 = x_970;
x_7 = x_708;
x_9 = x_969;
goto _start;
}
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
lean_dec(x_950);
lean_dec(x_948);
lean_dec(x_946);
lean_dec_ref(x_708);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_972 = lean_ctor_get(x_955, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_955, 1);
lean_inc(x_973);
if (lean_is_exclusive(x_955)) {
 lean_ctor_release(x_955, 0);
 lean_ctor_release(x_955, 1);
 x_974 = x_955;
} else {
 lean_dec_ref(x_955);
 x_974 = lean_box(0);
}
if (lean_is_scalar(x_974)) {
 x_975 = lean_alloc_ctor(1, 2, 0);
} else {
 x_975 = x_974;
}
lean_ctor_set(x_975, 0, x_972);
lean_ctor_set(x_975, 1, x_973);
return x_975;
}
block_954:
{
lean_object* x_952; lean_object* x_953; 
x_952 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_1, x_946, x_948);
lean_dec_ref(x_1);
if (lean_is_scalar(x_950)) {
 x_953 = lean_alloc_ctor(0, 2, 0);
} else {
 x_953 = x_950;
}
lean_ctor_set(x_953, 0, x_952);
lean_ctor_set(x_953, 1, x_951);
return x_953;
}
}
else
{
lean_object* x_976; 
lean_dec_ref(x_940);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_976 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_708, x_8, x_943);
lean_dec(x_8);
lean_dec_ref(x_708);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_976;
}
}
case 4:
{
lean_object* x_977; lean_object* x_978; 
x_977 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_977);
lean_inc(x_8);
lean_inc_ref(x_708);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_977);
x_978 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_977, x_2, x_3, x_4, x_5, x_6, x_708, x_8, x_651);
if (lean_obj_tag(x_978) == 0)
{
lean_object* x_979; 
x_979 = lean_ctor_get(x_978, 0);
lean_inc(x_979);
if (lean_obj_tag(x_979) == 0)
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
x_980 = lean_ctor_get(x_978, 1);
lean_inc(x_980);
lean_dec_ref(x_978);
x_981 = lean_st_ref_get(x_3, x_980);
x_982 = lean_ctor_get(x_981, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_981, 1);
lean_inc(x_983);
lean_dec_ref(x_981);
x_984 = lean_ctor_get(x_977, 1);
lean_inc_ref(x_984);
x_985 = lean_ctor_get(x_977, 2);
lean_inc(x_985);
x_986 = lean_ctor_get(x_977, 3);
lean_inc_ref(x_986);
lean_dec_ref(x_977);
x_987 = lean_ctor_get(x_982, 0);
lean_inc_ref(x_987);
lean_dec(x_982);
x_988 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_987, x_985, x_100);
lean_dec_ref(x_987);
if (lean_obj_tag(x_988) == 0)
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; 
x_989 = lean_ctor_get(x_988, 0);
lean_inc(x_989);
lean_dec_ref(x_988);
x_990 = lean_st_ref_get(x_3, x_983);
x_991 = lean_ctor_get(x_990, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_990, 1);
lean_inc(x_992);
lean_dec_ref(x_990);
x_993 = lean_box(x_100);
lean_inc(x_989);
x_994 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__1___boxed), 11, 2);
lean_closure_set(x_994, 0, x_989);
lean_closure_set(x_994, 1, x_993);
x_995 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_67, x_986, x_994);
lean_inc(x_8);
lean_inc_ref(x_708);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_996 = lean_apply_8(x_995, x_2, x_3, x_4, x_5, x_6, x_708, x_8, x_992);
if (lean_obj_tag(x_996) == 0)
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; 
x_997 = lean_ctor_get(x_996, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_996, 1);
lean_inc(x_998);
lean_dec_ref(x_996);
lean_inc(x_6);
lean_inc(x_3);
x_999 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_997, x_2, x_3, x_4, x_5, x_6, x_708, x_8, x_998);
if (lean_obj_tag(x_999) == 0)
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1013; uint8_t x_1014; 
x_1000 = lean_ctor_get(x_999, 0);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_999, 1);
lean_inc(x_1001);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 lean_ctor_release(x_999, 1);
 x_1002 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1002 = lean_box(0);
}
x_1003 = lean_ctor_get(x_991, 0);
lean_inc_ref(x_1003);
lean_dec(x_991);
x_1004 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1003, x_100, x_984);
lean_dec_ref(x_1003);
x_1013 = lean_array_get_size(x_1000);
x_1014 = lean_nat_dec_eq(x_1013, x_706);
lean_dec(x_1013);
if (x_1014 == 0)
{
lean_dec(x_1002);
lean_dec(x_6);
x_1005 = x_3;
x_1006 = x_1001;
goto block_1012;
}
else
{
lean_object* x_1015; lean_object* x_1016; 
x_1015 = lean_unsigned_to_nat(0u);
x_1016 = lean_array_fget(x_1000, x_1015);
if (lean_obj_tag(x_1016) == 0)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1025; lean_object* x_1026; uint8_t x_1035; lean_object* x_1036; uint8_t x_1038; 
lean_dec(x_1002);
x_1017 = lean_ctor_get(x_1016, 1);
lean_inc_ref(x_1017);
x_1018 = lean_ctor_get(x_1016, 2);
lean_inc_ref(x_1018);
lean_dec_ref(x_1016);
x_1025 = lean_array_get_size(x_1017);
x_1038 = lean_nat_dec_lt(x_1015, x_1025);
if (x_1038 == 0)
{
x_1035 = x_100;
x_1036 = x_1001;
goto block_1037;
}
else
{
if (x_1038 == 0)
{
x_1035 = x_100;
x_1036 = x_1001;
goto block_1037;
}
else
{
size_t x_1039; size_t x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; uint8_t x_1044; 
x_1039 = 0;
x_1040 = lean_usize_of_nat(x_1025);
x_1041 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1017, x_1039, x_1040, x_3, x_1001);
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
lean_dec_ref(x_1041);
x_1044 = lean_unbox(x_1042);
lean_dec(x_1042);
x_1035 = x_1044;
x_1036 = x_1043;
goto block_1037;
}
}
block_1024:
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1020 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_1019);
lean_dec(x_3);
x_1021 = lean_ctor_get(x_1020, 1);
lean_inc(x_1021);
if (lean_is_exclusive(x_1020)) {
 lean_ctor_release(x_1020, 0);
 lean_ctor_release(x_1020, 1);
 x_1022 = x_1020;
} else {
 lean_dec_ref(x_1020);
 x_1022 = lean_box(0);
}
if (lean_is_scalar(x_1022)) {
 x_1023 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1023 = x_1022;
}
lean_ctor_set(x_1023, 0, x_1018);
lean_ctor_set(x_1023, 1, x_1021);
return x_1023;
}
block_1034:
{
uint8_t x_1027; 
x_1027 = lean_nat_dec_lt(x_1015, x_1025);
if (x_1027 == 0)
{
lean_dec(x_1025);
lean_dec_ref(x_1017);
lean_dec(x_6);
x_1019 = x_1026;
goto block_1024;
}
else
{
uint8_t x_1028; 
x_1028 = lean_nat_dec_le(x_1025, x_1025);
if (x_1028 == 0)
{
lean_dec(x_1025);
lean_dec_ref(x_1017);
lean_dec(x_6);
x_1019 = x_1026;
goto block_1024;
}
else
{
lean_object* x_1029; size_t x_1030; size_t x_1031; lean_object* x_1032; lean_object* x_1033; 
x_1029 = lean_box(0);
x_1030 = 0;
x_1031 = lean_usize_of_nat(x_1025);
lean_dec(x_1025);
x_1032 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1017, x_1030, x_1031, x_1029, x_6, x_1026);
lean_dec(x_6);
lean_dec_ref(x_1017);
x_1033 = lean_ctor_get(x_1032, 1);
lean_inc(x_1033);
lean_dec_ref(x_1032);
x_1019 = x_1033;
goto block_1024;
}
}
}
block_1037:
{
if (x_1035 == 0)
{
lean_dec_ref(x_1004);
lean_dec(x_1000);
lean_dec(x_989);
lean_dec_ref(x_1);
x_1026 = x_1036;
goto block_1034;
}
else
{
if (x_100 == 0)
{
lean_dec(x_1025);
lean_dec_ref(x_1018);
lean_dec_ref(x_1017);
lean_dec(x_6);
x_1005 = x_3;
x_1006 = x_1036;
goto block_1012;
}
else
{
lean_dec_ref(x_1004);
lean_dec(x_1000);
lean_dec(x_989);
lean_dec_ref(x_1);
x_1026 = x_1036;
goto block_1034;
}
}
}
}
else
{
lean_object* x_1045; lean_object* x_1046; 
lean_dec_ref(x_1004);
lean_dec(x_1000);
lean_dec(x_989);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1045 = lean_ctor_get(x_1016, 0);
lean_inc_ref(x_1045);
lean_dec_ref(x_1016);
if (lean_is_scalar(x_1002)) {
 x_1046 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1046 = x_1002;
}
lean_ctor_set(x_1046, 0, x_1045);
lean_ctor_set(x_1046, 1, x_1001);
return x_1046;
}
}
block_1012:
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
lean_inc(x_989);
x_1007 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_989, x_1005, x_1006);
lean_dec(x_1005);
x_1008 = lean_ctor_get(x_1007, 1);
lean_inc(x_1008);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1009 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1009 = lean_box(0);
}
x_1010 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_1, x_1004, x_989, x_1000);
if (lean_is_scalar(x_1009)) {
 x_1011 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1011 = x_1009;
}
lean_ctor_set(x_1011, 0, x_1010);
lean_ctor_set(x_1011, 1, x_1008);
return x_1011;
}
}
else
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
lean_dec(x_991);
lean_dec(x_989);
lean_dec_ref(x_984);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1047 = lean_ctor_get(x_999, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_999, 1);
lean_inc(x_1048);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 lean_ctor_release(x_999, 1);
 x_1049 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1049 = lean_box(0);
}
if (lean_is_scalar(x_1049)) {
 x_1050 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1050 = x_1049;
}
lean_ctor_set(x_1050, 0, x_1047);
lean_ctor_set(x_1050, 1, x_1048);
return x_1050;
}
}
else
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_991);
lean_dec(x_989);
lean_dec_ref(x_984);
lean_dec_ref(x_708);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1051 = lean_ctor_get(x_996, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_996, 1);
lean_inc(x_1052);
if (lean_is_exclusive(x_996)) {
 lean_ctor_release(x_996, 0);
 lean_ctor_release(x_996, 1);
 x_1053 = x_996;
} else {
 lean_dec_ref(x_996);
 x_1053 = lean_box(0);
}
if (lean_is_scalar(x_1053)) {
 x_1054 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1054 = x_1053;
}
lean_ctor_set(x_1054, 0, x_1051);
lean_ctor_set(x_1054, 1, x_1052);
return x_1054;
}
}
else
{
lean_object* x_1055; 
lean_dec_ref(x_986);
lean_dec_ref(x_984);
lean_dec_ref(x_67);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1055 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_708, x_8, x_983);
lean_dec(x_8);
lean_dec_ref(x_708);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1055;
}
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
lean_dec_ref(x_977);
lean_dec_ref(x_708);
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1056 = lean_ctor_get(x_978, 1);
lean_inc(x_1056);
if (lean_is_exclusive(x_978)) {
 lean_ctor_release(x_978, 0);
 lean_ctor_release(x_978, 1);
 x_1057 = x_978;
} else {
 lean_dec_ref(x_978);
 x_1057 = lean_box(0);
}
x_1058 = lean_ctor_get(x_979, 0);
lean_inc(x_1058);
lean_dec_ref(x_979);
if (lean_is_scalar(x_1057)) {
 x_1059 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1059 = x_1057;
}
lean_ctor_set(x_1059, 0, x_1058);
lean_ctor_set(x_1059, 1, x_1056);
return x_1059;
}
}
else
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
lean_dec_ref(x_977);
lean_dec_ref(x_708);
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1060 = lean_ctor_get(x_978, 0);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_978, 1);
lean_inc(x_1061);
if (lean_is_exclusive(x_978)) {
 lean_ctor_release(x_978, 0);
 lean_ctor_release(x_978, 1);
 x_1062 = x_978;
} else {
 lean_dec_ref(x_978);
 x_1062 = lean_box(0);
}
if (lean_is_scalar(x_1062)) {
 x_1063 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1063 = x_1062;
}
lean_ctor_set(x_1063, 0, x_1060);
lean_ctor_set(x_1063, 1, x_1061);
return x_1063;
}
}
case 5:
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
lean_dec_ref(x_67);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1064 = lean_ctor_get(x_1, 0);
lean_inc(x_1064);
x_1065 = lean_st_ref_get(x_3, x_651);
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1065, 1);
lean_inc(x_1067);
lean_dec_ref(x_1065);
x_1068 = lean_ctor_get(x_1066, 0);
lean_inc_ref(x_1068);
lean_dec(x_1066);
x_1069 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_1068, x_1064, x_100);
lean_dec_ref(x_1068);
if (lean_obj_tag(x_1069) == 0)
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
lean_dec_ref(x_708);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1070 = lean_ctor_get(x_1069, 0);
lean_inc(x_1070);
lean_dec_ref(x_1069);
lean_inc(x_1070);
x_1071 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1070, x_3, x_1067);
lean_dec(x_3);
x_1072 = lean_ctor_get(x_1071, 1);
lean_inc(x_1072);
if (lean_is_exclusive(x_1071)) {
 lean_ctor_release(x_1071, 0);
 lean_ctor_release(x_1071, 1);
 x_1073 = x_1071;
} else {
 lean_dec_ref(x_1071);
 x_1073 = lean_box(0);
}
x_1074 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_1, x_1070);
if (lean_is_scalar(x_1073)) {
 x_1075 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1075 = x_1073;
}
lean_ctor_set(x_1075, 0, x_1074);
lean_ctor_set(x_1075, 1, x_1072);
return x_1075;
}
else
{
lean_object* x_1076; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1076 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_708, x_8, x_1067);
lean_dec(x_8);
lean_dec_ref(x_708);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1076;
}
}
case 6:
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
lean_dec_ref(x_708);
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1077 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1077);
x_1078 = lean_st_ref_get(x_3, x_651);
lean_dec(x_3);
x_1079 = lean_ctor_get(x_1078, 0);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_1078, 1);
lean_inc(x_1080);
if (lean_is_exclusive(x_1078)) {
 lean_ctor_release(x_1078, 0);
 lean_ctor_release(x_1078, 1);
 x_1081 = x_1078;
} else {
 lean_dec_ref(x_1078);
 x_1081 = lean_box(0);
}
x_1082 = lean_ctor_get(x_1079, 0);
lean_inc_ref(x_1082);
lean_dec(x_1079);
x_1083 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1082, x_100, x_1077);
lean_dec_ref(x_1082);
x_1084 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(x_1, x_1083);
if (lean_is_scalar(x_1081)) {
 x_1085 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1085 = x_1081;
}
lean_ctor_set(x_1085, 0, x_1084);
lean_ctor_set(x_1085, 1, x_1080);
return x_1085;
}
default: 
{
lean_object* x_1086; lean_object* x_1087; 
lean_dec_ref(x_67);
x_1086 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1086);
x_1087 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1087);
x_652 = x_1086;
x_653 = x_1087;
x_654 = x_2;
x_655 = x_3;
x_656 = x_4;
x_657 = x_5;
x_658 = x_6;
x_659 = x_708;
x_660 = x_8;
goto block_705;
}
}
block_705:
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; uint8_t x_668; 
x_661 = lean_ctor_get(x_652, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_652, 2);
lean_inc_ref(x_662);
x_663 = lean_ctor_get(x_652, 3);
lean_inc_ref(x_663);
x_664 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_661, x_655, x_651);
lean_dec(x_661);
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec_ref(x_664);
lean_inc(x_665);
lean_inc_ref(x_1);
lean_inc_ref(x_653);
x_667 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_667, 0, x_653);
lean_closure_set(x_667, 1, x_1);
lean_closure_set(x_667, 2, x_665);
x_668 = lean_unbox(x_665);
if (x_668 == 0)
{
uint8_t x_669; 
lean_dec(x_665);
lean_dec_ref(x_653);
x_669 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_669 == 0)
{
lean_dec_ref(x_663);
lean_dec_ref(x_662);
x_10 = x_667;
x_11 = x_652;
x_12 = x_654;
x_13 = x_655;
x_14 = x_656;
x_15 = x_657;
x_16 = x_658;
x_17 = x_659;
x_18 = x_660;
x_19 = x_666;
goto block_29;
}
else
{
uint8_t x_670; 
x_670 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_663, x_662);
lean_dec_ref(x_662);
if (x_670 == 0)
{
x_10 = x_667;
x_11 = x_652;
x_12 = x_654;
x_13 = x_655;
x_14 = x_656;
x_15 = x_657;
x_16 = x_658;
x_17 = x_659;
x_18 = x_660;
x_19 = x_666;
goto block_29;
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_671 = lean_st_ref_get(x_655, x_666);
x_672 = lean_ctor_get(x_671, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_671, 1);
lean_inc(x_673);
lean_dec_ref(x_671);
x_674 = lean_ctor_get(x_672, 0);
lean_inc_ref(x_674);
lean_dec(x_672);
lean_inc(x_660);
lean_inc_ref(x_659);
lean_inc(x_658);
lean_inc_ref(x_657);
x_675 = l_Lean_Compiler_LCNF_normFunDeclImp(x_100, x_652, x_674, x_657, x_658, x_659, x_660, x_673);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec_ref(x_675);
lean_inc(x_660);
lean_inc_ref(x_659);
lean_inc(x_658);
lean_inc_ref(x_657);
x_678 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_676, x_657, x_658, x_659, x_660, x_677);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 1);
lean_inc(x_680);
lean_dec_ref(x_678);
x_681 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_655, x_680);
x_682 = lean_ctor_get(x_681, 1);
lean_inc(x_682);
lean_dec_ref(x_681);
x_10 = x_667;
x_11 = x_679;
x_12 = x_654;
x_13 = x_655;
x_14 = x_656;
x_15 = x_657;
x_16 = x_658;
x_17 = x_659;
x_18 = x_660;
x_19 = x_682;
goto block_29;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
lean_dec_ref(x_667);
lean_dec(x_660);
lean_dec_ref(x_659);
lean_dec(x_658);
lean_dec_ref(x_657);
lean_dec_ref(x_656);
lean_dec(x_655);
lean_dec_ref(x_654);
x_683 = lean_ctor_get(x_678, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_678, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_685 = x_678;
} else {
 lean_dec_ref(x_678);
 x_685 = lean_box(0);
}
if (lean_is_scalar(x_685)) {
 x_686 = lean_alloc_ctor(1, 2, 0);
} else {
 x_686 = x_685;
}
lean_ctor_set(x_686, 0, x_683);
lean_ctor_set(x_686, 1, x_684);
return x_686;
}
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec_ref(x_667);
lean_dec(x_660);
lean_dec_ref(x_659);
lean_dec(x_658);
lean_dec_ref(x_657);
lean_dec_ref(x_656);
lean_dec(x_655);
lean_dec_ref(x_654);
x_687 = lean_ctor_get(x_675, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_675, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 x_689 = x_675;
} else {
 lean_dec_ref(x_675);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(1, 2, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_687);
lean_ctor_set(x_690, 1, x_688);
return x_690;
}
}
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec_ref(x_667);
lean_dec_ref(x_663);
lean_dec_ref(x_662);
x_691 = lean_st_ref_get(x_655, x_666);
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
lean_dec_ref(x_691);
x_694 = lean_ctor_get(x_692, 0);
lean_inc_ref(x_694);
lean_dec(x_692);
lean_inc(x_660);
lean_inc_ref(x_659);
lean_inc(x_658);
lean_inc_ref(x_657);
x_695 = l_Lean_Compiler_LCNF_normFunDeclImp(x_100, x_652, x_694, x_657, x_658, x_659, x_660, x_693);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; uint8_t x_699; lean_object* x_700; 
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec_ref(x_695);
x_698 = lean_box(0);
x_699 = lean_unbox(x_665);
lean_dec(x_665);
x_700 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_653, x_1, x_699, x_696, x_698, x_654, x_655, x_656, x_657, x_658, x_659, x_660, x_697);
lean_dec_ref(x_1);
return x_700;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_665);
lean_dec(x_660);
lean_dec_ref(x_659);
lean_dec(x_658);
lean_dec_ref(x_657);
lean_dec_ref(x_656);
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec_ref(x_653);
lean_dec_ref(x_1);
x_701 = lean_ctor_get(x_695, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_695, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 x_703 = x_695;
} else {
 lean_dec_ref(x_695);
 x_703 = lean_box(0);
}
if (lean_is_scalar(x_703)) {
 x_704 = lean_alloc_ctor(1, 2, 0);
} else {
 x_704 = x_703;
}
lean_ctor_set(x_704, 0, x_701);
lean_ctor_set(x_704, 1, x_702);
return x_704;
}
}
}
}
}
else
{
lean_object* x_1088; 
lean_dec_ref(x_99);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_67);
lean_dec_ref(x_1);
x_1088 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1088;
}
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; uint8_t x_1113; lean_object* x_1114; uint8_t x_1115; lean_object* x_1116; uint8_t x_1117; 
x_1089 = lean_ctor_get(x_69, 0);
x_1090 = lean_ctor_get(x_69, 2);
x_1091 = lean_ctor_get(x_69, 3);
x_1092 = lean_ctor_get(x_69, 4);
lean_inc(x_1092);
lean_inc(x_1091);
lean_inc(x_1090);
lean_inc(x_1089);
lean_dec(x_69);
x_1093 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_1094 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_1089);
x_1095 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_1095, 0, x_1089);
x_1096 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_1096, 0, x_1089);
x_1097 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1097, 0, x_1095);
lean_ctor_set(x_1097, 1, x_1096);
x_1098 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_1098, 0, x_1092);
x_1099 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_1099, 0, x_1091);
x_1100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_1100, 0, x_1090);
x_1101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1101, 0, x_1097);
lean_ctor_set(x_1101, 1, x_1093);
lean_ctor_set(x_1101, 2, x_1100);
lean_ctor_set(x_1101, 3, x_1099);
lean_ctor_set(x_1101, 4, x_1098);
lean_ctor_set(x_67, 1, x_1094);
lean_ctor_set(x_67, 0, x_1101);
x_1102 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_1102);
x_1103 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_1103);
x_1104 = lean_ctor_get(x_7, 2);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_7, 3);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_7, 4);
lean_inc(x_1106);
x_1107 = lean_ctor_get(x_7, 5);
lean_inc(x_1107);
x_1108 = lean_ctor_get(x_7, 6);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_7, 7);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_7, 8);
lean_inc(x_1110);
x_1111 = lean_ctor_get(x_7, 9);
lean_inc(x_1111);
x_1112 = lean_ctor_get(x_7, 10);
lean_inc(x_1112);
x_1113 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_1114 = lean_ctor_get(x_7, 11);
lean_inc(x_1114);
x_1115 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_1116 = lean_ctor_get(x_7, 12);
lean_inc_ref(x_1116);
x_1117 = lean_nat_dec_eq(x_1105, x_1106);
if (x_1117 == 0)
{
lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; 
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 lean_ctor_release(x_7, 9);
 lean_ctor_release(x_7, 10);
 lean_ctor_release(x_7, 11);
 lean_ctor_release(x_7, 12);
 x_1118 = x_7;
} else {
 lean_dec_ref(x_7);
 x_1118 = lean_box(0);
}
x_1119 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
x_1120 = lean_ctor_get(x_1119, 1);
lean_inc(x_1120);
lean_dec_ref(x_1119);
x_1175 = lean_unsigned_to_nat(1u);
x_1176 = lean_nat_add(x_1105, x_1175);
lean_dec(x_1105);
if (lean_is_scalar(x_1118)) {
 x_1177 = lean_alloc_ctor(0, 13, 2);
} else {
 x_1177 = x_1118;
}
lean_ctor_set(x_1177, 0, x_1102);
lean_ctor_set(x_1177, 1, x_1103);
lean_ctor_set(x_1177, 2, x_1104);
lean_ctor_set(x_1177, 3, x_1176);
lean_ctor_set(x_1177, 4, x_1106);
lean_ctor_set(x_1177, 5, x_1107);
lean_ctor_set(x_1177, 6, x_1108);
lean_ctor_set(x_1177, 7, x_1109);
lean_ctor_set(x_1177, 8, x_1110);
lean_ctor_set(x_1177, 9, x_1111);
lean_ctor_set(x_1177, 10, x_1112);
lean_ctor_set(x_1177, 11, x_1114);
lean_ctor_set(x_1177, 12, x_1116);
lean_ctor_set_uint8(x_1177, sizeof(void*)*13, x_1113);
lean_ctor_set_uint8(x_1177, sizeof(void*)*13 + 1, x_1115);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; uint8_t x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; uint8_t x_1213; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; uint8_t x_1407; 
lean_dec_ref(x_67);
x_1178 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1178);
x_1179 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1179);
lean_inc_ref(x_1178);
x_1374 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_1117, x_1178, x_3, x_5, x_6, x_1177, x_8, x_1120);
x_1375 = lean_ctor_get(x_1374, 0);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_1374, 1);
lean_inc(x_1376);
lean_dec_ref(x_1374);
x_1407 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2069_(x_1178, x_1375);
lean_dec_ref(x_1178);
if (x_1407 == 0)
{
goto block_1406;
}
else
{
if (x_1117 == 0)
{
x_1377 = x_2;
x_1378 = x_3;
x_1379 = x_4;
x_1380 = x_5;
x_1381 = x_6;
x_1382 = x_1177;
x_1383 = x_8;
x_1384 = x_1376;
goto block_1403;
}
else
{
goto block_1406;
}
}
block_1203:
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; 
x_1197 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_1197, 0, x_1196);
lean_ctor_set(x_1197, 1, x_1185);
lean_ctor_set(x_1197, 2, x_1186);
lean_ctor_set(x_1197, 3, x_1187);
lean_ctor_set(x_1197, 4, x_1189);
lean_ctor_set(x_1197, 5, x_1190);
lean_ctor_set(x_1197, 6, x_1191);
lean_ctor_set_uint8(x_1197, sizeof(void*)*7, x_1188);
x_1198 = lean_st_ref_set(x_1183, x_1197, x_1194);
x_1199 = lean_ctor_get(x_1198, 1);
lean_inc(x_1199);
lean_dec_ref(x_1198);
x_1200 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1184, x_1183, x_1180, x_1199);
lean_dec_ref(x_1184);
x_1201 = lean_ctor_get(x_1200, 1);
lean_inc(x_1201);
lean_dec_ref(x_1200);
x_1 = x_1179;
x_2 = x_1193;
x_3 = x_1183;
x_4 = x_1195;
x_5 = x_1192;
x_6 = x_1180;
x_7 = x_1182;
x_8 = x_1181;
x_9 = x_1201;
goto _start;
}
block_1358:
{
if (x_1213 == 0)
{
lean_object* x_1214; 
lean_inc(x_1206);
lean_inc_ref(x_1208);
lean_inc(x_1204);
lean_inc_ref(x_1211);
lean_inc_ref(x_1209);
x_1214 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_1209, x_1211, x_1204, x_1208, x_1206, x_1205);
if (lean_obj_tag(x_1214) == 0)
{
lean_object* x_1215; 
x_1215 = lean_ctor_get(x_1214, 0);
lean_inc(x_1215);
if (lean_obj_tag(x_1215) == 0)
{
lean_object* x_1216; lean_object* x_1217; 
x_1216 = lean_ctor_get(x_1214, 1);
lean_inc(x_1216);
lean_dec_ref(x_1214);
lean_inc(x_1206);
lean_inc_ref(x_1208);
lean_inc(x_1204);
lean_inc_ref(x_1211);
lean_inc_ref(x_1209);
x_1217 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1209, x_1210, x_1207, x_1211, x_1204, x_1208, x_1206, x_1216);
if (lean_obj_tag(x_1217) == 0)
{
lean_object* x_1218; 
x_1218 = lean_ctor_get(x_1217, 0);
lean_inc(x_1218);
if (lean_obj_tag(x_1218) == 0)
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; 
x_1219 = lean_ctor_get(x_1217, 1);
lean_inc(x_1219);
lean_dec_ref(x_1217);
x_1220 = lean_ctor_get(x_1209, 0);
lean_inc(x_1220);
x_1221 = lean_ctor_get(x_1209, 3);
lean_inc(x_1221);
lean_inc(x_1221);
x_1222 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1221, x_1219);
x_1223 = lean_ctor_get(x_1222, 0);
lean_inc(x_1223);
if (lean_obj_tag(x_1223) == 0)
{
lean_object* x_1224; lean_object* x_1225; 
x_1224 = lean_ctor_get(x_1222, 1);
lean_inc(x_1224);
lean_dec_ref(x_1222);
lean_inc(x_1206);
lean_inc_ref(x_1208);
lean_inc(x_1204);
lean_inc_ref(x_1211);
lean_inc_ref(x_1212);
lean_inc(x_1207);
lean_inc_ref(x_1210);
lean_inc_ref(x_1179);
lean_inc_ref(x_1209);
x_1225 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1209, x_1179, x_1210, x_1207, x_1212, x_1211, x_1204, x_1208, x_1206, x_1224);
if (lean_obj_tag(x_1225) == 0)
{
lean_object* x_1226; 
x_1226 = lean_ctor_get(x_1225, 0);
lean_inc(x_1226);
if (lean_obj_tag(x_1226) == 0)
{
lean_object* x_1227; lean_object* x_1228; 
x_1227 = lean_ctor_get(x_1225, 1);
lean_inc(x_1227);
lean_dec_ref(x_1225);
lean_inc(x_1206);
lean_inc_ref(x_1208);
lean_inc(x_1204);
lean_inc_ref(x_1211);
lean_inc_ref(x_1212);
lean_inc(x_1207);
lean_inc_ref(x_1210);
x_1228 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_1221, x_1210, x_1207, x_1212, x_1211, x_1204, x_1208, x_1206, x_1227);
if (lean_obj_tag(x_1228) == 0)
{
lean_object* x_1229; 
x_1229 = lean_ctor_get(x_1228, 0);
lean_inc(x_1229);
if (lean_obj_tag(x_1229) == 0)
{
lean_object* x_1230; lean_object* x_1231; 
x_1230 = lean_ctor_get(x_1228, 1);
lean_inc(x_1230);
lean_dec_ref(x_1228);
lean_inc(x_1206);
lean_inc_ref(x_1208);
lean_inc(x_1204);
lean_inc_ref(x_1211);
lean_inc_ref(x_1212);
lean_inc(x_1207);
lean_inc_ref(x_1210);
x_1231 = l_Lean_Compiler_LCNF_Simp_simp(x_1179, x_1210, x_1207, x_1212, x_1211, x_1204, x_1208, x_1206, x_1230);
if (lean_obj_tag(x_1231) == 0)
{
lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; uint8_t x_1236; 
x_1232 = lean_ctor_get(x_1231, 0);
lean_inc(x_1232);
x_1233 = lean_ctor_get(x_1231, 1);
lean_inc(x_1233);
lean_dec_ref(x_1231);
x_1234 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_1220, x_1207, x_1233);
lean_dec(x_1220);
x_1235 = lean_ctor_get(x_1234, 0);
lean_inc(x_1235);
x_1236 = lean_unbox(x_1235);
lean_dec(x_1235);
if (x_1236 == 0)
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; 
lean_dec_ref(x_1212);
lean_dec_ref(x_1211);
lean_dec_ref(x_1210);
lean_dec_ref(x_1208);
lean_dec(x_1206);
lean_dec_ref(x_1);
x_1237 = lean_ctor_get(x_1234, 1);
lean_inc(x_1237);
lean_dec_ref(x_1234);
x_1238 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1209, x_1207, x_1204, x_1237);
lean_dec(x_1204);
lean_dec(x_1207);
lean_dec_ref(x_1209);
x_1239 = lean_ctor_get(x_1238, 1);
lean_inc(x_1239);
if (lean_is_exclusive(x_1238)) {
 lean_ctor_release(x_1238, 0);
 lean_ctor_release(x_1238, 1);
 x_1240 = x_1238;
} else {
 lean_dec_ref(x_1238);
 x_1240 = lean_box(0);
}
if (lean_is_scalar(x_1240)) {
 x_1241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1241 = x_1240;
}
lean_ctor_set(x_1241, 0, x_1232);
lean_ctor_set(x_1241, 1, x_1239);
return x_1241;
}
else
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
x_1242 = lean_ctor_get(x_1234, 1);
lean_inc(x_1242);
lean_dec_ref(x_1234);
lean_inc_ref(x_1209);
x_1243 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_1209, x_1210, x_1207, x_1212, x_1211, x_1204, x_1208, x_1206, x_1242);
lean_dec(x_1206);
lean_dec_ref(x_1208);
lean_dec(x_1204);
lean_dec_ref(x_1211);
lean_dec_ref(x_1212);
lean_dec(x_1207);
lean_dec_ref(x_1210);
x_1244 = lean_ctor_get(x_1243, 1);
lean_inc(x_1244);
if (lean_is_exclusive(x_1243)) {
 lean_ctor_release(x_1243, 0);
 lean_ctor_release(x_1243, 1);
 x_1245 = x_1243;
} else {
 lean_dec_ref(x_1243);
 x_1245 = lean_box(0);
}
x_1246 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_1209, x_1232);
lean_dec_ref(x_1);
if (lean_is_scalar(x_1245)) {
 x_1247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1247 = x_1245;
}
lean_ctor_set(x_1247, 0, x_1246);
lean_ctor_set(x_1247, 1, x_1244);
return x_1247;
}
}
else
{
lean_dec(x_1220);
lean_dec_ref(x_1212);
lean_dec_ref(x_1211);
lean_dec_ref(x_1210);
lean_dec_ref(x_1209);
lean_dec_ref(x_1208);
lean_dec(x_1207);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec_ref(x_1);
return x_1231;
}
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; 
lean_dec_ref(x_1);
x_1248 = lean_ctor_get(x_1229, 0);
lean_inc(x_1248);
lean_dec_ref(x_1229);
x_1249 = lean_ctor_get(x_1228, 1);
lean_inc(x_1249);
lean_dec_ref(x_1228);
x_1250 = lean_ctor_get(x_1248, 0);
lean_inc(x_1250);
x_1251 = lean_ctor_get(x_1248, 1);
lean_inc(x_1251);
lean_dec(x_1248);
x_1252 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1220, x_1251, x_1207, x_1204, x_1208, x_1206, x_1249);
if (lean_obj_tag(x_1252) == 0)
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1253 = lean_ctor_get(x_1252, 1);
lean_inc(x_1253);
lean_dec_ref(x_1252);
x_1254 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1209, x_1207, x_1204, x_1253);
lean_dec_ref(x_1209);
x_1255 = lean_ctor_get(x_1254, 1);
lean_inc(x_1255);
lean_dec_ref(x_1254);
lean_inc(x_1206);
lean_inc_ref(x_1208);
lean_inc(x_1204);
lean_inc_ref(x_1211);
lean_inc_ref(x_1212);
lean_inc(x_1207);
lean_inc_ref(x_1210);
x_1256 = l_Lean_Compiler_LCNF_Simp_simp(x_1179, x_1210, x_1207, x_1212, x_1211, x_1204, x_1208, x_1206, x_1255);
if (lean_obj_tag(x_1256) == 0)
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; 
x_1257 = lean_ctor_get(x_1256, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1256, 1);
lean_inc(x_1258);
lean_dec_ref(x_1256);
x_1259 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1250, x_1257, x_1210, x_1207, x_1212, x_1211, x_1204, x_1208, x_1206, x_1258);
lean_dec(x_1206);
lean_dec_ref(x_1208);
lean_dec(x_1204);
lean_dec_ref(x_1211);
lean_dec_ref(x_1212);
lean_dec(x_1207);
lean_dec_ref(x_1210);
lean_dec(x_1250);
return x_1259;
}
else
{
lean_dec(x_1250);
lean_dec_ref(x_1212);
lean_dec_ref(x_1211);
lean_dec_ref(x_1210);
lean_dec_ref(x_1208);
lean_dec(x_1207);
lean_dec(x_1206);
lean_dec(x_1204);
return x_1256;
}
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
lean_dec(x_1250);
lean_dec_ref(x_1212);
lean_dec_ref(x_1211);
lean_dec_ref(x_1210);
lean_dec_ref(x_1209);
lean_dec_ref(x_1208);
lean_dec(x_1207);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec_ref(x_1179);
x_1260 = lean_ctor_get(x_1252, 0);
lean_inc(x_1260);
x_1261 = lean_ctor_get(x_1252, 1);
lean_inc(x_1261);
if (lean_is_exclusive(x_1252)) {
 lean_ctor_release(x_1252, 0);
 lean_ctor_release(x_1252, 1);
 x_1262 = x_1252;
} else {
 lean_dec_ref(x_1252);
 x_1262 = lean_box(0);
}
if (lean_is_scalar(x_1262)) {
 x_1263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1263 = x_1262;
}
lean_ctor_set(x_1263, 0, x_1260);
lean_ctor_set(x_1263, 1, x_1261);
return x_1263;
}
}
}
else
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
lean_dec(x_1220);
lean_dec_ref(x_1212);
lean_dec_ref(x_1211);
lean_dec_ref(x_1210);
lean_dec_ref(x_1209);
lean_dec_ref(x_1208);
lean_dec(x_1207);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec_ref(x_1179);
lean_dec_ref(x_1);
x_1264 = lean_ctor_get(x_1228, 0);
lean_inc(x_1264);
x_1265 = lean_ctor_get(x_1228, 1);
lean_inc(x_1265);
if (lean_is_exclusive(x_1228)) {
 lean_ctor_release(x_1228, 0);
 lean_ctor_release(x_1228, 1);
 x_1266 = x_1228;
} else {
 lean_dec_ref(x_1228);
 x_1266 = lean_box(0);
}
if (lean_is_scalar(x_1266)) {
 x_1267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1267 = x_1266;
}
lean_ctor_set(x_1267, 0, x_1264);
lean_ctor_set(x_1267, 1, x_1265);
return x_1267;
}
}
else
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; 
lean_dec(x_1221);
lean_dec(x_1220);
lean_dec_ref(x_1212);
lean_dec_ref(x_1211);
lean_dec_ref(x_1210);
lean_dec_ref(x_1208);
lean_dec(x_1206);
lean_dec_ref(x_1179);
lean_dec_ref(x_1);
x_1268 = lean_ctor_get(x_1225, 1);
lean_inc(x_1268);
lean_dec_ref(x_1225);
x_1269 = lean_ctor_get(x_1226, 0);
lean_inc(x_1269);
lean_dec_ref(x_1226);
x_1270 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1209, x_1207, x_1204, x_1268);
lean_dec(x_1204);
lean_dec(x_1207);
lean_dec_ref(x_1209);
x_1271 = lean_ctor_get(x_1270, 1);
lean_inc(x_1271);
if (lean_is_exclusive(x_1270)) {
 lean_ctor_release(x_1270, 0);
 lean_ctor_release(x_1270, 1);
 x_1272 = x_1270;
} else {
 lean_dec_ref(x_1270);
 x_1272 = lean_box(0);
}
if (lean_is_scalar(x_1272)) {
 x_1273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1273 = x_1272;
}
lean_ctor_set(x_1273, 0, x_1269);
lean_ctor_set(x_1273, 1, x_1271);
return x_1273;
}
}
else
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; 
lean_dec(x_1221);
lean_dec(x_1220);
lean_dec_ref(x_1212);
lean_dec_ref(x_1211);
lean_dec_ref(x_1210);
lean_dec_ref(x_1209);
lean_dec_ref(x_1208);
lean_dec(x_1207);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec_ref(x_1179);
lean_dec_ref(x_1);
x_1274 = lean_ctor_get(x_1225, 0);
lean_inc(x_1274);
x_1275 = lean_ctor_get(x_1225, 1);
lean_inc(x_1275);
if (lean_is_exclusive(x_1225)) {
 lean_ctor_release(x_1225, 0);
 lean_ctor_release(x_1225, 1);
 x_1276 = x_1225;
} else {
 lean_dec_ref(x_1225);
 x_1276 = lean_box(0);
}
if (lean_is_scalar(x_1276)) {
 x_1277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1277 = x_1276;
}
lean_ctor_set(x_1277, 0, x_1274);
lean_ctor_set(x_1277, 1, x_1275);
return x_1277;
}
}
else
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
lean_dec(x_1221);
lean_dec_ref(x_1);
x_1278 = lean_ctor_get(x_1222, 1);
lean_inc(x_1278);
lean_dec_ref(x_1222);
x_1279 = lean_ctor_get(x_1223, 0);
lean_inc(x_1279);
lean_dec_ref(x_1223);
x_1280 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1220, x_1279, x_1207, x_1204, x_1208, x_1206, x_1278);
if (lean_obj_tag(x_1280) == 0)
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
x_1281 = lean_ctor_get(x_1280, 1);
lean_inc(x_1281);
lean_dec_ref(x_1280);
x_1282 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1209, x_1207, x_1204, x_1281);
lean_dec_ref(x_1209);
x_1283 = lean_ctor_get(x_1282, 1);
lean_inc(x_1283);
lean_dec_ref(x_1282);
x_1 = x_1179;
x_2 = x_1210;
x_3 = x_1207;
x_4 = x_1212;
x_5 = x_1211;
x_6 = x_1204;
x_7 = x_1208;
x_8 = x_1206;
x_9 = x_1283;
goto _start;
}
else
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
lean_dec_ref(x_1212);
lean_dec_ref(x_1211);
lean_dec_ref(x_1210);
lean_dec_ref(x_1209);
lean_dec_ref(x_1208);
lean_dec(x_1207);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec_ref(x_1179);
x_1285 = lean_ctor_get(x_1280, 0);
lean_inc(x_1285);
x_1286 = lean_ctor_get(x_1280, 1);
lean_inc(x_1286);
if (lean_is_exclusive(x_1280)) {
 lean_ctor_release(x_1280, 0);
 lean_ctor_release(x_1280, 1);
 x_1287 = x_1280;
} else {
 lean_dec_ref(x_1280);
 x_1287 = lean_box(0);
}
if (lean_is_scalar(x_1287)) {
 x_1288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1288 = x_1287;
}
lean_ctor_set(x_1288, 0, x_1285);
lean_ctor_set(x_1288, 1, x_1286);
return x_1288;
}
}
}
else
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; 
lean_dec_ref(x_1209);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1289 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1289 = lean_box(0);
}
x_1290 = lean_ctor_get(x_1217, 1);
lean_inc(x_1290);
lean_dec_ref(x_1217);
x_1291 = lean_ctor_get(x_1218, 0);
lean_inc(x_1291);
lean_dec_ref(x_1218);
if (lean_is_scalar(x_1289)) {
 x_1292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1292 = x_1289;
 lean_ctor_set_tag(x_1292, 1);
}
lean_ctor_set(x_1292, 0, x_1291);
lean_ctor_set(x_1292, 1, x_1179);
x_1 = x_1292;
x_2 = x_1210;
x_3 = x_1207;
x_4 = x_1212;
x_5 = x_1211;
x_6 = x_1204;
x_7 = x_1208;
x_8 = x_1206;
x_9 = x_1290;
goto _start;
}
}
else
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
lean_dec_ref(x_1212);
lean_dec_ref(x_1211);
lean_dec_ref(x_1210);
lean_dec_ref(x_1209);
lean_dec_ref(x_1208);
lean_dec(x_1207);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec_ref(x_1179);
lean_dec_ref(x_1);
x_1294 = lean_ctor_get(x_1217, 0);
lean_inc(x_1294);
x_1295 = lean_ctor_get(x_1217, 1);
lean_inc(x_1295);
if (lean_is_exclusive(x_1217)) {
 lean_ctor_release(x_1217, 0);
 lean_ctor_release(x_1217, 1);
 x_1296 = x_1217;
} else {
 lean_dec_ref(x_1217);
 x_1296 = lean_box(0);
}
if (lean_is_scalar(x_1296)) {
 x_1297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1297 = x_1296;
}
lean_ctor_set(x_1297, 0, x_1294);
lean_ctor_set(x_1297, 1, x_1295);
return x_1297;
}
}
else
{
lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
lean_dec_ref(x_1209);
lean_dec_ref(x_1);
x_1298 = lean_ctor_get(x_1214, 1);
lean_inc(x_1298);
lean_dec_ref(x_1214);
x_1299 = lean_ctor_get(x_1215, 0);
lean_inc(x_1299);
lean_dec_ref(x_1215);
x_1300 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1207, x_1298);
x_1301 = lean_ctor_get(x_1300, 1);
lean_inc(x_1301);
lean_dec_ref(x_1300);
lean_inc(x_1206);
lean_inc_ref(x_1208);
lean_inc(x_1204);
lean_inc_ref(x_1211);
lean_inc_ref(x_1212);
lean_inc(x_1207);
lean_inc_ref(x_1210);
x_1302 = l_Lean_Compiler_LCNF_Simp_simp(x_1179, x_1210, x_1207, x_1212, x_1211, x_1204, x_1208, x_1206, x_1301);
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; 
x_1303 = lean_ctor_get(x_1302, 0);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1302, 1);
lean_inc(x_1304);
lean_dec_ref(x_1302);
x_1305 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1299, x_1303, x_1210, x_1207, x_1212, x_1211, x_1204, x_1208, x_1206, x_1304);
lean_dec(x_1206);
lean_dec_ref(x_1208);
lean_dec(x_1204);
lean_dec_ref(x_1211);
lean_dec_ref(x_1212);
lean_dec(x_1207);
lean_dec_ref(x_1210);
lean_dec(x_1299);
return x_1305;
}
else
{
lean_dec(x_1299);
lean_dec_ref(x_1212);
lean_dec_ref(x_1211);
lean_dec_ref(x_1210);
lean_dec_ref(x_1208);
lean_dec(x_1207);
lean_dec(x_1206);
lean_dec(x_1204);
return x_1302;
}
}
}
else
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; 
lean_dec_ref(x_1212);
lean_dec_ref(x_1211);
lean_dec_ref(x_1210);
lean_dec_ref(x_1209);
lean_dec_ref(x_1208);
lean_dec(x_1207);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec_ref(x_1179);
lean_dec_ref(x_1);
x_1306 = lean_ctor_get(x_1214, 0);
lean_inc(x_1306);
x_1307 = lean_ctor_get(x_1214, 1);
lean_inc(x_1307);
if (lean_is_exclusive(x_1214)) {
 lean_ctor_release(x_1214, 0);
 lean_ctor_release(x_1214, 1);
 x_1308 = x_1214;
} else {
 lean_dec_ref(x_1214);
 x_1308 = lean_box(0);
}
if (lean_is_scalar(x_1308)) {
 x_1309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1309 = x_1308;
}
lean_ctor_set(x_1309, 0, x_1306);
lean_ctor_set(x_1309, 1, x_1307);
return x_1309;
}
}
else
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; uint8_t x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; uint64_t x_1327; uint64_t x_1328; uint64_t x_1329; uint64_t x_1330; uint64_t x_1331; uint64_t x_1332; uint64_t x_1333; size_t x_1334; size_t x_1335; size_t x_1336; size_t x_1337; size_t x_1338; lean_object* x_1339; uint8_t x_1340; 
lean_dec_ref(x_1);
x_1310 = lean_st_ref_take(x_1207, x_1205);
x_1311 = lean_ctor_get(x_1310, 0);
lean_inc(x_1311);
x_1312 = lean_ctor_get(x_1311, 0);
lean_inc_ref(x_1312);
x_1313 = lean_ctor_get(x_1310, 1);
lean_inc(x_1313);
lean_dec_ref(x_1310);
x_1314 = lean_ctor_get(x_1311, 1);
lean_inc_ref(x_1314);
x_1315 = lean_ctor_get(x_1311, 2);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1311, 3);
lean_inc_ref(x_1316);
x_1317 = lean_ctor_get_uint8(x_1311, sizeof(void*)*7);
x_1318 = lean_ctor_get(x_1311, 4);
lean_inc(x_1318);
x_1319 = lean_ctor_get(x_1311, 5);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1311, 6);
lean_inc(x_1320);
lean_dec(x_1311);
x_1321 = lean_ctor_get(x_1312, 0);
lean_inc(x_1321);
x_1322 = lean_ctor_get(x_1312, 1);
lean_inc_ref(x_1322);
if (lean_is_exclusive(x_1312)) {
 lean_ctor_release(x_1312, 0);
 lean_ctor_release(x_1312, 1);
 x_1323 = x_1312;
} else {
 lean_dec_ref(x_1312);
 x_1323 = lean_box(0);
}
x_1324 = lean_ctor_get(x_1209, 0);
lean_inc(x_1324);
x_1325 = lean_box(0);
x_1326 = lean_array_get_size(x_1322);
x_1327 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_1324);
x_1328 = 32;
x_1329 = lean_uint64_shift_right(x_1327, x_1328);
x_1330 = lean_uint64_xor(x_1327, x_1329);
x_1331 = 16;
x_1332 = lean_uint64_shift_right(x_1330, x_1331);
x_1333 = lean_uint64_xor(x_1330, x_1332);
x_1334 = lean_uint64_to_usize(x_1333);
x_1335 = lean_usize_of_nat(x_1326);
lean_dec(x_1326);
x_1336 = 1;
x_1337 = lean_usize_sub(x_1335, x_1336);
x_1338 = lean_usize_land(x_1334, x_1337);
x_1339 = lean_array_uget(x_1322, x_1338);
x_1340 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1324, x_1339);
if (x_1340 == 0)
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; uint8_t x_1349; 
x_1341 = lean_nat_add(x_1321, x_1175);
lean_dec(x_1321);
x_1342 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1342, 0, x_1324);
lean_ctor_set(x_1342, 1, x_1325);
lean_ctor_set(x_1342, 2, x_1339);
x_1343 = lean_array_uset(x_1322, x_1338, x_1342);
x_1344 = lean_unsigned_to_nat(4u);
x_1345 = lean_nat_mul(x_1341, x_1344);
x_1346 = lean_unsigned_to_nat(3u);
x_1347 = lean_nat_div(x_1345, x_1346);
lean_dec(x_1345);
x_1348 = lean_array_get_size(x_1343);
x_1349 = lean_nat_dec_le(x_1347, x_1348);
lean_dec(x_1348);
lean_dec(x_1347);
if (x_1349 == 0)
{
lean_object* x_1350; lean_object* x_1351; 
x_1350 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_1343);
if (lean_is_scalar(x_1323)) {
 x_1351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1351 = x_1323;
}
lean_ctor_set(x_1351, 0, x_1341);
lean_ctor_set(x_1351, 1, x_1350);
x_1180 = x_1204;
x_1181 = x_1206;
x_1182 = x_1208;
x_1183 = x_1207;
x_1184 = x_1209;
x_1185 = x_1314;
x_1186 = x_1315;
x_1187 = x_1316;
x_1188 = x_1317;
x_1189 = x_1318;
x_1190 = x_1319;
x_1191 = x_1320;
x_1192 = x_1211;
x_1193 = x_1210;
x_1194 = x_1313;
x_1195 = x_1212;
x_1196 = x_1351;
goto block_1203;
}
else
{
lean_object* x_1352; 
if (lean_is_scalar(x_1323)) {
 x_1352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1352 = x_1323;
}
lean_ctor_set(x_1352, 0, x_1341);
lean_ctor_set(x_1352, 1, x_1343);
x_1180 = x_1204;
x_1181 = x_1206;
x_1182 = x_1208;
x_1183 = x_1207;
x_1184 = x_1209;
x_1185 = x_1314;
x_1186 = x_1315;
x_1187 = x_1316;
x_1188 = x_1317;
x_1189 = x_1318;
x_1190 = x_1319;
x_1191 = x_1320;
x_1192 = x_1211;
x_1193 = x_1210;
x_1194 = x_1313;
x_1195 = x_1212;
x_1196 = x_1352;
goto block_1203;
}
}
else
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; 
x_1353 = lean_box(0);
x_1354 = lean_array_uset(x_1322, x_1338, x_1353);
x_1355 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_1324, x_1325, x_1339);
x_1356 = lean_array_uset(x_1354, x_1338, x_1355);
if (lean_is_scalar(x_1323)) {
 x_1357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1357 = x_1323;
}
lean_ctor_set(x_1357, 0, x_1321);
lean_ctor_set(x_1357, 1, x_1356);
x_1180 = x_1204;
x_1181 = x_1206;
x_1182 = x_1208;
x_1183 = x_1207;
x_1184 = x_1209;
x_1185 = x_1314;
x_1186 = x_1315;
x_1187 = x_1316;
x_1188 = x_1317;
x_1189 = x_1318;
x_1190 = x_1319;
x_1191 = x_1320;
x_1192 = x_1211;
x_1193 = x_1210;
x_1194 = x_1313;
x_1195 = x_1212;
x_1196 = x_1357;
goto block_1203;
}
}
}
block_1373:
{
uint8_t x_1370; 
x_1370 = l_Lean_Expr_isErased(x_1360);
lean_dec_ref(x_1360);
if (x_1370 == 0)
{
lean_dec(x_1361);
x_1204 = x_1366;
x_1205 = x_1369;
x_1206 = x_1368;
x_1207 = x_1363;
x_1208 = x_1367;
x_1209 = x_1359;
x_1210 = x_1362;
x_1211 = x_1365;
x_1212 = x_1364;
x_1213 = x_1117;
goto block_1358;
}
else
{
lean_object* x_1371; uint8_t x_1372; 
x_1371 = lean_box(1);
x_1372 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1209_(x_1361, x_1371);
lean_dec(x_1361);
if (x_1372 == 0)
{
x_1204 = x_1366;
x_1205 = x_1369;
x_1206 = x_1368;
x_1207 = x_1363;
x_1208 = x_1367;
x_1209 = x_1359;
x_1210 = x_1362;
x_1211 = x_1365;
x_1212 = x_1364;
x_1213 = x_1370;
goto block_1358;
}
else
{
x_1204 = x_1366;
x_1205 = x_1369;
x_1206 = x_1368;
x_1207 = x_1363;
x_1208 = x_1367;
x_1209 = x_1359;
x_1210 = x_1362;
x_1211 = x_1365;
x_1212 = x_1364;
x_1213 = x_1117;
goto block_1358;
}
}
}
block_1403:
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
x_1385 = lean_ctor_get(x_1375, 2);
lean_inc_ref(x_1385);
x_1386 = lean_ctor_get(x_1375, 3);
lean_inc(x_1386);
lean_inc(x_1383);
lean_inc_ref(x_1382);
lean_inc(x_1381);
lean_inc_ref(x_1380);
lean_inc_ref(x_1379);
lean_inc(x_1386);
x_1387 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_1386, x_1377, x_1379, x_1380, x_1381, x_1382, x_1383, x_1384);
if (lean_obj_tag(x_1387) == 0)
{
lean_object* x_1388; 
x_1388 = lean_ctor_get(x_1387, 0);
lean_inc(x_1388);
if (lean_obj_tag(x_1388) == 0)
{
lean_object* x_1389; 
x_1389 = lean_ctor_get(x_1387, 1);
lean_inc(x_1389);
lean_dec_ref(x_1387);
x_1359 = x_1375;
x_1360 = x_1385;
x_1361 = x_1386;
x_1362 = x_1377;
x_1363 = x_1378;
x_1364 = x_1379;
x_1365 = x_1380;
x_1366 = x_1381;
x_1367 = x_1382;
x_1368 = x_1383;
x_1369 = x_1389;
goto block_1373;
}
else
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
lean_dec(x_1386);
lean_dec_ref(x_1385);
x_1390 = lean_ctor_get(x_1387, 1);
lean_inc(x_1390);
lean_dec_ref(x_1387);
x_1391 = lean_ctor_get(x_1388, 0);
lean_inc(x_1391);
lean_dec_ref(x_1388);
x_1392 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1378, x_1390);
x_1393 = lean_ctor_get(x_1392, 1);
lean_inc(x_1393);
lean_dec_ref(x_1392);
x_1394 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_1375, x_1391, x_1381, x_1393);
x_1395 = lean_ctor_get(x_1394, 0);
lean_inc(x_1395);
x_1396 = lean_ctor_get(x_1394, 1);
lean_inc(x_1396);
lean_dec_ref(x_1394);
x_1397 = lean_ctor_get(x_1395, 2);
lean_inc_ref(x_1397);
x_1398 = lean_ctor_get(x_1395, 3);
lean_inc(x_1398);
x_1359 = x_1395;
x_1360 = x_1397;
x_1361 = x_1398;
x_1362 = x_1377;
x_1363 = x_1378;
x_1364 = x_1379;
x_1365 = x_1380;
x_1366 = x_1381;
x_1367 = x_1382;
x_1368 = x_1383;
x_1369 = x_1396;
goto block_1373;
}
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; 
lean_dec(x_1386);
lean_dec_ref(x_1385);
lean_dec(x_1383);
lean_dec_ref(x_1382);
lean_dec(x_1381);
lean_dec_ref(x_1380);
lean_dec_ref(x_1379);
lean_dec(x_1378);
lean_dec_ref(x_1377);
lean_dec(x_1375);
lean_dec_ref(x_1179);
lean_dec_ref(x_1);
x_1399 = lean_ctor_get(x_1387, 0);
lean_inc(x_1399);
x_1400 = lean_ctor_get(x_1387, 1);
lean_inc(x_1400);
if (lean_is_exclusive(x_1387)) {
 lean_ctor_release(x_1387, 0);
 lean_ctor_release(x_1387, 1);
 x_1401 = x_1387;
} else {
 lean_dec_ref(x_1387);
 x_1401 = lean_box(0);
}
if (lean_is_scalar(x_1401)) {
 x_1402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1402 = x_1401;
}
lean_ctor_set(x_1402, 0, x_1399);
lean_ctor_set(x_1402, 1, x_1400);
return x_1402;
}
}
block_1406:
{
lean_object* x_1404; lean_object* x_1405; 
x_1404 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_1376);
x_1405 = lean_ctor_get(x_1404, 1);
lean_inc(x_1405);
lean_dec_ref(x_1404);
x_1377 = x_2;
x_1378 = x_3;
x_1379 = x_4;
x_1380 = x_5;
x_1381 = x_6;
x_1382 = x_1177;
x_1383 = x_8;
x_1384 = x_1405;
goto block_1403;
}
}
case 3:
{
lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; 
lean_dec_ref(x_67);
x_1408 = lean_ctor_get(x_1, 0);
lean_inc(x_1408);
x_1409 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1409);
x_1410 = lean_st_ref_get(x_3, x_1120);
x_1411 = lean_ctor_get(x_1410, 0);
lean_inc(x_1411);
x_1412 = lean_ctor_get(x_1410, 1);
lean_inc(x_1412);
lean_dec_ref(x_1410);
x_1413 = lean_ctor_get(x_1411, 0);
lean_inc_ref(x_1413);
lean_dec(x_1411);
x_1414 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_1413, x_1408, x_1117);
lean_dec_ref(x_1413);
if (lean_obj_tag(x_1414) == 0)
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1424; 
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
lean_dec_ref(x_1414);
x_1416 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_1117, x_1409, x_3, x_1412);
x_1417 = lean_ctor_get(x_1416, 0);
lean_inc(x_1417);
x_1418 = lean_ctor_get(x_1416, 1);
lean_inc(x_1418);
if (lean_is_exclusive(x_1416)) {
 lean_ctor_release(x_1416, 0);
 lean_ctor_release(x_1416, 1);
 x_1419 = x_1416;
} else {
 lean_dec_ref(x_1416);
 x_1419 = lean_box(0);
}
lean_inc(x_1417);
x_1424 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1415, x_1417, x_2, x_3, x_4, x_5, x_6, x_1177, x_8, x_1418);
if (lean_obj_tag(x_1424) == 0)
{
lean_object* x_1425; 
x_1425 = lean_ctor_get(x_1424, 0);
lean_inc(x_1425);
if (lean_obj_tag(x_1425) == 0)
{
lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; uint8_t x_1431; 
lean_dec_ref(x_1177);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1426 = lean_ctor_get(x_1424, 1);
lean_inc(x_1426);
lean_dec_ref(x_1424);
lean_inc(x_1415);
x_1427 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1415, x_3, x_1426);
x_1428 = lean_ctor_get(x_1427, 1);
lean_inc(x_1428);
lean_dec_ref(x_1427);
x_1429 = lean_unsigned_to_nat(0u);
x_1430 = lean_array_get_size(x_1417);
x_1431 = lean_nat_dec_lt(x_1429, x_1430);
if (x_1431 == 0)
{
lean_dec(x_1430);
lean_dec(x_3);
x_1420 = x_1428;
goto block_1423;
}
else
{
uint8_t x_1432; 
x_1432 = lean_nat_dec_le(x_1430, x_1430);
if (x_1432 == 0)
{
lean_dec(x_1430);
lean_dec(x_3);
x_1420 = x_1428;
goto block_1423;
}
else
{
lean_object* x_1433; size_t x_1434; size_t x_1435; lean_object* x_1436; lean_object* x_1437; 
x_1433 = lean_box(0);
x_1434 = 0;
x_1435 = lean_usize_of_nat(x_1430);
lean_dec(x_1430);
x_1436 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1417, x_1434, x_1435, x_1433, x_3, x_1428);
lean_dec(x_3);
x_1437 = lean_ctor_get(x_1436, 1);
lean_inc(x_1437);
lean_dec_ref(x_1436);
x_1420 = x_1437;
goto block_1423;
}
}
}
else
{
lean_object* x_1438; lean_object* x_1439; 
lean_dec(x_1419);
lean_dec(x_1417);
lean_dec(x_1415);
lean_dec_ref(x_1);
x_1438 = lean_ctor_get(x_1424, 1);
lean_inc(x_1438);
lean_dec_ref(x_1424);
x_1439 = lean_ctor_get(x_1425, 0);
lean_inc(x_1439);
lean_dec_ref(x_1425);
x_1 = x_1439;
x_7 = x_1177;
x_9 = x_1438;
goto _start;
}
}
else
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; 
lean_dec(x_1419);
lean_dec(x_1417);
lean_dec(x_1415);
lean_dec_ref(x_1177);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1441 = lean_ctor_get(x_1424, 0);
lean_inc(x_1441);
x_1442 = lean_ctor_get(x_1424, 1);
lean_inc(x_1442);
if (lean_is_exclusive(x_1424)) {
 lean_ctor_release(x_1424, 0);
 lean_ctor_release(x_1424, 1);
 x_1443 = x_1424;
} else {
 lean_dec_ref(x_1424);
 x_1443 = lean_box(0);
}
if (lean_is_scalar(x_1443)) {
 x_1444 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1444 = x_1443;
}
lean_ctor_set(x_1444, 0, x_1441);
lean_ctor_set(x_1444, 1, x_1442);
return x_1444;
}
block_1423:
{
lean_object* x_1421; lean_object* x_1422; 
x_1421 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_1, x_1415, x_1417);
lean_dec_ref(x_1);
if (lean_is_scalar(x_1419)) {
 x_1422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1422 = x_1419;
}
lean_ctor_set(x_1422, 0, x_1421);
lean_ctor_set(x_1422, 1, x_1420);
return x_1422;
}
}
else
{
lean_object* x_1445; 
lean_dec_ref(x_1409);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1445 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1177, x_8, x_1412);
lean_dec(x_8);
lean_dec_ref(x_1177);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1445;
}
}
case 4:
{
lean_object* x_1446; lean_object* x_1447; 
x_1446 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1446);
lean_inc(x_8);
lean_inc_ref(x_1177);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1446);
x_1447 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1446, x_2, x_3, x_4, x_5, x_6, x_1177, x_8, x_1120);
if (lean_obj_tag(x_1447) == 0)
{
lean_object* x_1448; 
x_1448 = lean_ctor_get(x_1447, 0);
lean_inc(x_1448);
if (lean_obj_tag(x_1448) == 0)
{
lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
x_1449 = lean_ctor_get(x_1447, 1);
lean_inc(x_1449);
lean_dec_ref(x_1447);
x_1450 = lean_st_ref_get(x_3, x_1449);
x_1451 = lean_ctor_get(x_1450, 0);
lean_inc(x_1451);
x_1452 = lean_ctor_get(x_1450, 1);
lean_inc(x_1452);
lean_dec_ref(x_1450);
x_1453 = lean_ctor_get(x_1446, 1);
lean_inc_ref(x_1453);
x_1454 = lean_ctor_get(x_1446, 2);
lean_inc(x_1454);
x_1455 = lean_ctor_get(x_1446, 3);
lean_inc_ref(x_1455);
lean_dec_ref(x_1446);
x_1456 = lean_ctor_get(x_1451, 0);
lean_inc_ref(x_1456);
lean_dec(x_1451);
x_1457 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_1456, x_1454, x_1117);
lean_dec_ref(x_1456);
if (lean_obj_tag(x_1457) == 0)
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; 
x_1458 = lean_ctor_get(x_1457, 0);
lean_inc(x_1458);
lean_dec_ref(x_1457);
x_1459 = lean_st_ref_get(x_3, x_1452);
x_1460 = lean_ctor_get(x_1459, 0);
lean_inc(x_1460);
x_1461 = lean_ctor_get(x_1459, 1);
lean_inc(x_1461);
lean_dec_ref(x_1459);
x_1462 = lean_box(x_1117);
lean_inc(x_1458);
x_1463 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__1___boxed), 11, 2);
lean_closure_set(x_1463, 0, x_1458);
lean_closure_set(x_1463, 1, x_1462);
x_1464 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_67, x_1455, x_1463);
lean_inc(x_8);
lean_inc_ref(x_1177);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_1465 = lean_apply_8(x_1464, x_2, x_3, x_4, x_5, x_6, x_1177, x_8, x_1461);
if (lean_obj_tag(x_1465) == 0)
{
lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; 
x_1466 = lean_ctor_get(x_1465, 0);
lean_inc(x_1466);
x_1467 = lean_ctor_get(x_1465, 1);
lean_inc(x_1467);
lean_dec_ref(x_1465);
lean_inc(x_6);
lean_inc(x_3);
x_1468 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1466, x_2, x_3, x_4, x_5, x_6, x_1177, x_8, x_1467);
if (lean_obj_tag(x_1468) == 0)
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1482; uint8_t x_1483; 
x_1469 = lean_ctor_get(x_1468, 0);
lean_inc(x_1469);
x_1470 = lean_ctor_get(x_1468, 1);
lean_inc(x_1470);
if (lean_is_exclusive(x_1468)) {
 lean_ctor_release(x_1468, 0);
 lean_ctor_release(x_1468, 1);
 x_1471 = x_1468;
} else {
 lean_dec_ref(x_1468);
 x_1471 = lean_box(0);
}
x_1472 = lean_ctor_get(x_1460, 0);
lean_inc_ref(x_1472);
lean_dec(x_1460);
x_1473 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1472, x_1117, x_1453);
lean_dec_ref(x_1472);
x_1482 = lean_array_get_size(x_1469);
x_1483 = lean_nat_dec_eq(x_1482, x_1175);
lean_dec(x_1482);
if (x_1483 == 0)
{
lean_dec(x_1471);
lean_dec(x_6);
x_1474 = x_3;
x_1475 = x_1470;
goto block_1481;
}
else
{
lean_object* x_1484; lean_object* x_1485; 
x_1484 = lean_unsigned_to_nat(0u);
x_1485 = lean_array_fget(x_1469, x_1484);
if (lean_obj_tag(x_1485) == 0)
{
lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1494; lean_object* x_1495; uint8_t x_1504; lean_object* x_1505; uint8_t x_1507; 
lean_dec(x_1471);
x_1486 = lean_ctor_get(x_1485, 1);
lean_inc_ref(x_1486);
x_1487 = lean_ctor_get(x_1485, 2);
lean_inc_ref(x_1487);
lean_dec_ref(x_1485);
x_1494 = lean_array_get_size(x_1486);
x_1507 = lean_nat_dec_lt(x_1484, x_1494);
if (x_1507 == 0)
{
x_1504 = x_1117;
x_1505 = x_1470;
goto block_1506;
}
else
{
if (x_1507 == 0)
{
x_1504 = x_1117;
x_1505 = x_1470;
goto block_1506;
}
else
{
size_t x_1508; size_t x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; uint8_t x_1513; 
x_1508 = 0;
x_1509 = lean_usize_of_nat(x_1494);
x_1510 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1486, x_1508, x_1509, x_3, x_1470);
x_1511 = lean_ctor_get(x_1510, 0);
lean_inc(x_1511);
x_1512 = lean_ctor_get(x_1510, 1);
lean_inc(x_1512);
lean_dec_ref(x_1510);
x_1513 = lean_unbox(x_1511);
lean_dec(x_1511);
x_1504 = x_1513;
x_1505 = x_1512;
goto block_1506;
}
}
block_1493:
{
lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; 
x_1489 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_1488);
lean_dec(x_3);
x_1490 = lean_ctor_get(x_1489, 1);
lean_inc(x_1490);
if (lean_is_exclusive(x_1489)) {
 lean_ctor_release(x_1489, 0);
 lean_ctor_release(x_1489, 1);
 x_1491 = x_1489;
} else {
 lean_dec_ref(x_1489);
 x_1491 = lean_box(0);
}
if (lean_is_scalar(x_1491)) {
 x_1492 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1492 = x_1491;
}
lean_ctor_set(x_1492, 0, x_1487);
lean_ctor_set(x_1492, 1, x_1490);
return x_1492;
}
block_1503:
{
uint8_t x_1496; 
x_1496 = lean_nat_dec_lt(x_1484, x_1494);
if (x_1496 == 0)
{
lean_dec(x_1494);
lean_dec_ref(x_1486);
lean_dec(x_6);
x_1488 = x_1495;
goto block_1493;
}
else
{
uint8_t x_1497; 
x_1497 = lean_nat_dec_le(x_1494, x_1494);
if (x_1497 == 0)
{
lean_dec(x_1494);
lean_dec_ref(x_1486);
lean_dec(x_6);
x_1488 = x_1495;
goto block_1493;
}
else
{
lean_object* x_1498; size_t x_1499; size_t x_1500; lean_object* x_1501; lean_object* x_1502; 
x_1498 = lean_box(0);
x_1499 = 0;
x_1500 = lean_usize_of_nat(x_1494);
lean_dec(x_1494);
x_1501 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1486, x_1499, x_1500, x_1498, x_6, x_1495);
lean_dec(x_6);
lean_dec_ref(x_1486);
x_1502 = lean_ctor_get(x_1501, 1);
lean_inc(x_1502);
lean_dec_ref(x_1501);
x_1488 = x_1502;
goto block_1493;
}
}
}
block_1506:
{
if (x_1504 == 0)
{
lean_dec_ref(x_1473);
lean_dec(x_1469);
lean_dec(x_1458);
lean_dec_ref(x_1);
x_1495 = x_1505;
goto block_1503;
}
else
{
if (x_1117 == 0)
{
lean_dec(x_1494);
lean_dec_ref(x_1487);
lean_dec_ref(x_1486);
lean_dec(x_6);
x_1474 = x_3;
x_1475 = x_1505;
goto block_1481;
}
else
{
lean_dec_ref(x_1473);
lean_dec(x_1469);
lean_dec(x_1458);
lean_dec_ref(x_1);
x_1495 = x_1505;
goto block_1503;
}
}
}
}
else
{
lean_object* x_1514; lean_object* x_1515; 
lean_dec_ref(x_1473);
lean_dec(x_1469);
lean_dec(x_1458);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1514 = lean_ctor_get(x_1485, 0);
lean_inc_ref(x_1514);
lean_dec_ref(x_1485);
if (lean_is_scalar(x_1471)) {
 x_1515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1515 = x_1471;
}
lean_ctor_set(x_1515, 0, x_1514);
lean_ctor_set(x_1515, 1, x_1470);
return x_1515;
}
}
block_1481:
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; 
lean_inc(x_1458);
x_1476 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1458, x_1474, x_1475);
lean_dec(x_1474);
x_1477 = lean_ctor_get(x_1476, 1);
lean_inc(x_1477);
if (lean_is_exclusive(x_1476)) {
 lean_ctor_release(x_1476, 0);
 lean_ctor_release(x_1476, 1);
 x_1478 = x_1476;
} else {
 lean_dec_ref(x_1476);
 x_1478 = lean_box(0);
}
x_1479 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_1, x_1473, x_1458, x_1469);
if (lean_is_scalar(x_1478)) {
 x_1480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1480 = x_1478;
}
lean_ctor_set(x_1480, 0, x_1479);
lean_ctor_set(x_1480, 1, x_1477);
return x_1480;
}
}
else
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; 
lean_dec(x_1460);
lean_dec(x_1458);
lean_dec_ref(x_1453);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1516 = lean_ctor_get(x_1468, 0);
lean_inc(x_1516);
x_1517 = lean_ctor_get(x_1468, 1);
lean_inc(x_1517);
if (lean_is_exclusive(x_1468)) {
 lean_ctor_release(x_1468, 0);
 lean_ctor_release(x_1468, 1);
 x_1518 = x_1468;
} else {
 lean_dec_ref(x_1468);
 x_1518 = lean_box(0);
}
if (lean_is_scalar(x_1518)) {
 x_1519 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1519 = x_1518;
}
lean_ctor_set(x_1519, 0, x_1516);
lean_ctor_set(x_1519, 1, x_1517);
return x_1519;
}
}
else
{
lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; 
lean_dec(x_1460);
lean_dec(x_1458);
lean_dec_ref(x_1453);
lean_dec_ref(x_1177);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1520 = lean_ctor_get(x_1465, 0);
lean_inc(x_1520);
x_1521 = lean_ctor_get(x_1465, 1);
lean_inc(x_1521);
if (lean_is_exclusive(x_1465)) {
 lean_ctor_release(x_1465, 0);
 lean_ctor_release(x_1465, 1);
 x_1522 = x_1465;
} else {
 lean_dec_ref(x_1465);
 x_1522 = lean_box(0);
}
if (lean_is_scalar(x_1522)) {
 x_1523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1523 = x_1522;
}
lean_ctor_set(x_1523, 0, x_1520);
lean_ctor_set(x_1523, 1, x_1521);
return x_1523;
}
}
else
{
lean_object* x_1524; 
lean_dec_ref(x_1455);
lean_dec_ref(x_1453);
lean_dec_ref(x_67);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1524 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1177, x_8, x_1452);
lean_dec(x_8);
lean_dec_ref(x_1177);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1524;
}
}
else
{
lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; 
lean_dec_ref(x_1446);
lean_dec_ref(x_1177);
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1525 = lean_ctor_get(x_1447, 1);
lean_inc(x_1525);
if (lean_is_exclusive(x_1447)) {
 lean_ctor_release(x_1447, 0);
 lean_ctor_release(x_1447, 1);
 x_1526 = x_1447;
} else {
 lean_dec_ref(x_1447);
 x_1526 = lean_box(0);
}
x_1527 = lean_ctor_get(x_1448, 0);
lean_inc(x_1527);
lean_dec_ref(x_1448);
if (lean_is_scalar(x_1526)) {
 x_1528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1528 = x_1526;
}
lean_ctor_set(x_1528, 0, x_1527);
lean_ctor_set(x_1528, 1, x_1525);
return x_1528;
}
}
else
{
lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; 
lean_dec_ref(x_1446);
lean_dec_ref(x_1177);
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1529 = lean_ctor_get(x_1447, 0);
lean_inc(x_1529);
x_1530 = lean_ctor_get(x_1447, 1);
lean_inc(x_1530);
if (lean_is_exclusive(x_1447)) {
 lean_ctor_release(x_1447, 0);
 lean_ctor_release(x_1447, 1);
 x_1531 = x_1447;
} else {
 lean_dec_ref(x_1447);
 x_1531 = lean_box(0);
}
if (lean_is_scalar(x_1531)) {
 x_1532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1532 = x_1531;
}
lean_ctor_set(x_1532, 0, x_1529);
lean_ctor_set(x_1532, 1, x_1530);
return x_1532;
}
}
case 5:
{
lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; 
lean_dec_ref(x_67);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1533 = lean_ctor_get(x_1, 0);
lean_inc(x_1533);
x_1534 = lean_st_ref_get(x_3, x_1120);
x_1535 = lean_ctor_get(x_1534, 0);
lean_inc(x_1535);
x_1536 = lean_ctor_get(x_1534, 1);
lean_inc(x_1536);
lean_dec_ref(x_1534);
x_1537 = lean_ctor_get(x_1535, 0);
lean_inc_ref(x_1537);
lean_dec(x_1535);
x_1538 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_1537, x_1533, x_1117);
lean_dec_ref(x_1537);
if (lean_obj_tag(x_1538) == 0)
{
lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; 
lean_dec_ref(x_1177);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1539 = lean_ctor_get(x_1538, 0);
lean_inc(x_1539);
lean_dec_ref(x_1538);
lean_inc(x_1539);
x_1540 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1539, x_3, x_1536);
lean_dec(x_3);
x_1541 = lean_ctor_get(x_1540, 1);
lean_inc(x_1541);
if (lean_is_exclusive(x_1540)) {
 lean_ctor_release(x_1540, 0);
 lean_ctor_release(x_1540, 1);
 x_1542 = x_1540;
} else {
 lean_dec_ref(x_1540);
 x_1542 = lean_box(0);
}
x_1543 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_1, x_1539);
if (lean_is_scalar(x_1542)) {
 x_1544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1544 = x_1542;
}
lean_ctor_set(x_1544, 0, x_1543);
lean_ctor_set(x_1544, 1, x_1541);
return x_1544;
}
else
{
lean_object* x_1545; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1545 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1177, x_8, x_1536);
lean_dec(x_8);
lean_dec_ref(x_1177);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1545;
}
}
case 6:
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; 
lean_dec_ref(x_1177);
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1546 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1546);
x_1547 = lean_st_ref_get(x_3, x_1120);
lean_dec(x_3);
x_1548 = lean_ctor_get(x_1547, 0);
lean_inc(x_1548);
x_1549 = lean_ctor_get(x_1547, 1);
lean_inc(x_1549);
if (lean_is_exclusive(x_1547)) {
 lean_ctor_release(x_1547, 0);
 lean_ctor_release(x_1547, 1);
 x_1550 = x_1547;
} else {
 lean_dec_ref(x_1547);
 x_1550 = lean_box(0);
}
x_1551 = lean_ctor_get(x_1548, 0);
lean_inc_ref(x_1551);
lean_dec(x_1548);
x_1552 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1551, x_1117, x_1546);
lean_dec_ref(x_1551);
x_1553 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(x_1, x_1552);
if (lean_is_scalar(x_1550)) {
 x_1554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1554 = x_1550;
}
lean_ctor_set(x_1554, 0, x_1553);
lean_ctor_set(x_1554, 1, x_1549);
return x_1554;
}
default: 
{
lean_object* x_1555; lean_object* x_1556; 
lean_dec_ref(x_67);
x_1555 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1555);
x_1556 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1556);
x_1121 = x_1555;
x_1122 = x_1556;
x_1123 = x_2;
x_1124 = x_3;
x_1125 = x_4;
x_1126 = x_5;
x_1127 = x_6;
x_1128 = x_1177;
x_1129 = x_8;
goto block_1174;
}
}
block_1174:
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; uint8_t x_1137; 
x_1130 = lean_ctor_get(x_1121, 0);
lean_inc(x_1130);
x_1131 = lean_ctor_get(x_1121, 2);
lean_inc_ref(x_1131);
x_1132 = lean_ctor_get(x_1121, 3);
lean_inc_ref(x_1132);
x_1133 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_1130, x_1124, x_1120);
lean_dec(x_1130);
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
x_1135 = lean_ctor_get(x_1133, 1);
lean_inc(x_1135);
lean_dec_ref(x_1133);
lean_inc(x_1134);
lean_inc_ref(x_1);
lean_inc_ref(x_1122);
x_1136 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_1136, 0, x_1122);
lean_closure_set(x_1136, 1, x_1);
lean_closure_set(x_1136, 2, x_1134);
x_1137 = lean_unbox(x_1134);
if (x_1137 == 0)
{
uint8_t x_1138; 
lean_dec(x_1134);
lean_dec_ref(x_1122);
x_1138 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_1138 == 0)
{
lean_dec_ref(x_1132);
lean_dec_ref(x_1131);
x_10 = x_1136;
x_11 = x_1121;
x_12 = x_1123;
x_13 = x_1124;
x_14 = x_1125;
x_15 = x_1126;
x_16 = x_1127;
x_17 = x_1128;
x_18 = x_1129;
x_19 = x_1135;
goto block_29;
}
else
{
uint8_t x_1139; 
x_1139 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_1132, x_1131);
lean_dec_ref(x_1131);
if (x_1139 == 0)
{
x_10 = x_1136;
x_11 = x_1121;
x_12 = x_1123;
x_13 = x_1124;
x_14 = x_1125;
x_15 = x_1126;
x_16 = x_1127;
x_17 = x_1128;
x_18 = x_1129;
x_19 = x_1135;
goto block_29;
}
else
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1140 = lean_st_ref_get(x_1124, x_1135);
x_1141 = lean_ctor_get(x_1140, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1140, 1);
lean_inc(x_1142);
lean_dec_ref(x_1140);
x_1143 = lean_ctor_get(x_1141, 0);
lean_inc_ref(x_1143);
lean_dec(x_1141);
lean_inc(x_1129);
lean_inc_ref(x_1128);
lean_inc(x_1127);
lean_inc_ref(x_1126);
x_1144 = l_Lean_Compiler_LCNF_normFunDeclImp(x_1117, x_1121, x_1143, x_1126, x_1127, x_1128, x_1129, x_1142);
if (lean_obj_tag(x_1144) == 0)
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1145 = lean_ctor_get(x_1144, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1144, 1);
lean_inc(x_1146);
lean_dec_ref(x_1144);
lean_inc(x_1129);
lean_inc_ref(x_1128);
lean_inc(x_1127);
lean_inc_ref(x_1126);
x_1147 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_1145, x_1126, x_1127, x_1128, x_1129, x_1146);
if (lean_obj_tag(x_1147) == 0)
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
x_1148 = lean_ctor_get(x_1147, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1147, 1);
lean_inc(x_1149);
lean_dec_ref(x_1147);
x_1150 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1124, x_1149);
x_1151 = lean_ctor_get(x_1150, 1);
lean_inc(x_1151);
lean_dec_ref(x_1150);
x_10 = x_1136;
x_11 = x_1148;
x_12 = x_1123;
x_13 = x_1124;
x_14 = x_1125;
x_15 = x_1126;
x_16 = x_1127;
x_17 = x_1128;
x_18 = x_1129;
x_19 = x_1151;
goto block_29;
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
lean_dec_ref(x_1136);
lean_dec(x_1129);
lean_dec_ref(x_1128);
lean_dec(x_1127);
lean_dec_ref(x_1126);
lean_dec_ref(x_1125);
lean_dec(x_1124);
lean_dec_ref(x_1123);
x_1152 = lean_ctor_get(x_1147, 0);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1147, 1);
lean_inc(x_1153);
if (lean_is_exclusive(x_1147)) {
 lean_ctor_release(x_1147, 0);
 lean_ctor_release(x_1147, 1);
 x_1154 = x_1147;
} else {
 lean_dec_ref(x_1147);
 x_1154 = lean_box(0);
}
if (lean_is_scalar(x_1154)) {
 x_1155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1155 = x_1154;
}
lean_ctor_set(x_1155, 0, x_1152);
lean_ctor_set(x_1155, 1, x_1153);
return x_1155;
}
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
lean_dec_ref(x_1136);
lean_dec(x_1129);
lean_dec_ref(x_1128);
lean_dec(x_1127);
lean_dec_ref(x_1126);
lean_dec_ref(x_1125);
lean_dec(x_1124);
lean_dec_ref(x_1123);
x_1156 = lean_ctor_get(x_1144, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1144, 1);
lean_inc(x_1157);
if (lean_is_exclusive(x_1144)) {
 lean_ctor_release(x_1144, 0);
 lean_ctor_release(x_1144, 1);
 x_1158 = x_1144;
} else {
 lean_dec_ref(x_1144);
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
}
else
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
lean_dec_ref(x_1136);
lean_dec_ref(x_1132);
lean_dec_ref(x_1131);
x_1160 = lean_st_ref_get(x_1124, x_1135);
x_1161 = lean_ctor_get(x_1160, 0);
lean_inc(x_1161);
x_1162 = lean_ctor_get(x_1160, 1);
lean_inc(x_1162);
lean_dec_ref(x_1160);
x_1163 = lean_ctor_get(x_1161, 0);
lean_inc_ref(x_1163);
lean_dec(x_1161);
lean_inc(x_1129);
lean_inc_ref(x_1128);
lean_inc(x_1127);
lean_inc_ref(x_1126);
x_1164 = l_Lean_Compiler_LCNF_normFunDeclImp(x_1117, x_1121, x_1163, x_1126, x_1127, x_1128, x_1129, x_1162);
if (lean_obj_tag(x_1164) == 0)
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; uint8_t x_1168; lean_object* x_1169; 
x_1165 = lean_ctor_get(x_1164, 0);
lean_inc(x_1165);
x_1166 = lean_ctor_get(x_1164, 1);
lean_inc(x_1166);
lean_dec_ref(x_1164);
x_1167 = lean_box(0);
x_1168 = lean_unbox(x_1134);
lean_dec(x_1134);
x_1169 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_1122, x_1, x_1168, x_1165, x_1167, x_1123, x_1124, x_1125, x_1126, x_1127, x_1128, x_1129, x_1166);
lean_dec_ref(x_1);
return x_1169;
}
else
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; 
lean_dec(x_1134);
lean_dec(x_1129);
lean_dec_ref(x_1128);
lean_dec(x_1127);
lean_dec_ref(x_1126);
lean_dec_ref(x_1125);
lean_dec(x_1124);
lean_dec_ref(x_1123);
lean_dec_ref(x_1122);
lean_dec_ref(x_1);
x_1170 = lean_ctor_get(x_1164, 0);
lean_inc(x_1170);
x_1171 = lean_ctor_get(x_1164, 1);
lean_inc(x_1171);
if (lean_is_exclusive(x_1164)) {
 lean_ctor_release(x_1164, 0);
 lean_ctor_release(x_1164, 1);
 x_1172 = x_1164;
} else {
 lean_dec_ref(x_1164);
 x_1172 = lean_box(0);
}
if (lean_is_scalar(x_1172)) {
 x_1173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1173 = x_1172;
}
lean_ctor_set(x_1173, 0, x_1170);
lean_ctor_set(x_1173, 1, x_1171);
return x_1173;
}
}
}
}
else
{
lean_object* x_1557; 
lean_dec_ref(x_1116);
lean_dec(x_1114);
lean_dec(x_1112);
lean_dec(x_1111);
lean_dec(x_1110);
lean_dec(x_1109);
lean_dec(x_1108);
lean_dec(x_1107);
lean_dec(x_1106);
lean_dec(x_1105);
lean_dec(x_1104);
lean_dec_ref(x_1103);
lean_dec_ref(x_1102);
lean_dec_ref(x_67);
lean_dec_ref(x_1);
x_1557 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1557;
}
}
}
else
{
lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; uint8_t x_1585; lean_object* x_1586; uint8_t x_1587; lean_object* x_1588; uint8_t x_1589; 
x_1558 = lean_ctor_get(x_67, 0);
lean_inc(x_1558);
lean_dec(x_67);
x_1559 = lean_ctor_get(x_1558, 0);
lean_inc_ref(x_1559);
x_1560 = lean_ctor_get(x_1558, 2);
lean_inc_ref(x_1560);
x_1561 = lean_ctor_get(x_1558, 3);
lean_inc_ref(x_1561);
x_1562 = lean_ctor_get(x_1558, 4);
lean_inc_ref(x_1562);
if (lean_is_exclusive(x_1558)) {
 lean_ctor_release(x_1558, 0);
 lean_ctor_release(x_1558, 1);
 lean_ctor_release(x_1558, 2);
 lean_ctor_release(x_1558, 3);
 lean_ctor_release(x_1558, 4);
 x_1563 = x_1558;
} else {
 lean_dec_ref(x_1558);
 x_1563 = lean_box(0);
}
x_1564 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_1565 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_1559);
x_1566 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_1566, 0, x_1559);
x_1567 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_1567, 0, x_1559);
x_1568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1568, 0, x_1566);
lean_ctor_set(x_1568, 1, x_1567);
x_1569 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_1569, 0, x_1562);
x_1570 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_1570, 0, x_1561);
x_1571 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_1571, 0, x_1560);
if (lean_is_scalar(x_1563)) {
 x_1572 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1572 = x_1563;
}
lean_ctor_set(x_1572, 0, x_1568);
lean_ctor_set(x_1572, 1, x_1564);
lean_ctor_set(x_1572, 2, x_1571);
lean_ctor_set(x_1572, 3, x_1570);
lean_ctor_set(x_1572, 4, x_1569);
x_1573 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1573, 0, x_1572);
lean_ctor_set(x_1573, 1, x_1565);
x_1574 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_1574);
x_1575 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_1575);
x_1576 = lean_ctor_get(x_7, 2);
lean_inc(x_1576);
x_1577 = lean_ctor_get(x_7, 3);
lean_inc(x_1577);
x_1578 = lean_ctor_get(x_7, 4);
lean_inc(x_1578);
x_1579 = lean_ctor_get(x_7, 5);
lean_inc(x_1579);
x_1580 = lean_ctor_get(x_7, 6);
lean_inc(x_1580);
x_1581 = lean_ctor_get(x_7, 7);
lean_inc(x_1581);
x_1582 = lean_ctor_get(x_7, 8);
lean_inc(x_1582);
x_1583 = lean_ctor_get(x_7, 9);
lean_inc(x_1583);
x_1584 = lean_ctor_get(x_7, 10);
lean_inc(x_1584);
x_1585 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_1586 = lean_ctor_get(x_7, 11);
lean_inc(x_1586);
x_1587 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_1588 = lean_ctor_get(x_7, 12);
lean_inc_ref(x_1588);
x_1589 = lean_nat_dec_eq(x_1577, x_1578);
if (x_1589 == 0)
{
lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; 
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 lean_ctor_release(x_7, 9);
 lean_ctor_release(x_7, 10);
 lean_ctor_release(x_7, 11);
 lean_ctor_release(x_7, 12);
 x_1590 = x_7;
} else {
 lean_dec_ref(x_7);
 x_1590 = lean_box(0);
}
x_1591 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
x_1592 = lean_ctor_get(x_1591, 1);
lean_inc(x_1592);
lean_dec_ref(x_1591);
x_1647 = lean_unsigned_to_nat(1u);
x_1648 = lean_nat_add(x_1577, x_1647);
lean_dec(x_1577);
if (lean_is_scalar(x_1590)) {
 x_1649 = lean_alloc_ctor(0, 13, 2);
} else {
 x_1649 = x_1590;
}
lean_ctor_set(x_1649, 0, x_1574);
lean_ctor_set(x_1649, 1, x_1575);
lean_ctor_set(x_1649, 2, x_1576);
lean_ctor_set(x_1649, 3, x_1648);
lean_ctor_set(x_1649, 4, x_1578);
lean_ctor_set(x_1649, 5, x_1579);
lean_ctor_set(x_1649, 6, x_1580);
lean_ctor_set(x_1649, 7, x_1581);
lean_ctor_set(x_1649, 8, x_1582);
lean_ctor_set(x_1649, 9, x_1583);
lean_ctor_set(x_1649, 10, x_1584);
lean_ctor_set(x_1649, 11, x_1586);
lean_ctor_set(x_1649, 12, x_1588);
lean_ctor_set_uint8(x_1649, sizeof(void*)*13, x_1585);
lean_ctor_set_uint8(x_1649, sizeof(void*)*13 + 1, x_1587);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; uint8_t x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; uint8_t x_1685; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; uint8_t x_1879; 
lean_dec_ref(x_1573);
x_1650 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1650);
x_1651 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1651);
lean_inc_ref(x_1650);
x_1846 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_1589, x_1650, x_3, x_5, x_6, x_1649, x_8, x_1592);
x_1847 = lean_ctor_get(x_1846, 0);
lean_inc(x_1847);
x_1848 = lean_ctor_get(x_1846, 1);
lean_inc(x_1848);
lean_dec_ref(x_1846);
x_1879 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2069_(x_1650, x_1847);
lean_dec_ref(x_1650);
if (x_1879 == 0)
{
goto block_1878;
}
else
{
if (x_1589 == 0)
{
x_1849 = x_2;
x_1850 = x_3;
x_1851 = x_4;
x_1852 = x_5;
x_1853 = x_6;
x_1854 = x_1649;
x_1855 = x_8;
x_1856 = x_1848;
goto block_1875;
}
else
{
goto block_1878;
}
}
block_1675:
{
lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; 
x_1669 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_1669, 0, x_1668);
lean_ctor_set(x_1669, 1, x_1657);
lean_ctor_set(x_1669, 2, x_1658);
lean_ctor_set(x_1669, 3, x_1659);
lean_ctor_set(x_1669, 4, x_1661);
lean_ctor_set(x_1669, 5, x_1662);
lean_ctor_set(x_1669, 6, x_1663);
lean_ctor_set_uint8(x_1669, sizeof(void*)*7, x_1660);
x_1670 = lean_st_ref_set(x_1655, x_1669, x_1666);
x_1671 = lean_ctor_get(x_1670, 1);
lean_inc(x_1671);
lean_dec_ref(x_1670);
x_1672 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1656, x_1655, x_1652, x_1671);
lean_dec_ref(x_1656);
x_1673 = lean_ctor_get(x_1672, 1);
lean_inc(x_1673);
lean_dec_ref(x_1672);
x_1 = x_1651;
x_2 = x_1665;
x_3 = x_1655;
x_4 = x_1667;
x_5 = x_1664;
x_6 = x_1652;
x_7 = x_1654;
x_8 = x_1653;
x_9 = x_1673;
goto _start;
}
block_1830:
{
if (x_1685 == 0)
{
lean_object* x_1686; 
lean_inc(x_1678);
lean_inc_ref(x_1680);
lean_inc(x_1676);
lean_inc_ref(x_1683);
lean_inc_ref(x_1681);
x_1686 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_1681, x_1683, x_1676, x_1680, x_1678, x_1677);
if (lean_obj_tag(x_1686) == 0)
{
lean_object* x_1687; 
x_1687 = lean_ctor_get(x_1686, 0);
lean_inc(x_1687);
if (lean_obj_tag(x_1687) == 0)
{
lean_object* x_1688; lean_object* x_1689; 
x_1688 = lean_ctor_get(x_1686, 1);
lean_inc(x_1688);
lean_dec_ref(x_1686);
lean_inc(x_1678);
lean_inc_ref(x_1680);
lean_inc(x_1676);
lean_inc_ref(x_1683);
lean_inc_ref(x_1681);
x_1689 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1681, x_1682, x_1679, x_1683, x_1676, x_1680, x_1678, x_1688);
if (lean_obj_tag(x_1689) == 0)
{
lean_object* x_1690; 
x_1690 = lean_ctor_get(x_1689, 0);
lean_inc(x_1690);
if (lean_obj_tag(x_1690) == 0)
{
lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; 
x_1691 = lean_ctor_get(x_1689, 1);
lean_inc(x_1691);
lean_dec_ref(x_1689);
x_1692 = lean_ctor_get(x_1681, 0);
lean_inc(x_1692);
x_1693 = lean_ctor_get(x_1681, 3);
lean_inc(x_1693);
lean_inc(x_1693);
x_1694 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1693, x_1691);
x_1695 = lean_ctor_get(x_1694, 0);
lean_inc(x_1695);
if (lean_obj_tag(x_1695) == 0)
{
lean_object* x_1696; lean_object* x_1697; 
x_1696 = lean_ctor_get(x_1694, 1);
lean_inc(x_1696);
lean_dec_ref(x_1694);
lean_inc(x_1678);
lean_inc_ref(x_1680);
lean_inc(x_1676);
lean_inc_ref(x_1683);
lean_inc_ref(x_1684);
lean_inc(x_1679);
lean_inc_ref(x_1682);
lean_inc_ref(x_1651);
lean_inc_ref(x_1681);
x_1697 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1681, x_1651, x_1682, x_1679, x_1684, x_1683, x_1676, x_1680, x_1678, x_1696);
if (lean_obj_tag(x_1697) == 0)
{
lean_object* x_1698; 
x_1698 = lean_ctor_get(x_1697, 0);
lean_inc(x_1698);
if (lean_obj_tag(x_1698) == 0)
{
lean_object* x_1699; lean_object* x_1700; 
x_1699 = lean_ctor_get(x_1697, 1);
lean_inc(x_1699);
lean_dec_ref(x_1697);
lean_inc(x_1678);
lean_inc_ref(x_1680);
lean_inc(x_1676);
lean_inc_ref(x_1683);
lean_inc_ref(x_1684);
lean_inc(x_1679);
lean_inc_ref(x_1682);
x_1700 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_1693, x_1682, x_1679, x_1684, x_1683, x_1676, x_1680, x_1678, x_1699);
if (lean_obj_tag(x_1700) == 0)
{
lean_object* x_1701; 
x_1701 = lean_ctor_get(x_1700, 0);
lean_inc(x_1701);
if (lean_obj_tag(x_1701) == 0)
{
lean_object* x_1702; lean_object* x_1703; 
x_1702 = lean_ctor_get(x_1700, 1);
lean_inc(x_1702);
lean_dec_ref(x_1700);
lean_inc(x_1678);
lean_inc_ref(x_1680);
lean_inc(x_1676);
lean_inc_ref(x_1683);
lean_inc_ref(x_1684);
lean_inc(x_1679);
lean_inc_ref(x_1682);
x_1703 = l_Lean_Compiler_LCNF_Simp_simp(x_1651, x_1682, x_1679, x_1684, x_1683, x_1676, x_1680, x_1678, x_1702);
if (lean_obj_tag(x_1703) == 0)
{
lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; uint8_t x_1708; 
x_1704 = lean_ctor_get(x_1703, 0);
lean_inc(x_1704);
x_1705 = lean_ctor_get(x_1703, 1);
lean_inc(x_1705);
lean_dec_ref(x_1703);
x_1706 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_1692, x_1679, x_1705);
lean_dec(x_1692);
x_1707 = lean_ctor_get(x_1706, 0);
lean_inc(x_1707);
x_1708 = lean_unbox(x_1707);
lean_dec(x_1707);
if (x_1708 == 0)
{
lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; 
lean_dec_ref(x_1684);
lean_dec_ref(x_1683);
lean_dec_ref(x_1682);
lean_dec_ref(x_1680);
lean_dec(x_1678);
lean_dec_ref(x_1);
x_1709 = lean_ctor_get(x_1706, 1);
lean_inc(x_1709);
lean_dec_ref(x_1706);
x_1710 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1681, x_1679, x_1676, x_1709);
lean_dec(x_1676);
lean_dec(x_1679);
lean_dec_ref(x_1681);
x_1711 = lean_ctor_get(x_1710, 1);
lean_inc(x_1711);
if (lean_is_exclusive(x_1710)) {
 lean_ctor_release(x_1710, 0);
 lean_ctor_release(x_1710, 1);
 x_1712 = x_1710;
} else {
 lean_dec_ref(x_1710);
 x_1712 = lean_box(0);
}
if (lean_is_scalar(x_1712)) {
 x_1713 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1713 = x_1712;
}
lean_ctor_set(x_1713, 0, x_1704);
lean_ctor_set(x_1713, 1, x_1711);
return x_1713;
}
else
{
lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; 
x_1714 = lean_ctor_get(x_1706, 1);
lean_inc(x_1714);
lean_dec_ref(x_1706);
lean_inc_ref(x_1681);
x_1715 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_1681, x_1682, x_1679, x_1684, x_1683, x_1676, x_1680, x_1678, x_1714);
lean_dec(x_1678);
lean_dec_ref(x_1680);
lean_dec(x_1676);
lean_dec_ref(x_1683);
lean_dec_ref(x_1684);
lean_dec(x_1679);
lean_dec_ref(x_1682);
x_1716 = lean_ctor_get(x_1715, 1);
lean_inc(x_1716);
if (lean_is_exclusive(x_1715)) {
 lean_ctor_release(x_1715, 0);
 lean_ctor_release(x_1715, 1);
 x_1717 = x_1715;
} else {
 lean_dec_ref(x_1715);
 x_1717 = lean_box(0);
}
x_1718 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_1681, x_1704);
lean_dec_ref(x_1);
if (lean_is_scalar(x_1717)) {
 x_1719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1719 = x_1717;
}
lean_ctor_set(x_1719, 0, x_1718);
lean_ctor_set(x_1719, 1, x_1716);
return x_1719;
}
}
else
{
lean_dec(x_1692);
lean_dec_ref(x_1684);
lean_dec_ref(x_1683);
lean_dec_ref(x_1682);
lean_dec_ref(x_1681);
lean_dec_ref(x_1680);
lean_dec(x_1679);
lean_dec(x_1678);
lean_dec(x_1676);
lean_dec_ref(x_1);
return x_1703;
}
}
else
{
lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; 
lean_dec_ref(x_1);
x_1720 = lean_ctor_get(x_1701, 0);
lean_inc(x_1720);
lean_dec_ref(x_1701);
x_1721 = lean_ctor_get(x_1700, 1);
lean_inc(x_1721);
lean_dec_ref(x_1700);
x_1722 = lean_ctor_get(x_1720, 0);
lean_inc(x_1722);
x_1723 = lean_ctor_get(x_1720, 1);
lean_inc(x_1723);
lean_dec(x_1720);
x_1724 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1692, x_1723, x_1679, x_1676, x_1680, x_1678, x_1721);
if (lean_obj_tag(x_1724) == 0)
{
lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; 
x_1725 = lean_ctor_get(x_1724, 1);
lean_inc(x_1725);
lean_dec_ref(x_1724);
x_1726 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1681, x_1679, x_1676, x_1725);
lean_dec_ref(x_1681);
x_1727 = lean_ctor_get(x_1726, 1);
lean_inc(x_1727);
lean_dec_ref(x_1726);
lean_inc(x_1678);
lean_inc_ref(x_1680);
lean_inc(x_1676);
lean_inc_ref(x_1683);
lean_inc_ref(x_1684);
lean_inc(x_1679);
lean_inc_ref(x_1682);
x_1728 = l_Lean_Compiler_LCNF_Simp_simp(x_1651, x_1682, x_1679, x_1684, x_1683, x_1676, x_1680, x_1678, x_1727);
if (lean_obj_tag(x_1728) == 0)
{
lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; 
x_1729 = lean_ctor_get(x_1728, 0);
lean_inc(x_1729);
x_1730 = lean_ctor_get(x_1728, 1);
lean_inc(x_1730);
lean_dec_ref(x_1728);
x_1731 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1722, x_1729, x_1682, x_1679, x_1684, x_1683, x_1676, x_1680, x_1678, x_1730);
lean_dec(x_1678);
lean_dec_ref(x_1680);
lean_dec(x_1676);
lean_dec_ref(x_1683);
lean_dec_ref(x_1684);
lean_dec(x_1679);
lean_dec_ref(x_1682);
lean_dec(x_1722);
return x_1731;
}
else
{
lean_dec(x_1722);
lean_dec_ref(x_1684);
lean_dec_ref(x_1683);
lean_dec_ref(x_1682);
lean_dec_ref(x_1680);
lean_dec(x_1679);
lean_dec(x_1678);
lean_dec(x_1676);
return x_1728;
}
}
else
{
lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; 
lean_dec(x_1722);
lean_dec_ref(x_1684);
lean_dec_ref(x_1683);
lean_dec_ref(x_1682);
lean_dec_ref(x_1681);
lean_dec_ref(x_1680);
lean_dec(x_1679);
lean_dec(x_1678);
lean_dec(x_1676);
lean_dec_ref(x_1651);
x_1732 = lean_ctor_get(x_1724, 0);
lean_inc(x_1732);
x_1733 = lean_ctor_get(x_1724, 1);
lean_inc(x_1733);
if (lean_is_exclusive(x_1724)) {
 lean_ctor_release(x_1724, 0);
 lean_ctor_release(x_1724, 1);
 x_1734 = x_1724;
} else {
 lean_dec_ref(x_1724);
 x_1734 = lean_box(0);
}
if (lean_is_scalar(x_1734)) {
 x_1735 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1735 = x_1734;
}
lean_ctor_set(x_1735, 0, x_1732);
lean_ctor_set(x_1735, 1, x_1733);
return x_1735;
}
}
}
else
{
lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; 
lean_dec(x_1692);
lean_dec_ref(x_1684);
lean_dec_ref(x_1683);
lean_dec_ref(x_1682);
lean_dec_ref(x_1681);
lean_dec_ref(x_1680);
lean_dec(x_1679);
lean_dec(x_1678);
lean_dec(x_1676);
lean_dec_ref(x_1651);
lean_dec_ref(x_1);
x_1736 = lean_ctor_get(x_1700, 0);
lean_inc(x_1736);
x_1737 = lean_ctor_get(x_1700, 1);
lean_inc(x_1737);
if (lean_is_exclusive(x_1700)) {
 lean_ctor_release(x_1700, 0);
 lean_ctor_release(x_1700, 1);
 x_1738 = x_1700;
} else {
 lean_dec_ref(x_1700);
 x_1738 = lean_box(0);
}
if (lean_is_scalar(x_1738)) {
 x_1739 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1739 = x_1738;
}
lean_ctor_set(x_1739, 0, x_1736);
lean_ctor_set(x_1739, 1, x_1737);
return x_1739;
}
}
else
{
lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; 
lean_dec(x_1693);
lean_dec(x_1692);
lean_dec_ref(x_1684);
lean_dec_ref(x_1683);
lean_dec_ref(x_1682);
lean_dec_ref(x_1680);
lean_dec(x_1678);
lean_dec_ref(x_1651);
lean_dec_ref(x_1);
x_1740 = lean_ctor_get(x_1697, 1);
lean_inc(x_1740);
lean_dec_ref(x_1697);
x_1741 = lean_ctor_get(x_1698, 0);
lean_inc(x_1741);
lean_dec_ref(x_1698);
x_1742 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1681, x_1679, x_1676, x_1740);
lean_dec(x_1676);
lean_dec(x_1679);
lean_dec_ref(x_1681);
x_1743 = lean_ctor_get(x_1742, 1);
lean_inc(x_1743);
if (lean_is_exclusive(x_1742)) {
 lean_ctor_release(x_1742, 0);
 lean_ctor_release(x_1742, 1);
 x_1744 = x_1742;
} else {
 lean_dec_ref(x_1742);
 x_1744 = lean_box(0);
}
if (lean_is_scalar(x_1744)) {
 x_1745 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1745 = x_1744;
}
lean_ctor_set(x_1745, 0, x_1741);
lean_ctor_set(x_1745, 1, x_1743);
return x_1745;
}
}
else
{
lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; 
lean_dec(x_1693);
lean_dec(x_1692);
lean_dec_ref(x_1684);
lean_dec_ref(x_1683);
lean_dec_ref(x_1682);
lean_dec_ref(x_1681);
lean_dec_ref(x_1680);
lean_dec(x_1679);
lean_dec(x_1678);
lean_dec(x_1676);
lean_dec_ref(x_1651);
lean_dec_ref(x_1);
x_1746 = lean_ctor_get(x_1697, 0);
lean_inc(x_1746);
x_1747 = lean_ctor_get(x_1697, 1);
lean_inc(x_1747);
if (lean_is_exclusive(x_1697)) {
 lean_ctor_release(x_1697, 0);
 lean_ctor_release(x_1697, 1);
 x_1748 = x_1697;
} else {
 lean_dec_ref(x_1697);
 x_1748 = lean_box(0);
}
if (lean_is_scalar(x_1748)) {
 x_1749 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1749 = x_1748;
}
lean_ctor_set(x_1749, 0, x_1746);
lean_ctor_set(x_1749, 1, x_1747);
return x_1749;
}
}
else
{
lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; 
lean_dec(x_1693);
lean_dec_ref(x_1);
x_1750 = lean_ctor_get(x_1694, 1);
lean_inc(x_1750);
lean_dec_ref(x_1694);
x_1751 = lean_ctor_get(x_1695, 0);
lean_inc(x_1751);
lean_dec_ref(x_1695);
x_1752 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1692, x_1751, x_1679, x_1676, x_1680, x_1678, x_1750);
if (lean_obj_tag(x_1752) == 0)
{
lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; 
x_1753 = lean_ctor_get(x_1752, 1);
lean_inc(x_1753);
lean_dec_ref(x_1752);
x_1754 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1681, x_1679, x_1676, x_1753);
lean_dec_ref(x_1681);
x_1755 = lean_ctor_get(x_1754, 1);
lean_inc(x_1755);
lean_dec_ref(x_1754);
x_1 = x_1651;
x_2 = x_1682;
x_3 = x_1679;
x_4 = x_1684;
x_5 = x_1683;
x_6 = x_1676;
x_7 = x_1680;
x_8 = x_1678;
x_9 = x_1755;
goto _start;
}
else
{
lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; 
lean_dec_ref(x_1684);
lean_dec_ref(x_1683);
lean_dec_ref(x_1682);
lean_dec_ref(x_1681);
lean_dec_ref(x_1680);
lean_dec(x_1679);
lean_dec(x_1678);
lean_dec(x_1676);
lean_dec_ref(x_1651);
x_1757 = lean_ctor_get(x_1752, 0);
lean_inc(x_1757);
x_1758 = lean_ctor_get(x_1752, 1);
lean_inc(x_1758);
if (lean_is_exclusive(x_1752)) {
 lean_ctor_release(x_1752, 0);
 lean_ctor_release(x_1752, 1);
 x_1759 = x_1752;
} else {
 lean_dec_ref(x_1752);
 x_1759 = lean_box(0);
}
if (lean_is_scalar(x_1759)) {
 x_1760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1760 = x_1759;
}
lean_ctor_set(x_1760, 0, x_1757);
lean_ctor_set(x_1760, 1, x_1758);
return x_1760;
}
}
}
else
{
lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; 
lean_dec_ref(x_1681);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1761 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1761 = lean_box(0);
}
x_1762 = lean_ctor_get(x_1689, 1);
lean_inc(x_1762);
lean_dec_ref(x_1689);
x_1763 = lean_ctor_get(x_1690, 0);
lean_inc(x_1763);
lean_dec_ref(x_1690);
if (lean_is_scalar(x_1761)) {
 x_1764 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1764 = x_1761;
 lean_ctor_set_tag(x_1764, 1);
}
lean_ctor_set(x_1764, 0, x_1763);
lean_ctor_set(x_1764, 1, x_1651);
x_1 = x_1764;
x_2 = x_1682;
x_3 = x_1679;
x_4 = x_1684;
x_5 = x_1683;
x_6 = x_1676;
x_7 = x_1680;
x_8 = x_1678;
x_9 = x_1762;
goto _start;
}
}
else
{
lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; 
lean_dec_ref(x_1684);
lean_dec_ref(x_1683);
lean_dec_ref(x_1682);
lean_dec_ref(x_1681);
lean_dec_ref(x_1680);
lean_dec(x_1679);
lean_dec(x_1678);
lean_dec(x_1676);
lean_dec_ref(x_1651);
lean_dec_ref(x_1);
x_1766 = lean_ctor_get(x_1689, 0);
lean_inc(x_1766);
x_1767 = lean_ctor_get(x_1689, 1);
lean_inc(x_1767);
if (lean_is_exclusive(x_1689)) {
 lean_ctor_release(x_1689, 0);
 lean_ctor_release(x_1689, 1);
 x_1768 = x_1689;
} else {
 lean_dec_ref(x_1689);
 x_1768 = lean_box(0);
}
if (lean_is_scalar(x_1768)) {
 x_1769 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1769 = x_1768;
}
lean_ctor_set(x_1769, 0, x_1766);
lean_ctor_set(x_1769, 1, x_1767);
return x_1769;
}
}
else
{
lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; 
lean_dec_ref(x_1681);
lean_dec_ref(x_1);
x_1770 = lean_ctor_get(x_1686, 1);
lean_inc(x_1770);
lean_dec_ref(x_1686);
x_1771 = lean_ctor_get(x_1687, 0);
lean_inc(x_1771);
lean_dec_ref(x_1687);
x_1772 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1679, x_1770);
x_1773 = lean_ctor_get(x_1772, 1);
lean_inc(x_1773);
lean_dec_ref(x_1772);
lean_inc(x_1678);
lean_inc_ref(x_1680);
lean_inc(x_1676);
lean_inc_ref(x_1683);
lean_inc_ref(x_1684);
lean_inc(x_1679);
lean_inc_ref(x_1682);
x_1774 = l_Lean_Compiler_LCNF_Simp_simp(x_1651, x_1682, x_1679, x_1684, x_1683, x_1676, x_1680, x_1678, x_1773);
if (lean_obj_tag(x_1774) == 0)
{
lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; 
x_1775 = lean_ctor_get(x_1774, 0);
lean_inc(x_1775);
x_1776 = lean_ctor_get(x_1774, 1);
lean_inc(x_1776);
lean_dec_ref(x_1774);
x_1777 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1771, x_1775, x_1682, x_1679, x_1684, x_1683, x_1676, x_1680, x_1678, x_1776);
lean_dec(x_1678);
lean_dec_ref(x_1680);
lean_dec(x_1676);
lean_dec_ref(x_1683);
lean_dec_ref(x_1684);
lean_dec(x_1679);
lean_dec_ref(x_1682);
lean_dec(x_1771);
return x_1777;
}
else
{
lean_dec(x_1771);
lean_dec_ref(x_1684);
lean_dec_ref(x_1683);
lean_dec_ref(x_1682);
lean_dec_ref(x_1680);
lean_dec(x_1679);
lean_dec(x_1678);
lean_dec(x_1676);
return x_1774;
}
}
}
else
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; 
lean_dec_ref(x_1684);
lean_dec_ref(x_1683);
lean_dec_ref(x_1682);
lean_dec_ref(x_1681);
lean_dec_ref(x_1680);
lean_dec(x_1679);
lean_dec(x_1678);
lean_dec(x_1676);
lean_dec_ref(x_1651);
lean_dec_ref(x_1);
x_1778 = lean_ctor_get(x_1686, 0);
lean_inc(x_1778);
x_1779 = lean_ctor_get(x_1686, 1);
lean_inc(x_1779);
if (lean_is_exclusive(x_1686)) {
 lean_ctor_release(x_1686, 0);
 lean_ctor_release(x_1686, 1);
 x_1780 = x_1686;
} else {
 lean_dec_ref(x_1686);
 x_1780 = lean_box(0);
}
if (lean_is_scalar(x_1780)) {
 x_1781 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1781 = x_1780;
}
lean_ctor_set(x_1781, 0, x_1778);
lean_ctor_set(x_1781, 1, x_1779);
return x_1781;
}
}
else
{
lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; uint8_t x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; uint64_t x_1799; uint64_t x_1800; uint64_t x_1801; uint64_t x_1802; uint64_t x_1803; uint64_t x_1804; uint64_t x_1805; size_t x_1806; size_t x_1807; size_t x_1808; size_t x_1809; size_t x_1810; lean_object* x_1811; uint8_t x_1812; 
lean_dec_ref(x_1);
x_1782 = lean_st_ref_take(x_1679, x_1677);
x_1783 = lean_ctor_get(x_1782, 0);
lean_inc(x_1783);
x_1784 = lean_ctor_get(x_1783, 0);
lean_inc_ref(x_1784);
x_1785 = lean_ctor_get(x_1782, 1);
lean_inc(x_1785);
lean_dec_ref(x_1782);
x_1786 = lean_ctor_get(x_1783, 1);
lean_inc_ref(x_1786);
x_1787 = lean_ctor_get(x_1783, 2);
lean_inc(x_1787);
x_1788 = lean_ctor_get(x_1783, 3);
lean_inc_ref(x_1788);
x_1789 = lean_ctor_get_uint8(x_1783, sizeof(void*)*7);
x_1790 = lean_ctor_get(x_1783, 4);
lean_inc(x_1790);
x_1791 = lean_ctor_get(x_1783, 5);
lean_inc(x_1791);
x_1792 = lean_ctor_get(x_1783, 6);
lean_inc(x_1792);
lean_dec(x_1783);
x_1793 = lean_ctor_get(x_1784, 0);
lean_inc(x_1793);
x_1794 = lean_ctor_get(x_1784, 1);
lean_inc_ref(x_1794);
if (lean_is_exclusive(x_1784)) {
 lean_ctor_release(x_1784, 0);
 lean_ctor_release(x_1784, 1);
 x_1795 = x_1784;
} else {
 lean_dec_ref(x_1784);
 x_1795 = lean_box(0);
}
x_1796 = lean_ctor_get(x_1681, 0);
lean_inc(x_1796);
x_1797 = lean_box(0);
x_1798 = lean_array_get_size(x_1794);
x_1799 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_1796);
x_1800 = 32;
x_1801 = lean_uint64_shift_right(x_1799, x_1800);
x_1802 = lean_uint64_xor(x_1799, x_1801);
x_1803 = 16;
x_1804 = lean_uint64_shift_right(x_1802, x_1803);
x_1805 = lean_uint64_xor(x_1802, x_1804);
x_1806 = lean_uint64_to_usize(x_1805);
x_1807 = lean_usize_of_nat(x_1798);
lean_dec(x_1798);
x_1808 = 1;
x_1809 = lean_usize_sub(x_1807, x_1808);
x_1810 = lean_usize_land(x_1806, x_1809);
x_1811 = lean_array_uget(x_1794, x_1810);
x_1812 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1796, x_1811);
if (x_1812 == 0)
{
lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; uint8_t x_1821; 
x_1813 = lean_nat_add(x_1793, x_1647);
lean_dec(x_1793);
x_1814 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1814, 0, x_1796);
lean_ctor_set(x_1814, 1, x_1797);
lean_ctor_set(x_1814, 2, x_1811);
x_1815 = lean_array_uset(x_1794, x_1810, x_1814);
x_1816 = lean_unsigned_to_nat(4u);
x_1817 = lean_nat_mul(x_1813, x_1816);
x_1818 = lean_unsigned_to_nat(3u);
x_1819 = lean_nat_div(x_1817, x_1818);
lean_dec(x_1817);
x_1820 = lean_array_get_size(x_1815);
x_1821 = lean_nat_dec_le(x_1819, x_1820);
lean_dec(x_1820);
lean_dec(x_1819);
if (x_1821 == 0)
{
lean_object* x_1822; lean_object* x_1823; 
x_1822 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_1815);
if (lean_is_scalar(x_1795)) {
 x_1823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1823 = x_1795;
}
lean_ctor_set(x_1823, 0, x_1813);
lean_ctor_set(x_1823, 1, x_1822);
x_1652 = x_1676;
x_1653 = x_1678;
x_1654 = x_1680;
x_1655 = x_1679;
x_1656 = x_1681;
x_1657 = x_1786;
x_1658 = x_1787;
x_1659 = x_1788;
x_1660 = x_1789;
x_1661 = x_1790;
x_1662 = x_1791;
x_1663 = x_1792;
x_1664 = x_1683;
x_1665 = x_1682;
x_1666 = x_1785;
x_1667 = x_1684;
x_1668 = x_1823;
goto block_1675;
}
else
{
lean_object* x_1824; 
if (lean_is_scalar(x_1795)) {
 x_1824 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1824 = x_1795;
}
lean_ctor_set(x_1824, 0, x_1813);
lean_ctor_set(x_1824, 1, x_1815);
x_1652 = x_1676;
x_1653 = x_1678;
x_1654 = x_1680;
x_1655 = x_1679;
x_1656 = x_1681;
x_1657 = x_1786;
x_1658 = x_1787;
x_1659 = x_1788;
x_1660 = x_1789;
x_1661 = x_1790;
x_1662 = x_1791;
x_1663 = x_1792;
x_1664 = x_1683;
x_1665 = x_1682;
x_1666 = x_1785;
x_1667 = x_1684;
x_1668 = x_1824;
goto block_1675;
}
}
else
{
lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; 
x_1825 = lean_box(0);
x_1826 = lean_array_uset(x_1794, x_1810, x_1825);
x_1827 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_1796, x_1797, x_1811);
x_1828 = lean_array_uset(x_1826, x_1810, x_1827);
if (lean_is_scalar(x_1795)) {
 x_1829 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1829 = x_1795;
}
lean_ctor_set(x_1829, 0, x_1793);
lean_ctor_set(x_1829, 1, x_1828);
x_1652 = x_1676;
x_1653 = x_1678;
x_1654 = x_1680;
x_1655 = x_1679;
x_1656 = x_1681;
x_1657 = x_1786;
x_1658 = x_1787;
x_1659 = x_1788;
x_1660 = x_1789;
x_1661 = x_1790;
x_1662 = x_1791;
x_1663 = x_1792;
x_1664 = x_1683;
x_1665 = x_1682;
x_1666 = x_1785;
x_1667 = x_1684;
x_1668 = x_1829;
goto block_1675;
}
}
}
block_1845:
{
uint8_t x_1842; 
x_1842 = l_Lean_Expr_isErased(x_1832);
lean_dec_ref(x_1832);
if (x_1842 == 0)
{
lean_dec(x_1833);
x_1676 = x_1838;
x_1677 = x_1841;
x_1678 = x_1840;
x_1679 = x_1835;
x_1680 = x_1839;
x_1681 = x_1831;
x_1682 = x_1834;
x_1683 = x_1837;
x_1684 = x_1836;
x_1685 = x_1589;
goto block_1830;
}
else
{
lean_object* x_1843; uint8_t x_1844; 
x_1843 = lean_box(1);
x_1844 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1209_(x_1833, x_1843);
lean_dec(x_1833);
if (x_1844 == 0)
{
x_1676 = x_1838;
x_1677 = x_1841;
x_1678 = x_1840;
x_1679 = x_1835;
x_1680 = x_1839;
x_1681 = x_1831;
x_1682 = x_1834;
x_1683 = x_1837;
x_1684 = x_1836;
x_1685 = x_1842;
goto block_1830;
}
else
{
x_1676 = x_1838;
x_1677 = x_1841;
x_1678 = x_1840;
x_1679 = x_1835;
x_1680 = x_1839;
x_1681 = x_1831;
x_1682 = x_1834;
x_1683 = x_1837;
x_1684 = x_1836;
x_1685 = x_1589;
goto block_1830;
}
}
}
block_1875:
{
lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; 
x_1857 = lean_ctor_get(x_1847, 2);
lean_inc_ref(x_1857);
x_1858 = lean_ctor_get(x_1847, 3);
lean_inc(x_1858);
lean_inc(x_1855);
lean_inc_ref(x_1854);
lean_inc(x_1853);
lean_inc_ref(x_1852);
lean_inc_ref(x_1851);
lean_inc(x_1858);
x_1859 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_1858, x_1849, x_1851, x_1852, x_1853, x_1854, x_1855, x_1856);
if (lean_obj_tag(x_1859) == 0)
{
lean_object* x_1860; 
x_1860 = lean_ctor_get(x_1859, 0);
lean_inc(x_1860);
if (lean_obj_tag(x_1860) == 0)
{
lean_object* x_1861; 
x_1861 = lean_ctor_get(x_1859, 1);
lean_inc(x_1861);
lean_dec_ref(x_1859);
x_1831 = x_1847;
x_1832 = x_1857;
x_1833 = x_1858;
x_1834 = x_1849;
x_1835 = x_1850;
x_1836 = x_1851;
x_1837 = x_1852;
x_1838 = x_1853;
x_1839 = x_1854;
x_1840 = x_1855;
x_1841 = x_1861;
goto block_1845;
}
else
{
lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; 
lean_dec(x_1858);
lean_dec_ref(x_1857);
x_1862 = lean_ctor_get(x_1859, 1);
lean_inc(x_1862);
lean_dec_ref(x_1859);
x_1863 = lean_ctor_get(x_1860, 0);
lean_inc(x_1863);
lean_dec_ref(x_1860);
x_1864 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1850, x_1862);
x_1865 = lean_ctor_get(x_1864, 1);
lean_inc(x_1865);
lean_dec_ref(x_1864);
x_1866 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_1847, x_1863, x_1853, x_1865);
x_1867 = lean_ctor_get(x_1866, 0);
lean_inc(x_1867);
x_1868 = lean_ctor_get(x_1866, 1);
lean_inc(x_1868);
lean_dec_ref(x_1866);
x_1869 = lean_ctor_get(x_1867, 2);
lean_inc_ref(x_1869);
x_1870 = lean_ctor_get(x_1867, 3);
lean_inc(x_1870);
x_1831 = x_1867;
x_1832 = x_1869;
x_1833 = x_1870;
x_1834 = x_1849;
x_1835 = x_1850;
x_1836 = x_1851;
x_1837 = x_1852;
x_1838 = x_1853;
x_1839 = x_1854;
x_1840 = x_1855;
x_1841 = x_1868;
goto block_1845;
}
}
else
{
lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; 
lean_dec(x_1858);
lean_dec_ref(x_1857);
lean_dec(x_1855);
lean_dec_ref(x_1854);
lean_dec(x_1853);
lean_dec_ref(x_1852);
lean_dec_ref(x_1851);
lean_dec(x_1850);
lean_dec_ref(x_1849);
lean_dec(x_1847);
lean_dec_ref(x_1651);
lean_dec_ref(x_1);
x_1871 = lean_ctor_get(x_1859, 0);
lean_inc(x_1871);
x_1872 = lean_ctor_get(x_1859, 1);
lean_inc(x_1872);
if (lean_is_exclusive(x_1859)) {
 lean_ctor_release(x_1859, 0);
 lean_ctor_release(x_1859, 1);
 x_1873 = x_1859;
} else {
 lean_dec_ref(x_1859);
 x_1873 = lean_box(0);
}
if (lean_is_scalar(x_1873)) {
 x_1874 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1874 = x_1873;
}
lean_ctor_set(x_1874, 0, x_1871);
lean_ctor_set(x_1874, 1, x_1872);
return x_1874;
}
}
block_1878:
{
lean_object* x_1876; lean_object* x_1877; 
x_1876 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_1848);
x_1877 = lean_ctor_get(x_1876, 1);
lean_inc(x_1877);
lean_dec_ref(x_1876);
x_1849 = x_2;
x_1850 = x_3;
x_1851 = x_4;
x_1852 = x_5;
x_1853 = x_6;
x_1854 = x_1649;
x_1855 = x_8;
x_1856 = x_1877;
goto block_1875;
}
}
case 3:
{
lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; 
lean_dec_ref(x_1573);
x_1880 = lean_ctor_get(x_1, 0);
lean_inc(x_1880);
x_1881 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1881);
x_1882 = lean_st_ref_get(x_3, x_1592);
x_1883 = lean_ctor_get(x_1882, 0);
lean_inc(x_1883);
x_1884 = lean_ctor_get(x_1882, 1);
lean_inc(x_1884);
lean_dec_ref(x_1882);
x_1885 = lean_ctor_get(x_1883, 0);
lean_inc_ref(x_1885);
lean_dec(x_1883);
x_1886 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_1885, x_1880, x_1589);
lean_dec_ref(x_1885);
if (lean_obj_tag(x_1886) == 0)
{
lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1896; 
x_1887 = lean_ctor_get(x_1886, 0);
lean_inc(x_1887);
lean_dec_ref(x_1886);
x_1888 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_1589, x_1881, x_3, x_1884);
x_1889 = lean_ctor_get(x_1888, 0);
lean_inc(x_1889);
x_1890 = lean_ctor_get(x_1888, 1);
lean_inc(x_1890);
if (lean_is_exclusive(x_1888)) {
 lean_ctor_release(x_1888, 0);
 lean_ctor_release(x_1888, 1);
 x_1891 = x_1888;
} else {
 lean_dec_ref(x_1888);
 x_1891 = lean_box(0);
}
lean_inc(x_1889);
x_1896 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1887, x_1889, x_2, x_3, x_4, x_5, x_6, x_1649, x_8, x_1890);
if (lean_obj_tag(x_1896) == 0)
{
lean_object* x_1897; 
x_1897 = lean_ctor_get(x_1896, 0);
lean_inc(x_1897);
if (lean_obj_tag(x_1897) == 0)
{
lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; uint8_t x_1903; 
lean_dec_ref(x_1649);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1898 = lean_ctor_get(x_1896, 1);
lean_inc(x_1898);
lean_dec_ref(x_1896);
lean_inc(x_1887);
x_1899 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1887, x_3, x_1898);
x_1900 = lean_ctor_get(x_1899, 1);
lean_inc(x_1900);
lean_dec_ref(x_1899);
x_1901 = lean_unsigned_to_nat(0u);
x_1902 = lean_array_get_size(x_1889);
x_1903 = lean_nat_dec_lt(x_1901, x_1902);
if (x_1903 == 0)
{
lean_dec(x_1902);
lean_dec(x_3);
x_1892 = x_1900;
goto block_1895;
}
else
{
uint8_t x_1904; 
x_1904 = lean_nat_dec_le(x_1902, x_1902);
if (x_1904 == 0)
{
lean_dec(x_1902);
lean_dec(x_3);
x_1892 = x_1900;
goto block_1895;
}
else
{
lean_object* x_1905; size_t x_1906; size_t x_1907; lean_object* x_1908; lean_object* x_1909; 
x_1905 = lean_box(0);
x_1906 = 0;
x_1907 = lean_usize_of_nat(x_1902);
lean_dec(x_1902);
x_1908 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1889, x_1906, x_1907, x_1905, x_3, x_1900);
lean_dec(x_3);
x_1909 = lean_ctor_get(x_1908, 1);
lean_inc(x_1909);
lean_dec_ref(x_1908);
x_1892 = x_1909;
goto block_1895;
}
}
}
else
{
lean_object* x_1910; lean_object* x_1911; 
lean_dec(x_1891);
lean_dec(x_1889);
lean_dec(x_1887);
lean_dec_ref(x_1);
x_1910 = lean_ctor_get(x_1896, 1);
lean_inc(x_1910);
lean_dec_ref(x_1896);
x_1911 = lean_ctor_get(x_1897, 0);
lean_inc(x_1911);
lean_dec_ref(x_1897);
x_1 = x_1911;
x_7 = x_1649;
x_9 = x_1910;
goto _start;
}
}
else
{
lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; 
lean_dec(x_1891);
lean_dec(x_1889);
lean_dec(x_1887);
lean_dec_ref(x_1649);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1913 = lean_ctor_get(x_1896, 0);
lean_inc(x_1913);
x_1914 = lean_ctor_get(x_1896, 1);
lean_inc(x_1914);
if (lean_is_exclusive(x_1896)) {
 lean_ctor_release(x_1896, 0);
 lean_ctor_release(x_1896, 1);
 x_1915 = x_1896;
} else {
 lean_dec_ref(x_1896);
 x_1915 = lean_box(0);
}
if (lean_is_scalar(x_1915)) {
 x_1916 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1916 = x_1915;
}
lean_ctor_set(x_1916, 0, x_1913);
lean_ctor_set(x_1916, 1, x_1914);
return x_1916;
}
block_1895:
{
lean_object* x_1893; lean_object* x_1894; 
x_1893 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_1, x_1887, x_1889);
lean_dec_ref(x_1);
if (lean_is_scalar(x_1891)) {
 x_1894 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1894 = x_1891;
}
lean_ctor_set(x_1894, 0, x_1893);
lean_ctor_set(x_1894, 1, x_1892);
return x_1894;
}
}
else
{
lean_object* x_1917; 
lean_dec_ref(x_1881);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1917 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1649, x_8, x_1884);
lean_dec(x_8);
lean_dec_ref(x_1649);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1917;
}
}
case 4:
{
lean_object* x_1918; lean_object* x_1919; 
x_1918 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1918);
lean_inc(x_8);
lean_inc_ref(x_1649);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1918);
x_1919 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1918, x_2, x_3, x_4, x_5, x_6, x_1649, x_8, x_1592);
if (lean_obj_tag(x_1919) == 0)
{
lean_object* x_1920; 
x_1920 = lean_ctor_get(x_1919, 0);
lean_inc(x_1920);
if (lean_obj_tag(x_1920) == 0)
{
lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; 
x_1921 = lean_ctor_get(x_1919, 1);
lean_inc(x_1921);
lean_dec_ref(x_1919);
x_1922 = lean_st_ref_get(x_3, x_1921);
x_1923 = lean_ctor_get(x_1922, 0);
lean_inc(x_1923);
x_1924 = lean_ctor_get(x_1922, 1);
lean_inc(x_1924);
lean_dec_ref(x_1922);
x_1925 = lean_ctor_get(x_1918, 1);
lean_inc_ref(x_1925);
x_1926 = lean_ctor_get(x_1918, 2);
lean_inc(x_1926);
x_1927 = lean_ctor_get(x_1918, 3);
lean_inc_ref(x_1927);
lean_dec_ref(x_1918);
x_1928 = lean_ctor_get(x_1923, 0);
lean_inc_ref(x_1928);
lean_dec(x_1923);
x_1929 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_1928, x_1926, x_1589);
lean_dec_ref(x_1928);
if (lean_obj_tag(x_1929) == 0)
{
lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; 
x_1930 = lean_ctor_get(x_1929, 0);
lean_inc(x_1930);
lean_dec_ref(x_1929);
x_1931 = lean_st_ref_get(x_3, x_1924);
x_1932 = lean_ctor_get(x_1931, 0);
lean_inc(x_1932);
x_1933 = lean_ctor_get(x_1931, 1);
lean_inc(x_1933);
lean_dec_ref(x_1931);
x_1934 = lean_box(x_1589);
lean_inc(x_1930);
x_1935 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__1___boxed), 11, 2);
lean_closure_set(x_1935, 0, x_1930);
lean_closure_set(x_1935, 1, x_1934);
x_1936 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_1573, x_1927, x_1935);
lean_inc(x_8);
lean_inc_ref(x_1649);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_1937 = lean_apply_8(x_1936, x_2, x_3, x_4, x_5, x_6, x_1649, x_8, x_1933);
if (lean_obj_tag(x_1937) == 0)
{
lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; 
x_1938 = lean_ctor_get(x_1937, 0);
lean_inc(x_1938);
x_1939 = lean_ctor_get(x_1937, 1);
lean_inc(x_1939);
lean_dec_ref(x_1937);
lean_inc(x_6);
lean_inc(x_3);
x_1940 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1938, x_2, x_3, x_4, x_5, x_6, x_1649, x_8, x_1939);
if (lean_obj_tag(x_1940) == 0)
{
lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1954; uint8_t x_1955; 
x_1941 = lean_ctor_get(x_1940, 0);
lean_inc(x_1941);
x_1942 = lean_ctor_get(x_1940, 1);
lean_inc(x_1942);
if (lean_is_exclusive(x_1940)) {
 lean_ctor_release(x_1940, 0);
 lean_ctor_release(x_1940, 1);
 x_1943 = x_1940;
} else {
 lean_dec_ref(x_1940);
 x_1943 = lean_box(0);
}
x_1944 = lean_ctor_get(x_1932, 0);
lean_inc_ref(x_1944);
lean_dec(x_1932);
x_1945 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1944, x_1589, x_1925);
lean_dec_ref(x_1944);
x_1954 = lean_array_get_size(x_1941);
x_1955 = lean_nat_dec_eq(x_1954, x_1647);
lean_dec(x_1954);
if (x_1955 == 0)
{
lean_dec(x_1943);
lean_dec(x_6);
x_1946 = x_3;
x_1947 = x_1942;
goto block_1953;
}
else
{
lean_object* x_1956; lean_object* x_1957; 
x_1956 = lean_unsigned_to_nat(0u);
x_1957 = lean_array_fget(x_1941, x_1956);
if (lean_obj_tag(x_1957) == 0)
{
lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1966; lean_object* x_1967; uint8_t x_1976; lean_object* x_1977; uint8_t x_1979; 
lean_dec(x_1943);
x_1958 = lean_ctor_get(x_1957, 1);
lean_inc_ref(x_1958);
x_1959 = lean_ctor_get(x_1957, 2);
lean_inc_ref(x_1959);
lean_dec_ref(x_1957);
x_1966 = lean_array_get_size(x_1958);
x_1979 = lean_nat_dec_lt(x_1956, x_1966);
if (x_1979 == 0)
{
x_1976 = x_1589;
x_1977 = x_1942;
goto block_1978;
}
else
{
if (x_1979 == 0)
{
x_1976 = x_1589;
x_1977 = x_1942;
goto block_1978;
}
else
{
size_t x_1980; size_t x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; uint8_t x_1985; 
x_1980 = 0;
x_1981 = lean_usize_of_nat(x_1966);
x_1982 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1958, x_1980, x_1981, x_3, x_1942);
x_1983 = lean_ctor_get(x_1982, 0);
lean_inc(x_1983);
x_1984 = lean_ctor_get(x_1982, 1);
lean_inc(x_1984);
lean_dec_ref(x_1982);
x_1985 = lean_unbox(x_1983);
lean_dec(x_1983);
x_1976 = x_1985;
x_1977 = x_1984;
goto block_1978;
}
}
block_1965:
{
lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; 
x_1961 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_1960);
lean_dec(x_3);
x_1962 = lean_ctor_get(x_1961, 1);
lean_inc(x_1962);
if (lean_is_exclusive(x_1961)) {
 lean_ctor_release(x_1961, 0);
 lean_ctor_release(x_1961, 1);
 x_1963 = x_1961;
} else {
 lean_dec_ref(x_1961);
 x_1963 = lean_box(0);
}
if (lean_is_scalar(x_1963)) {
 x_1964 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1964 = x_1963;
}
lean_ctor_set(x_1964, 0, x_1959);
lean_ctor_set(x_1964, 1, x_1962);
return x_1964;
}
block_1975:
{
uint8_t x_1968; 
x_1968 = lean_nat_dec_lt(x_1956, x_1966);
if (x_1968 == 0)
{
lean_dec(x_1966);
lean_dec_ref(x_1958);
lean_dec(x_6);
x_1960 = x_1967;
goto block_1965;
}
else
{
uint8_t x_1969; 
x_1969 = lean_nat_dec_le(x_1966, x_1966);
if (x_1969 == 0)
{
lean_dec(x_1966);
lean_dec_ref(x_1958);
lean_dec(x_6);
x_1960 = x_1967;
goto block_1965;
}
else
{
lean_object* x_1970; size_t x_1971; size_t x_1972; lean_object* x_1973; lean_object* x_1974; 
x_1970 = lean_box(0);
x_1971 = 0;
x_1972 = lean_usize_of_nat(x_1966);
lean_dec(x_1966);
x_1973 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1958, x_1971, x_1972, x_1970, x_6, x_1967);
lean_dec(x_6);
lean_dec_ref(x_1958);
x_1974 = lean_ctor_get(x_1973, 1);
lean_inc(x_1974);
lean_dec_ref(x_1973);
x_1960 = x_1974;
goto block_1965;
}
}
}
block_1978:
{
if (x_1976 == 0)
{
lean_dec_ref(x_1945);
lean_dec(x_1941);
lean_dec(x_1930);
lean_dec_ref(x_1);
x_1967 = x_1977;
goto block_1975;
}
else
{
if (x_1589 == 0)
{
lean_dec(x_1966);
lean_dec_ref(x_1959);
lean_dec_ref(x_1958);
lean_dec(x_6);
x_1946 = x_3;
x_1947 = x_1977;
goto block_1953;
}
else
{
lean_dec_ref(x_1945);
lean_dec(x_1941);
lean_dec(x_1930);
lean_dec_ref(x_1);
x_1967 = x_1977;
goto block_1975;
}
}
}
}
else
{
lean_object* x_1986; lean_object* x_1987; 
lean_dec_ref(x_1945);
lean_dec(x_1941);
lean_dec(x_1930);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1986 = lean_ctor_get(x_1957, 0);
lean_inc_ref(x_1986);
lean_dec_ref(x_1957);
if (lean_is_scalar(x_1943)) {
 x_1987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1987 = x_1943;
}
lean_ctor_set(x_1987, 0, x_1986);
lean_ctor_set(x_1987, 1, x_1942);
return x_1987;
}
}
block_1953:
{
lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; 
lean_inc(x_1930);
x_1948 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1930, x_1946, x_1947);
lean_dec(x_1946);
x_1949 = lean_ctor_get(x_1948, 1);
lean_inc(x_1949);
if (lean_is_exclusive(x_1948)) {
 lean_ctor_release(x_1948, 0);
 lean_ctor_release(x_1948, 1);
 x_1950 = x_1948;
} else {
 lean_dec_ref(x_1948);
 x_1950 = lean_box(0);
}
x_1951 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_1, x_1945, x_1930, x_1941);
if (lean_is_scalar(x_1950)) {
 x_1952 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1952 = x_1950;
}
lean_ctor_set(x_1952, 0, x_1951);
lean_ctor_set(x_1952, 1, x_1949);
return x_1952;
}
}
else
{
lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; 
lean_dec(x_1932);
lean_dec(x_1930);
lean_dec_ref(x_1925);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1988 = lean_ctor_get(x_1940, 0);
lean_inc(x_1988);
x_1989 = lean_ctor_get(x_1940, 1);
lean_inc(x_1989);
if (lean_is_exclusive(x_1940)) {
 lean_ctor_release(x_1940, 0);
 lean_ctor_release(x_1940, 1);
 x_1990 = x_1940;
} else {
 lean_dec_ref(x_1940);
 x_1990 = lean_box(0);
}
if (lean_is_scalar(x_1990)) {
 x_1991 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1991 = x_1990;
}
lean_ctor_set(x_1991, 0, x_1988);
lean_ctor_set(x_1991, 1, x_1989);
return x_1991;
}
}
else
{
lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; 
lean_dec(x_1932);
lean_dec(x_1930);
lean_dec_ref(x_1925);
lean_dec_ref(x_1649);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1992 = lean_ctor_get(x_1937, 0);
lean_inc(x_1992);
x_1993 = lean_ctor_get(x_1937, 1);
lean_inc(x_1993);
if (lean_is_exclusive(x_1937)) {
 lean_ctor_release(x_1937, 0);
 lean_ctor_release(x_1937, 1);
 x_1994 = x_1937;
} else {
 lean_dec_ref(x_1937);
 x_1994 = lean_box(0);
}
if (lean_is_scalar(x_1994)) {
 x_1995 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1995 = x_1994;
}
lean_ctor_set(x_1995, 0, x_1992);
lean_ctor_set(x_1995, 1, x_1993);
return x_1995;
}
}
else
{
lean_object* x_1996; 
lean_dec_ref(x_1927);
lean_dec_ref(x_1925);
lean_dec_ref(x_1573);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1996 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1649, x_8, x_1924);
lean_dec(x_8);
lean_dec_ref(x_1649);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1996;
}
}
else
{
lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; 
lean_dec_ref(x_1918);
lean_dec_ref(x_1649);
lean_dec_ref(x_1573);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1997 = lean_ctor_get(x_1919, 1);
lean_inc(x_1997);
if (lean_is_exclusive(x_1919)) {
 lean_ctor_release(x_1919, 0);
 lean_ctor_release(x_1919, 1);
 x_1998 = x_1919;
} else {
 lean_dec_ref(x_1919);
 x_1998 = lean_box(0);
}
x_1999 = lean_ctor_get(x_1920, 0);
lean_inc(x_1999);
lean_dec_ref(x_1920);
if (lean_is_scalar(x_1998)) {
 x_2000 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2000 = x_1998;
}
lean_ctor_set(x_2000, 0, x_1999);
lean_ctor_set(x_2000, 1, x_1997);
return x_2000;
}
}
else
{
lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; 
lean_dec_ref(x_1918);
lean_dec_ref(x_1649);
lean_dec_ref(x_1573);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2001 = lean_ctor_get(x_1919, 0);
lean_inc(x_2001);
x_2002 = lean_ctor_get(x_1919, 1);
lean_inc(x_2002);
if (lean_is_exclusive(x_1919)) {
 lean_ctor_release(x_1919, 0);
 lean_ctor_release(x_1919, 1);
 x_2003 = x_1919;
} else {
 lean_dec_ref(x_1919);
 x_2003 = lean_box(0);
}
if (lean_is_scalar(x_2003)) {
 x_2004 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2004 = x_2003;
}
lean_ctor_set(x_2004, 0, x_2001);
lean_ctor_set(x_2004, 1, x_2002);
return x_2004;
}
}
case 5:
{
lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; 
lean_dec_ref(x_1573);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_2005 = lean_ctor_get(x_1, 0);
lean_inc(x_2005);
x_2006 = lean_st_ref_get(x_3, x_1592);
x_2007 = lean_ctor_get(x_2006, 0);
lean_inc(x_2007);
x_2008 = lean_ctor_get(x_2006, 1);
lean_inc(x_2008);
lean_dec_ref(x_2006);
x_2009 = lean_ctor_get(x_2007, 0);
lean_inc_ref(x_2009);
lean_dec(x_2007);
x_2010 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_2009, x_2005, x_1589);
lean_dec_ref(x_2009);
if (lean_obj_tag(x_2010) == 0)
{
lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; 
lean_dec_ref(x_1649);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_2011 = lean_ctor_get(x_2010, 0);
lean_inc(x_2011);
lean_dec_ref(x_2010);
lean_inc(x_2011);
x_2012 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_2011, x_3, x_2008);
lean_dec(x_3);
x_2013 = lean_ctor_get(x_2012, 1);
lean_inc(x_2013);
if (lean_is_exclusive(x_2012)) {
 lean_ctor_release(x_2012, 0);
 lean_ctor_release(x_2012, 1);
 x_2014 = x_2012;
} else {
 lean_dec_ref(x_2012);
 x_2014 = lean_box(0);
}
x_2015 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_1, x_2011);
if (lean_is_scalar(x_2014)) {
 x_2016 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2016 = x_2014;
}
lean_ctor_set(x_2016, 0, x_2015);
lean_ctor_set(x_2016, 1, x_2013);
return x_2016;
}
else
{
lean_object* x_2017; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_2017 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_1649, x_8, x_2008);
lean_dec(x_8);
lean_dec_ref(x_1649);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_2017;
}
}
case 6:
{
lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; 
lean_dec_ref(x_1649);
lean_dec_ref(x_1573);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_2018 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2018);
x_2019 = lean_st_ref_get(x_3, x_1592);
lean_dec(x_3);
x_2020 = lean_ctor_get(x_2019, 0);
lean_inc(x_2020);
x_2021 = lean_ctor_get(x_2019, 1);
lean_inc(x_2021);
if (lean_is_exclusive(x_2019)) {
 lean_ctor_release(x_2019, 0);
 lean_ctor_release(x_2019, 1);
 x_2022 = x_2019;
} else {
 lean_dec_ref(x_2019);
 x_2022 = lean_box(0);
}
x_2023 = lean_ctor_get(x_2020, 0);
lean_inc_ref(x_2023);
lean_dec(x_2020);
x_2024 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_2023, x_1589, x_2018);
lean_dec_ref(x_2023);
x_2025 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(x_1, x_2024);
if (lean_is_scalar(x_2022)) {
 x_2026 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2026 = x_2022;
}
lean_ctor_set(x_2026, 0, x_2025);
lean_ctor_set(x_2026, 1, x_2021);
return x_2026;
}
default: 
{
lean_object* x_2027; lean_object* x_2028; 
lean_dec_ref(x_1573);
x_2027 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2027);
x_2028 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2028);
x_1593 = x_2027;
x_1594 = x_2028;
x_1595 = x_2;
x_1596 = x_3;
x_1597 = x_4;
x_1598 = x_5;
x_1599 = x_6;
x_1600 = x_1649;
x_1601 = x_8;
goto block_1646;
}
}
block_1646:
{
lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; uint8_t x_1609; 
x_1602 = lean_ctor_get(x_1593, 0);
lean_inc(x_1602);
x_1603 = lean_ctor_get(x_1593, 2);
lean_inc_ref(x_1603);
x_1604 = lean_ctor_get(x_1593, 3);
lean_inc_ref(x_1604);
x_1605 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_1602, x_1596, x_1592);
lean_dec(x_1602);
x_1606 = lean_ctor_get(x_1605, 0);
lean_inc(x_1606);
x_1607 = lean_ctor_get(x_1605, 1);
lean_inc(x_1607);
lean_dec_ref(x_1605);
lean_inc(x_1606);
lean_inc_ref(x_1);
lean_inc_ref(x_1594);
x_1608 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_1608, 0, x_1594);
lean_closure_set(x_1608, 1, x_1);
lean_closure_set(x_1608, 2, x_1606);
x_1609 = lean_unbox(x_1606);
if (x_1609 == 0)
{
uint8_t x_1610; 
lean_dec(x_1606);
lean_dec_ref(x_1594);
x_1610 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_1610 == 0)
{
lean_dec_ref(x_1604);
lean_dec_ref(x_1603);
x_10 = x_1608;
x_11 = x_1593;
x_12 = x_1595;
x_13 = x_1596;
x_14 = x_1597;
x_15 = x_1598;
x_16 = x_1599;
x_17 = x_1600;
x_18 = x_1601;
x_19 = x_1607;
goto block_29;
}
else
{
uint8_t x_1611; 
x_1611 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_1604, x_1603);
lean_dec_ref(x_1603);
if (x_1611 == 0)
{
x_10 = x_1608;
x_11 = x_1593;
x_12 = x_1595;
x_13 = x_1596;
x_14 = x_1597;
x_15 = x_1598;
x_16 = x_1599;
x_17 = x_1600;
x_18 = x_1601;
x_19 = x_1607;
goto block_29;
}
else
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; 
x_1612 = lean_st_ref_get(x_1596, x_1607);
x_1613 = lean_ctor_get(x_1612, 0);
lean_inc(x_1613);
x_1614 = lean_ctor_get(x_1612, 1);
lean_inc(x_1614);
lean_dec_ref(x_1612);
x_1615 = lean_ctor_get(x_1613, 0);
lean_inc_ref(x_1615);
lean_dec(x_1613);
lean_inc(x_1601);
lean_inc_ref(x_1600);
lean_inc(x_1599);
lean_inc_ref(x_1598);
x_1616 = l_Lean_Compiler_LCNF_normFunDeclImp(x_1589, x_1593, x_1615, x_1598, x_1599, x_1600, x_1601, x_1614);
if (lean_obj_tag(x_1616) == 0)
{
lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; 
x_1617 = lean_ctor_get(x_1616, 0);
lean_inc(x_1617);
x_1618 = lean_ctor_get(x_1616, 1);
lean_inc(x_1618);
lean_dec_ref(x_1616);
lean_inc(x_1601);
lean_inc_ref(x_1600);
lean_inc(x_1599);
lean_inc_ref(x_1598);
x_1619 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_1617, x_1598, x_1599, x_1600, x_1601, x_1618);
if (lean_obj_tag(x_1619) == 0)
{
lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; 
x_1620 = lean_ctor_get(x_1619, 0);
lean_inc(x_1620);
x_1621 = lean_ctor_get(x_1619, 1);
lean_inc(x_1621);
lean_dec_ref(x_1619);
x_1622 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1596, x_1621);
x_1623 = lean_ctor_get(x_1622, 1);
lean_inc(x_1623);
lean_dec_ref(x_1622);
x_10 = x_1608;
x_11 = x_1620;
x_12 = x_1595;
x_13 = x_1596;
x_14 = x_1597;
x_15 = x_1598;
x_16 = x_1599;
x_17 = x_1600;
x_18 = x_1601;
x_19 = x_1623;
goto block_29;
}
else
{
lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; 
lean_dec_ref(x_1608);
lean_dec(x_1601);
lean_dec_ref(x_1600);
lean_dec(x_1599);
lean_dec_ref(x_1598);
lean_dec_ref(x_1597);
lean_dec(x_1596);
lean_dec_ref(x_1595);
x_1624 = lean_ctor_get(x_1619, 0);
lean_inc(x_1624);
x_1625 = lean_ctor_get(x_1619, 1);
lean_inc(x_1625);
if (lean_is_exclusive(x_1619)) {
 lean_ctor_release(x_1619, 0);
 lean_ctor_release(x_1619, 1);
 x_1626 = x_1619;
} else {
 lean_dec_ref(x_1619);
 x_1626 = lean_box(0);
}
if (lean_is_scalar(x_1626)) {
 x_1627 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1627 = x_1626;
}
lean_ctor_set(x_1627, 0, x_1624);
lean_ctor_set(x_1627, 1, x_1625);
return x_1627;
}
}
else
{
lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; 
lean_dec_ref(x_1608);
lean_dec(x_1601);
lean_dec_ref(x_1600);
lean_dec(x_1599);
lean_dec_ref(x_1598);
lean_dec_ref(x_1597);
lean_dec(x_1596);
lean_dec_ref(x_1595);
x_1628 = lean_ctor_get(x_1616, 0);
lean_inc(x_1628);
x_1629 = lean_ctor_get(x_1616, 1);
lean_inc(x_1629);
if (lean_is_exclusive(x_1616)) {
 lean_ctor_release(x_1616, 0);
 lean_ctor_release(x_1616, 1);
 x_1630 = x_1616;
} else {
 lean_dec_ref(x_1616);
 x_1630 = lean_box(0);
}
if (lean_is_scalar(x_1630)) {
 x_1631 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1631 = x_1630;
}
lean_ctor_set(x_1631, 0, x_1628);
lean_ctor_set(x_1631, 1, x_1629);
return x_1631;
}
}
}
}
else
{
lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; 
lean_dec_ref(x_1608);
lean_dec_ref(x_1604);
lean_dec_ref(x_1603);
x_1632 = lean_st_ref_get(x_1596, x_1607);
x_1633 = lean_ctor_get(x_1632, 0);
lean_inc(x_1633);
x_1634 = lean_ctor_get(x_1632, 1);
lean_inc(x_1634);
lean_dec_ref(x_1632);
x_1635 = lean_ctor_get(x_1633, 0);
lean_inc_ref(x_1635);
lean_dec(x_1633);
lean_inc(x_1601);
lean_inc_ref(x_1600);
lean_inc(x_1599);
lean_inc_ref(x_1598);
x_1636 = l_Lean_Compiler_LCNF_normFunDeclImp(x_1589, x_1593, x_1635, x_1598, x_1599, x_1600, x_1601, x_1634);
if (lean_obj_tag(x_1636) == 0)
{
lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; uint8_t x_1640; lean_object* x_1641; 
x_1637 = lean_ctor_get(x_1636, 0);
lean_inc(x_1637);
x_1638 = lean_ctor_get(x_1636, 1);
lean_inc(x_1638);
lean_dec_ref(x_1636);
x_1639 = lean_box(0);
x_1640 = lean_unbox(x_1606);
lean_dec(x_1606);
x_1641 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_1594, x_1, x_1640, x_1637, x_1639, x_1595, x_1596, x_1597, x_1598, x_1599, x_1600, x_1601, x_1638);
lean_dec_ref(x_1);
return x_1641;
}
else
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; 
lean_dec(x_1606);
lean_dec(x_1601);
lean_dec_ref(x_1600);
lean_dec(x_1599);
lean_dec_ref(x_1598);
lean_dec_ref(x_1597);
lean_dec(x_1596);
lean_dec_ref(x_1595);
lean_dec_ref(x_1594);
lean_dec_ref(x_1);
x_1642 = lean_ctor_get(x_1636, 0);
lean_inc(x_1642);
x_1643 = lean_ctor_get(x_1636, 1);
lean_inc(x_1643);
if (lean_is_exclusive(x_1636)) {
 lean_ctor_release(x_1636, 0);
 lean_ctor_release(x_1636, 1);
 x_1644 = x_1636;
} else {
 lean_dec_ref(x_1636);
 x_1644 = lean_box(0);
}
if (lean_is_scalar(x_1644)) {
 x_1645 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1645 = x_1644;
}
lean_ctor_set(x_1645, 0, x_1642);
lean_ctor_set(x_1645, 1, x_1643);
return x_1645;
}
}
}
}
else
{
lean_object* x_2029; 
lean_dec_ref(x_1588);
lean_dec(x_1586);
lean_dec(x_1584);
lean_dec(x_1583);
lean_dec(x_1582);
lean_dec(x_1581);
lean_dec(x_1580);
lean_dec(x_1579);
lean_dec(x_1578);
lean_dec(x_1577);
lean_dec(x_1576);
lean_dec_ref(x_1575);
lean_dec_ref(x_1574);
lean_dec_ref(x_1573);
lean_dec_ref(x_1);
x_2029 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2029;
}
}
}
else
{
lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; uint8_t x_2073; lean_object* x_2074; uint8_t x_2075; lean_object* x_2076; uint8_t x_2077; 
x_2030 = lean_ctor_get(x_50, 0);
x_2031 = lean_ctor_get(x_50, 2);
x_2032 = lean_ctor_get(x_50, 3);
x_2033 = lean_ctor_get(x_50, 4);
lean_inc(x_2033);
lean_inc(x_2032);
lean_inc(x_2031);
lean_inc(x_2030);
lean_dec(x_50);
x_2034 = l_Lean_Compiler_LCNF_Simp_simp___closed__4;
x_2035 = l_Lean_Compiler_LCNF_Simp_simp___closed__5;
lean_inc_ref(x_2030);
x_2036 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_2036, 0, x_2030);
x_2037 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_2037, 0, x_2030);
x_2038 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2038, 0, x_2036);
lean_ctor_set(x_2038, 1, x_2037);
x_2039 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_2039, 0, x_2033);
x_2040 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_2040, 0, x_2032);
x_2041 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_2041, 0, x_2031);
x_2042 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_2042, 0, x_2038);
lean_ctor_set(x_2042, 1, x_2034);
lean_ctor_set(x_2042, 2, x_2041);
lean_ctor_set(x_2042, 3, x_2040);
lean_ctor_set(x_2042, 4, x_2039);
lean_ctor_set(x_48, 1, x_2035);
lean_ctor_set(x_48, 0, x_2042);
x_2043 = l_ReaderT_instMonad___redArg(x_48);
x_2044 = l_ReaderT_instMonad___redArg(x_2043);
x_2045 = lean_ctor_get(x_2044, 0);
lean_inc_ref(x_2045);
if (lean_is_exclusive(x_2044)) {
 lean_ctor_release(x_2044, 0);
 lean_ctor_release(x_2044, 1);
 x_2046 = x_2044;
} else {
 lean_dec_ref(x_2044);
 x_2046 = lean_box(0);
}
x_2047 = lean_ctor_get(x_2045, 0);
lean_inc_ref(x_2047);
x_2048 = lean_ctor_get(x_2045, 2);
lean_inc_ref(x_2048);
x_2049 = lean_ctor_get(x_2045, 3);
lean_inc_ref(x_2049);
x_2050 = lean_ctor_get(x_2045, 4);
lean_inc_ref(x_2050);
if (lean_is_exclusive(x_2045)) {
 lean_ctor_release(x_2045, 0);
 lean_ctor_release(x_2045, 1);
 lean_ctor_release(x_2045, 2);
 lean_ctor_release(x_2045, 3);
 lean_ctor_release(x_2045, 4);
 x_2051 = x_2045;
} else {
 lean_dec_ref(x_2045);
 x_2051 = lean_box(0);
}
x_2052 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_2053 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_2047);
x_2054 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_2054, 0, x_2047);
x_2055 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_2055, 0, x_2047);
x_2056 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2056, 0, x_2054);
lean_ctor_set(x_2056, 1, x_2055);
x_2057 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_2057, 0, x_2050);
x_2058 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_2058, 0, x_2049);
x_2059 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_2059, 0, x_2048);
if (lean_is_scalar(x_2051)) {
 x_2060 = lean_alloc_ctor(0, 5, 0);
} else {
 x_2060 = x_2051;
}
lean_ctor_set(x_2060, 0, x_2056);
lean_ctor_set(x_2060, 1, x_2052);
lean_ctor_set(x_2060, 2, x_2059);
lean_ctor_set(x_2060, 3, x_2058);
lean_ctor_set(x_2060, 4, x_2057);
if (lean_is_scalar(x_2046)) {
 x_2061 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2061 = x_2046;
}
lean_ctor_set(x_2061, 0, x_2060);
lean_ctor_set(x_2061, 1, x_2053);
x_2062 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_2062);
x_2063 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_2063);
x_2064 = lean_ctor_get(x_7, 2);
lean_inc(x_2064);
x_2065 = lean_ctor_get(x_7, 3);
lean_inc(x_2065);
x_2066 = lean_ctor_get(x_7, 4);
lean_inc(x_2066);
x_2067 = lean_ctor_get(x_7, 5);
lean_inc(x_2067);
x_2068 = lean_ctor_get(x_7, 6);
lean_inc(x_2068);
x_2069 = lean_ctor_get(x_7, 7);
lean_inc(x_2069);
x_2070 = lean_ctor_get(x_7, 8);
lean_inc(x_2070);
x_2071 = lean_ctor_get(x_7, 9);
lean_inc(x_2071);
x_2072 = lean_ctor_get(x_7, 10);
lean_inc(x_2072);
x_2073 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_2074 = lean_ctor_get(x_7, 11);
lean_inc(x_2074);
x_2075 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_2076 = lean_ctor_get(x_7, 12);
lean_inc_ref(x_2076);
x_2077 = lean_nat_dec_eq(x_2065, x_2066);
if (x_2077 == 0)
{
lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; 
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 lean_ctor_release(x_7, 9);
 lean_ctor_release(x_7, 10);
 lean_ctor_release(x_7, 11);
 lean_ctor_release(x_7, 12);
 x_2078 = x_7;
} else {
 lean_dec_ref(x_7);
 x_2078 = lean_box(0);
}
x_2079 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
x_2080 = lean_ctor_get(x_2079, 1);
lean_inc(x_2080);
lean_dec_ref(x_2079);
x_2135 = lean_unsigned_to_nat(1u);
x_2136 = lean_nat_add(x_2065, x_2135);
lean_dec(x_2065);
if (lean_is_scalar(x_2078)) {
 x_2137 = lean_alloc_ctor(0, 13, 2);
} else {
 x_2137 = x_2078;
}
lean_ctor_set(x_2137, 0, x_2062);
lean_ctor_set(x_2137, 1, x_2063);
lean_ctor_set(x_2137, 2, x_2064);
lean_ctor_set(x_2137, 3, x_2136);
lean_ctor_set(x_2137, 4, x_2066);
lean_ctor_set(x_2137, 5, x_2067);
lean_ctor_set(x_2137, 6, x_2068);
lean_ctor_set(x_2137, 7, x_2069);
lean_ctor_set(x_2137, 8, x_2070);
lean_ctor_set(x_2137, 9, x_2071);
lean_ctor_set(x_2137, 10, x_2072);
lean_ctor_set(x_2137, 11, x_2074);
lean_ctor_set(x_2137, 12, x_2076);
lean_ctor_set_uint8(x_2137, sizeof(void*)*13, x_2073);
lean_ctor_set_uint8(x_2137, sizeof(void*)*13 + 1, x_2075);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; uint8_t x_2148; lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; uint8_t x_2173; lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; lean_object* x_2342; lean_object* x_2343; lean_object* x_2344; uint8_t x_2367; 
lean_dec_ref(x_2061);
x_2138 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2138);
x_2139 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2139);
lean_inc_ref(x_2138);
x_2334 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_2077, x_2138, x_3, x_5, x_6, x_2137, x_8, x_2080);
x_2335 = lean_ctor_get(x_2334, 0);
lean_inc(x_2335);
x_2336 = lean_ctor_get(x_2334, 1);
lean_inc(x_2336);
lean_dec_ref(x_2334);
x_2367 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2069_(x_2138, x_2335);
lean_dec_ref(x_2138);
if (x_2367 == 0)
{
goto block_2366;
}
else
{
if (x_2077 == 0)
{
x_2337 = x_2;
x_2338 = x_3;
x_2339 = x_4;
x_2340 = x_5;
x_2341 = x_6;
x_2342 = x_2137;
x_2343 = x_8;
x_2344 = x_2336;
goto block_2363;
}
else
{
goto block_2366;
}
}
block_2163:
{
lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; 
x_2157 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_2157, 0, x_2156);
lean_ctor_set(x_2157, 1, x_2145);
lean_ctor_set(x_2157, 2, x_2146);
lean_ctor_set(x_2157, 3, x_2147);
lean_ctor_set(x_2157, 4, x_2149);
lean_ctor_set(x_2157, 5, x_2150);
lean_ctor_set(x_2157, 6, x_2151);
lean_ctor_set_uint8(x_2157, sizeof(void*)*7, x_2148);
x_2158 = lean_st_ref_set(x_2143, x_2157, x_2154);
x_2159 = lean_ctor_get(x_2158, 1);
lean_inc(x_2159);
lean_dec_ref(x_2158);
x_2160 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_2144, x_2143, x_2140, x_2159);
lean_dec_ref(x_2144);
x_2161 = lean_ctor_get(x_2160, 1);
lean_inc(x_2161);
lean_dec_ref(x_2160);
x_1 = x_2139;
x_2 = x_2153;
x_3 = x_2143;
x_4 = x_2155;
x_5 = x_2152;
x_6 = x_2140;
x_7 = x_2142;
x_8 = x_2141;
x_9 = x_2161;
goto _start;
}
block_2318:
{
if (x_2173 == 0)
{
lean_object* x_2174; 
lean_inc(x_2166);
lean_inc_ref(x_2168);
lean_inc(x_2164);
lean_inc_ref(x_2171);
lean_inc_ref(x_2169);
x_2174 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_2169, x_2171, x_2164, x_2168, x_2166, x_2165);
if (lean_obj_tag(x_2174) == 0)
{
lean_object* x_2175; 
x_2175 = lean_ctor_get(x_2174, 0);
lean_inc(x_2175);
if (lean_obj_tag(x_2175) == 0)
{
lean_object* x_2176; lean_object* x_2177; 
x_2176 = lean_ctor_get(x_2174, 1);
lean_inc(x_2176);
lean_dec_ref(x_2174);
lean_inc(x_2166);
lean_inc_ref(x_2168);
lean_inc(x_2164);
lean_inc_ref(x_2171);
lean_inc_ref(x_2169);
x_2177 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_2169, x_2170, x_2167, x_2171, x_2164, x_2168, x_2166, x_2176);
if (lean_obj_tag(x_2177) == 0)
{
lean_object* x_2178; 
x_2178 = lean_ctor_get(x_2177, 0);
lean_inc(x_2178);
if (lean_obj_tag(x_2178) == 0)
{
lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; 
x_2179 = lean_ctor_get(x_2177, 1);
lean_inc(x_2179);
lean_dec_ref(x_2177);
x_2180 = lean_ctor_get(x_2169, 0);
lean_inc(x_2180);
x_2181 = lean_ctor_get(x_2169, 3);
lean_inc(x_2181);
lean_inc(x_2181);
x_2182 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_2181, x_2179);
x_2183 = lean_ctor_get(x_2182, 0);
lean_inc(x_2183);
if (lean_obj_tag(x_2183) == 0)
{
lean_object* x_2184; lean_object* x_2185; 
x_2184 = lean_ctor_get(x_2182, 1);
lean_inc(x_2184);
lean_dec_ref(x_2182);
lean_inc(x_2166);
lean_inc_ref(x_2168);
lean_inc(x_2164);
lean_inc_ref(x_2171);
lean_inc_ref(x_2172);
lean_inc(x_2167);
lean_inc_ref(x_2170);
lean_inc_ref(x_2139);
lean_inc_ref(x_2169);
x_2185 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_2169, x_2139, x_2170, x_2167, x_2172, x_2171, x_2164, x_2168, x_2166, x_2184);
if (lean_obj_tag(x_2185) == 0)
{
lean_object* x_2186; 
x_2186 = lean_ctor_get(x_2185, 0);
lean_inc(x_2186);
if (lean_obj_tag(x_2186) == 0)
{
lean_object* x_2187; lean_object* x_2188; 
x_2187 = lean_ctor_get(x_2185, 1);
lean_inc(x_2187);
lean_dec_ref(x_2185);
lean_inc(x_2166);
lean_inc_ref(x_2168);
lean_inc(x_2164);
lean_inc_ref(x_2171);
lean_inc_ref(x_2172);
lean_inc(x_2167);
lean_inc_ref(x_2170);
x_2188 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_2181, x_2170, x_2167, x_2172, x_2171, x_2164, x_2168, x_2166, x_2187);
if (lean_obj_tag(x_2188) == 0)
{
lean_object* x_2189; 
x_2189 = lean_ctor_get(x_2188, 0);
lean_inc(x_2189);
if (lean_obj_tag(x_2189) == 0)
{
lean_object* x_2190; lean_object* x_2191; 
x_2190 = lean_ctor_get(x_2188, 1);
lean_inc(x_2190);
lean_dec_ref(x_2188);
lean_inc(x_2166);
lean_inc_ref(x_2168);
lean_inc(x_2164);
lean_inc_ref(x_2171);
lean_inc_ref(x_2172);
lean_inc(x_2167);
lean_inc_ref(x_2170);
x_2191 = l_Lean_Compiler_LCNF_Simp_simp(x_2139, x_2170, x_2167, x_2172, x_2171, x_2164, x_2168, x_2166, x_2190);
if (lean_obj_tag(x_2191) == 0)
{
lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; uint8_t x_2196; 
x_2192 = lean_ctor_get(x_2191, 0);
lean_inc(x_2192);
x_2193 = lean_ctor_get(x_2191, 1);
lean_inc(x_2193);
lean_dec_ref(x_2191);
x_2194 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_2180, x_2167, x_2193);
lean_dec(x_2180);
x_2195 = lean_ctor_get(x_2194, 0);
lean_inc(x_2195);
x_2196 = lean_unbox(x_2195);
lean_dec(x_2195);
if (x_2196 == 0)
{
lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; 
lean_dec_ref(x_2172);
lean_dec_ref(x_2171);
lean_dec_ref(x_2170);
lean_dec_ref(x_2168);
lean_dec(x_2166);
lean_dec_ref(x_1);
x_2197 = lean_ctor_get(x_2194, 1);
lean_inc(x_2197);
lean_dec_ref(x_2194);
x_2198 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_2169, x_2167, x_2164, x_2197);
lean_dec(x_2164);
lean_dec(x_2167);
lean_dec_ref(x_2169);
x_2199 = lean_ctor_get(x_2198, 1);
lean_inc(x_2199);
if (lean_is_exclusive(x_2198)) {
 lean_ctor_release(x_2198, 0);
 lean_ctor_release(x_2198, 1);
 x_2200 = x_2198;
} else {
 lean_dec_ref(x_2198);
 x_2200 = lean_box(0);
}
if (lean_is_scalar(x_2200)) {
 x_2201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2201 = x_2200;
}
lean_ctor_set(x_2201, 0, x_2192);
lean_ctor_set(x_2201, 1, x_2199);
return x_2201;
}
else
{
lean_object* x_2202; lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; 
x_2202 = lean_ctor_get(x_2194, 1);
lean_inc(x_2202);
lean_dec_ref(x_2194);
lean_inc_ref(x_2169);
x_2203 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_2169, x_2170, x_2167, x_2172, x_2171, x_2164, x_2168, x_2166, x_2202);
lean_dec(x_2166);
lean_dec_ref(x_2168);
lean_dec(x_2164);
lean_dec_ref(x_2171);
lean_dec_ref(x_2172);
lean_dec(x_2167);
lean_dec_ref(x_2170);
x_2204 = lean_ctor_get(x_2203, 1);
lean_inc(x_2204);
if (lean_is_exclusive(x_2203)) {
 lean_ctor_release(x_2203, 0);
 lean_ctor_release(x_2203, 1);
 x_2205 = x_2203;
} else {
 lean_dec_ref(x_2203);
 x_2205 = lean_box(0);
}
x_2206 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_2169, x_2192);
lean_dec_ref(x_1);
if (lean_is_scalar(x_2205)) {
 x_2207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2207 = x_2205;
}
lean_ctor_set(x_2207, 0, x_2206);
lean_ctor_set(x_2207, 1, x_2204);
return x_2207;
}
}
else
{
lean_dec(x_2180);
lean_dec_ref(x_2172);
lean_dec_ref(x_2171);
lean_dec_ref(x_2170);
lean_dec_ref(x_2169);
lean_dec_ref(x_2168);
lean_dec(x_2167);
lean_dec(x_2166);
lean_dec(x_2164);
lean_dec_ref(x_1);
return x_2191;
}
}
else
{
lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; 
lean_dec_ref(x_1);
x_2208 = lean_ctor_get(x_2189, 0);
lean_inc(x_2208);
lean_dec_ref(x_2189);
x_2209 = lean_ctor_get(x_2188, 1);
lean_inc(x_2209);
lean_dec_ref(x_2188);
x_2210 = lean_ctor_get(x_2208, 0);
lean_inc(x_2210);
x_2211 = lean_ctor_get(x_2208, 1);
lean_inc(x_2211);
lean_dec(x_2208);
x_2212 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_2180, x_2211, x_2167, x_2164, x_2168, x_2166, x_2209);
if (lean_obj_tag(x_2212) == 0)
{
lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; lean_object* x_2216; 
x_2213 = lean_ctor_get(x_2212, 1);
lean_inc(x_2213);
lean_dec_ref(x_2212);
x_2214 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_2169, x_2167, x_2164, x_2213);
lean_dec_ref(x_2169);
x_2215 = lean_ctor_get(x_2214, 1);
lean_inc(x_2215);
lean_dec_ref(x_2214);
lean_inc(x_2166);
lean_inc_ref(x_2168);
lean_inc(x_2164);
lean_inc_ref(x_2171);
lean_inc_ref(x_2172);
lean_inc(x_2167);
lean_inc_ref(x_2170);
x_2216 = l_Lean_Compiler_LCNF_Simp_simp(x_2139, x_2170, x_2167, x_2172, x_2171, x_2164, x_2168, x_2166, x_2215);
if (lean_obj_tag(x_2216) == 0)
{
lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; 
x_2217 = lean_ctor_get(x_2216, 0);
lean_inc(x_2217);
x_2218 = lean_ctor_get(x_2216, 1);
lean_inc(x_2218);
lean_dec_ref(x_2216);
x_2219 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_2210, x_2217, x_2170, x_2167, x_2172, x_2171, x_2164, x_2168, x_2166, x_2218);
lean_dec(x_2166);
lean_dec_ref(x_2168);
lean_dec(x_2164);
lean_dec_ref(x_2171);
lean_dec_ref(x_2172);
lean_dec(x_2167);
lean_dec_ref(x_2170);
lean_dec(x_2210);
return x_2219;
}
else
{
lean_dec(x_2210);
lean_dec_ref(x_2172);
lean_dec_ref(x_2171);
lean_dec_ref(x_2170);
lean_dec_ref(x_2168);
lean_dec(x_2167);
lean_dec(x_2166);
lean_dec(x_2164);
return x_2216;
}
}
else
{
lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; 
lean_dec(x_2210);
lean_dec_ref(x_2172);
lean_dec_ref(x_2171);
lean_dec_ref(x_2170);
lean_dec_ref(x_2169);
lean_dec_ref(x_2168);
lean_dec(x_2167);
lean_dec(x_2166);
lean_dec(x_2164);
lean_dec_ref(x_2139);
x_2220 = lean_ctor_get(x_2212, 0);
lean_inc(x_2220);
x_2221 = lean_ctor_get(x_2212, 1);
lean_inc(x_2221);
if (lean_is_exclusive(x_2212)) {
 lean_ctor_release(x_2212, 0);
 lean_ctor_release(x_2212, 1);
 x_2222 = x_2212;
} else {
 lean_dec_ref(x_2212);
 x_2222 = lean_box(0);
}
if (lean_is_scalar(x_2222)) {
 x_2223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2223 = x_2222;
}
lean_ctor_set(x_2223, 0, x_2220);
lean_ctor_set(x_2223, 1, x_2221);
return x_2223;
}
}
}
else
{
lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; 
lean_dec(x_2180);
lean_dec_ref(x_2172);
lean_dec_ref(x_2171);
lean_dec_ref(x_2170);
lean_dec_ref(x_2169);
lean_dec_ref(x_2168);
lean_dec(x_2167);
lean_dec(x_2166);
lean_dec(x_2164);
lean_dec_ref(x_2139);
lean_dec_ref(x_1);
x_2224 = lean_ctor_get(x_2188, 0);
lean_inc(x_2224);
x_2225 = lean_ctor_get(x_2188, 1);
lean_inc(x_2225);
if (lean_is_exclusive(x_2188)) {
 lean_ctor_release(x_2188, 0);
 lean_ctor_release(x_2188, 1);
 x_2226 = x_2188;
} else {
 lean_dec_ref(x_2188);
 x_2226 = lean_box(0);
}
if (lean_is_scalar(x_2226)) {
 x_2227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2227 = x_2226;
}
lean_ctor_set(x_2227, 0, x_2224);
lean_ctor_set(x_2227, 1, x_2225);
return x_2227;
}
}
else
{
lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; lean_object* x_2233; 
lean_dec(x_2181);
lean_dec(x_2180);
lean_dec_ref(x_2172);
lean_dec_ref(x_2171);
lean_dec_ref(x_2170);
lean_dec_ref(x_2168);
lean_dec(x_2166);
lean_dec_ref(x_2139);
lean_dec_ref(x_1);
x_2228 = lean_ctor_get(x_2185, 1);
lean_inc(x_2228);
lean_dec_ref(x_2185);
x_2229 = lean_ctor_get(x_2186, 0);
lean_inc(x_2229);
lean_dec_ref(x_2186);
x_2230 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_2169, x_2167, x_2164, x_2228);
lean_dec(x_2164);
lean_dec(x_2167);
lean_dec_ref(x_2169);
x_2231 = lean_ctor_get(x_2230, 1);
lean_inc(x_2231);
if (lean_is_exclusive(x_2230)) {
 lean_ctor_release(x_2230, 0);
 lean_ctor_release(x_2230, 1);
 x_2232 = x_2230;
} else {
 lean_dec_ref(x_2230);
 x_2232 = lean_box(0);
}
if (lean_is_scalar(x_2232)) {
 x_2233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2233 = x_2232;
}
lean_ctor_set(x_2233, 0, x_2229);
lean_ctor_set(x_2233, 1, x_2231);
return x_2233;
}
}
else
{
lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; 
lean_dec(x_2181);
lean_dec(x_2180);
lean_dec_ref(x_2172);
lean_dec_ref(x_2171);
lean_dec_ref(x_2170);
lean_dec_ref(x_2169);
lean_dec_ref(x_2168);
lean_dec(x_2167);
lean_dec(x_2166);
lean_dec(x_2164);
lean_dec_ref(x_2139);
lean_dec_ref(x_1);
x_2234 = lean_ctor_get(x_2185, 0);
lean_inc(x_2234);
x_2235 = lean_ctor_get(x_2185, 1);
lean_inc(x_2235);
if (lean_is_exclusive(x_2185)) {
 lean_ctor_release(x_2185, 0);
 lean_ctor_release(x_2185, 1);
 x_2236 = x_2185;
} else {
 lean_dec_ref(x_2185);
 x_2236 = lean_box(0);
}
if (lean_is_scalar(x_2236)) {
 x_2237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2237 = x_2236;
}
lean_ctor_set(x_2237, 0, x_2234);
lean_ctor_set(x_2237, 1, x_2235);
return x_2237;
}
}
else
{
lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; 
lean_dec(x_2181);
lean_dec_ref(x_1);
x_2238 = lean_ctor_get(x_2182, 1);
lean_inc(x_2238);
lean_dec_ref(x_2182);
x_2239 = lean_ctor_get(x_2183, 0);
lean_inc(x_2239);
lean_dec_ref(x_2183);
x_2240 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_2180, x_2239, x_2167, x_2164, x_2168, x_2166, x_2238);
if (lean_obj_tag(x_2240) == 0)
{
lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; 
x_2241 = lean_ctor_get(x_2240, 1);
lean_inc(x_2241);
lean_dec_ref(x_2240);
x_2242 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_2169, x_2167, x_2164, x_2241);
lean_dec_ref(x_2169);
x_2243 = lean_ctor_get(x_2242, 1);
lean_inc(x_2243);
lean_dec_ref(x_2242);
x_1 = x_2139;
x_2 = x_2170;
x_3 = x_2167;
x_4 = x_2172;
x_5 = x_2171;
x_6 = x_2164;
x_7 = x_2168;
x_8 = x_2166;
x_9 = x_2243;
goto _start;
}
else
{
lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; 
lean_dec_ref(x_2172);
lean_dec_ref(x_2171);
lean_dec_ref(x_2170);
lean_dec_ref(x_2169);
lean_dec_ref(x_2168);
lean_dec(x_2167);
lean_dec(x_2166);
lean_dec(x_2164);
lean_dec_ref(x_2139);
x_2245 = lean_ctor_get(x_2240, 0);
lean_inc(x_2245);
x_2246 = lean_ctor_get(x_2240, 1);
lean_inc(x_2246);
if (lean_is_exclusive(x_2240)) {
 lean_ctor_release(x_2240, 0);
 lean_ctor_release(x_2240, 1);
 x_2247 = x_2240;
} else {
 lean_dec_ref(x_2240);
 x_2247 = lean_box(0);
}
if (lean_is_scalar(x_2247)) {
 x_2248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2248 = x_2247;
}
lean_ctor_set(x_2248, 0, x_2245);
lean_ctor_set(x_2248, 1, x_2246);
return x_2248;
}
}
}
else
{
lean_object* x_2249; lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; 
lean_dec_ref(x_2169);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_2249 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2249 = lean_box(0);
}
x_2250 = lean_ctor_get(x_2177, 1);
lean_inc(x_2250);
lean_dec_ref(x_2177);
x_2251 = lean_ctor_get(x_2178, 0);
lean_inc(x_2251);
lean_dec_ref(x_2178);
if (lean_is_scalar(x_2249)) {
 x_2252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2252 = x_2249;
 lean_ctor_set_tag(x_2252, 1);
}
lean_ctor_set(x_2252, 0, x_2251);
lean_ctor_set(x_2252, 1, x_2139);
x_1 = x_2252;
x_2 = x_2170;
x_3 = x_2167;
x_4 = x_2172;
x_5 = x_2171;
x_6 = x_2164;
x_7 = x_2168;
x_8 = x_2166;
x_9 = x_2250;
goto _start;
}
}
else
{
lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; 
lean_dec_ref(x_2172);
lean_dec_ref(x_2171);
lean_dec_ref(x_2170);
lean_dec_ref(x_2169);
lean_dec_ref(x_2168);
lean_dec(x_2167);
lean_dec(x_2166);
lean_dec(x_2164);
lean_dec_ref(x_2139);
lean_dec_ref(x_1);
x_2254 = lean_ctor_get(x_2177, 0);
lean_inc(x_2254);
x_2255 = lean_ctor_get(x_2177, 1);
lean_inc(x_2255);
if (lean_is_exclusive(x_2177)) {
 lean_ctor_release(x_2177, 0);
 lean_ctor_release(x_2177, 1);
 x_2256 = x_2177;
} else {
 lean_dec_ref(x_2177);
 x_2256 = lean_box(0);
}
if (lean_is_scalar(x_2256)) {
 x_2257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2257 = x_2256;
}
lean_ctor_set(x_2257, 0, x_2254);
lean_ctor_set(x_2257, 1, x_2255);
return x_2257;
}
}
else
{
lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; 
lean_dec_ref(x_2169);
lean_dec_ref(x_1);
x_2258 = lean_ctor_get(x_2174, 1);
lean_inc(x_2258);
lean_dec_ref(x_2174);
x_2259 = lean_ctor_get(x_2175, 0);
lean_inc(x_2259);
lean_dec_ref(x_2175);
x_2260 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_2167, x_2258);
x_2261 = lean_ctor_get(x_2260, 1);
lean_inc(x_2261);
lean_dec_ref(x_2260);
lean_inc(x_2166);
lean_inc_ref(x_2168);
lean_inc(x_2164);
lean_inc_ref(x_2171);
lean_inc_ref(x_2172);
lean_inc(x_2167);
lean_inc_ref(x_2170);
x_2262 = l_Lean_Compiler_LCNF_Simp_simp(x_2139, x_2170, x_2167, x_2172, x_2171, x_2164, x_2168, x_2166, x_2261);
if (lean_obj_tag(x_2262) == 0)
{
lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; 
x_2263 = lean_ctor_get(x_2262, 0);
lean_inc(x_2263);
x_2264 = lean_ctor_get(x_2262, 1);
lean_inc(x_2264);
lean_dec_ref(x_2262);
x_2265 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_2259, x_2263, x_2170, x_2167, x_2172, x_2171, x_2164, x_2168, x_2166, x_2264);
lean_dec(x_2166);
lean_dec_ref(x_2168);
lean_dec(x_2164);
lean_dec_ref(x_2171);
lean_dec_ref(x_2172);
lean_dec(x_2167);
lean_dec_ref(x_2170);
lean_dec(x_2259);
return x_2265;
}
else
{
lean_dec(x_2259);
lean_dec_ref(x_2172);
lean_dec_ref(x_2171);
lean_dec_ref(x_2170);
lean_dec_ref(x_2168);
lean_dec(x_2167);
lean_dec(x_2166);
lean_dec(x_2164);
return x_2262;
}
}
}
else
{
lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; 
lean_dec_ref(x_2172);
lean_dec_ref(x_2171);
lean_dec_ref(x_2170);
lean_dec_ref(x_2169);
lean_dec_ref(x_2168);
lean_dec(x_2167);
lean_dec(x_2166);
lean_dec(x_2164);
lean_dec_ref(x_2139);
lean_dec_ref(x_1);
x_2266 = lean_ctor_get(x_2174, 0);
lean_inc(x_2266);
x_2267 = lean_ctor_get(x_2174, 1);
lean_inc(x_2267);
if (lean_is_exclusive(x_2174)) {
 lean_ctor_release(x_2174, 0);
 lean_ctor_release(x_2174, 1);
 x_2268 = x_2174;
} else {
 lean_dec_ref(x_2174);
 x_2268 = lean_box(0);
}
if (lean_is_scalar(x_2268)) {
 x_2269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2269 = x_2268;
}
lean_ctor_set(x_2269, 0, x_2266);
lean_ctor_set(x_2269, 1, x_2267);
return x_2269;
}
}
else
{
lean_object* x_2270; lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; uint8_t x_2277; lean_object* x_2278; lean_object* x_2279; lean_object* x_2280; lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; lean_object* x_2285; lean_object* x_2286; uint64_t x_2287; uint64_t x_2288; uint64_t x_2289; uint64_t x_2290; uint64_t x_2291; uint64_t x_2292; uint64_t x_2293; size_t x_2294; size_t x_2295; size_t x_2296; size_t x_2297; size_t x_2298; lean_object* x_2299; uint8_t x_2300; 
lean_dec_ref(x_1);
x_2270 = lean_st_ref_take(x_2167, x_2165);
x_2271 = lean_ctor_get(x_2270, 0);
lean_inc(x_2271);
x_2272 = lean_ctor_get(x_2271, 0);
lean_inc_ref(x_2272);
x_2273 = lean_ctor_get(x_2270, 1);
lean_inc(x_2273);
lean_dec_ref(x_2270);
x_2274 = lean_ctor_get(x_2271, 1);
lean_inc_ref(x_2274);
x_2275 = lean_ctor_get(x_2271, 2);
lean_inc(x_2275);
x_2276 = lean_ctor_get(x_2271, 3);
lean_inc_ref(x_2276);
x_2277 = lean_ctor_get_uint8(x_2271, sizeof(void*)*7);
x_2278 = lean_ctor_get(x_2271, 4);
lean_inc(x_2278);
x_2279 = lean_ctor_get(x_2271, 5);
lean_inc(x_2279);
x_2280 = lean_ctor_get(x_2271, 6);
lean_inc(x_2280);
lean_dec(x_2271);
x_2281 = lean_ctor_get(x_2272, 0);
lean_inc(x_2281);
x_2282 = lean_ctor_get(x_2272, 1);
lean_inc_ref(x_2282);
if (lean_is_exclusive(x_2272)) {
 lean_ctor_release(x_2272, 0);
 lean_ctor_release(x_2272, 1);
 x_2283 = x_2272;
} else {
 lean_dec_ref(x_2272);
 x_2283 = lean_box(0);
}
x_2284 = lean_ctor_get(x_2169, 0);
lean_inc(x_2284);
x_2285 = lean_box(0);
x_2286 = lean_array_get_size(x_2282);
x_2287 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_2284);
x_2288 = 32;
x_2289 = lean_uint64_shift_right(x_2287, x_2288);
x_2290 = lean_uint64_xor(x_2287, x_2289);
x_2291 = 16;
x_2292 = lean_uint64_shift_right(x_2290, x_2291);
x_2293 = lean_uint64_xor(x_2290, x_2292);
x_2294 = lean_uint64_to_usize(x_2293);
x_2295 = lean_usize_of_nat(x_2286);
lean_dec(x_2286);
x_2296 = 1;
x_2297 = lean_usize_sub(x_2295, x_2296);
x_2298 = lean_usize_land(x_2294, x_2297);
x_2299 = lean_array_uget(x_2282, x_2298);
x_2300 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_2284, x_2299);
if (x_2300 == 0)
{
lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; uint8_t x_2309; 
x_2301 = lean_nat_add(x_2281, x_2135);
lean_dec(x_2281);
x_2302 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2302, 0, x_2284);
lean_ctor_set(x_2302, 1, x_2285);
lean_ctor_set(x_2302, 2, x_2299);
x_2303 = lean_array_uset(x_2282, x_2298, x_2302);
x_2304 = lean_unsigned_to_nat(4u);
x_2305 = lean_nat_mul(x_2301, x_2304);
x_2306 = lean_unsigned_to_nat(3u);
x_2307 = lean_nat_div(x_2305, x_2306);
lean_dec(x_2305);
x_2308 = lean_array_get_size(x_2303);
x_2309 = lean_nat_dec_le(x_2307, x_2308);
lean_dec(x_2308);
lean_dec(x_2307);
if (x_2309 == 0)
{
lean_object* x_2310; lean_object* x_2311; 
x_2310 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_2303);
if (lean_is_scalar(x_2283)) {
 x_2311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2311 = x_2283;
}
lean_ctor_set(x_2311, 0, x_2301);
lean_ctor_set(x_2311, 1, x_2310);
x_2140 = x_2164;
x_2141 = x_2166;
x_2142 = x_2168;
x_2143 = x_2167;
x_2144 = x_2169;
x_2145 = x_2274;
x_2146 = x_2275;
x_2147 = x_2276;
x_2148 = x_2277;
x_2149 = x_2278;
x_2150 = x_2279;
x_2151 = x_2280;
x_2152 = x_2171;
x_2153 = x_2170;
x_2154 = x_2273;
x_2155 = x_2172;
x_2156 = x_2311;
goto block_2163;
}
else
{
lean_object* x_2312; 
if (lean_is_scalar(x_2283)) {
 x_2312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2312 = x_2283;
}
lean_ctor_set(x_2312, 0, x_2301);
lean_ctor_set(x_2312, 1, x_2303);
x_2140 = x_2164;
x_2141 = x_2166;
x_2142 = x_2168;
x_2143 = x_2167;
x_2144 = x_2169;
x_2145 = x_2274;
x_2146 = x_2275;
x_2147 = x_2276;
x_2148 = x_2277;
x_2149 = x_2278;
x_2150 = x_2279;
x_2151 = x_2280;
x_2152 = x_2171;
x_2153 = x_2170;
x_2154 = x_2273;
x_2155 = x_2172;
x_2156 = x_2312;
goto block_2163;
}
}
else
{
lean_object* x_2313; lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; lean_object* x_2317; 
x_2313 = lean_box(0);
x_2314 = lean_array_uset(x_2282, x_2298, x_2313);
x_2315 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_2284, x_2285, x_2299);
x_2316 = lean_array_uset(x_2314, x_2298, x_2315);
if (lean_is_scalar(x_2283)) {
 x_2317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2317 = x_2283;
}
lean_ctor_set(x_2317, 0, x_2281);
lean_ctor_set(x_2317, 1, x_2316);
x_2140 = x_2164;
x_2141 = x_2166;
x_2142 = x_2168;
x_2143 = x_2167;
x_2144 = x_2169;
x_2145 = x_2274;
x_2146 = x_2275;
x_2147 = x_2276;
x_2148 = x_2277;
x_2149 = x_2278;
x_2150 = x_2279;
x_2151 = x_2280;
x_2152 = x_2171;
x_2153 = x_2170;
x_2154 = x_2273;
x_2155 = x_2172;
x_2156 = x_2317;
goto block_2163;
}
}
}
block_2333:
{
uint8_t x_2330; 
x_2330 = l_Lean_Expr_isErased(x_2320);
lean_dec_ref(x_2320);
if (x_2330 == 0)
{
lean_dec(x_2321);
x_2164 = x_2326;
x_2165 = x_2329;
x_2166 = x_2328;
x_2167 = x_2323;
x_2168 = x_2327;
x_2169 = x_2319;
x_2170 = x_2322;
x_2171 = x_2325;
x_2172 = x_2324;
x_2173 = x_2077;
goto block_2318;
}
else
{
lean_object* x_2331; uint8_t x_2332; 
x_2331 = lean_box(1);
x_2332 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1209_(x_2321, x_2331);
lean_dec(x_2321);
if (x_2332 == 0)
{
x_2164 = x_2326;
x_2165 = x_2329;
x_2166 = x_2328;
x_2167 = x_2323;
x_2168 = x_2327;
x_2169 = x_2319;
x_2170 = x_2322;
x_2171 = x_2325;
x_2172 = x_2324;
x_2173 = x_2330;
goto block_2318;
}
else
{
x_2164 = x_2326;
x_2165 = x_2329;
x_2166 = x_2328;
x_2167 = x_2323;
x_2168 = x_2327;
x_2169 = x_2319;
x_2170 = x_2322;
x_2171 = x_2325;
x_2172 = x_2324;
x_2173 = x_2077;
goto block_2318;
}
}
}
block_2363:
{
lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; 
x_2345 = lean_ctor_get(x_2335, 2);
lean_inc_ref(x_2345);
x_2346 = lean_ctor_get(x_2335, 3);
lean_inc(x_2346);
lean_inc(x_2343);
lean_inc_ref(x_2342);
lean_inc(x_2341);
lean_inc_ref(x_2340);
lean_inc_ref(x_2339);
lean_inc(x_2346);
x_2347 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_2346, x_2337, x_2339, x_2340, x_2341, x_2342, x_2343, x_2344);
if (lean_obj_tag(x_2347) == 0)
{
lean_object* x_2348; 
x_2348 = lean_ctor_get(x_2347, 0);
lean_inc(x_2348);
if (lean_obj_tag(x_2348) == 0)
{
lean_object* x_2349; 
x_2349 = lean_ctor_get(x_2347, 1);
lean_inc(x_2349);
lean_dec_ref(x_2347);
x_2319 = x_2335;
x_2320 = x_2345;
x_2321 = x_2346;
x_2322 = x_2337;
x_2323 = x_2338;
x_2324 = x_2339;
x_2325 = x_2340;
x_2326 = x_2341;
x_2327 = x_2342;
x_2328 = x_2343;
x_2329 = x_2349;
goto block_2333;
}
else
{
lean_object* x_2350; lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; lean_object* x_2355; lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; 
lean_dec(x_2346);
lean_dec_ref(x_2345);
x_2350 = lean_ctor_get(x_2347, 1);
lean_inc(x_2350);
lean_dec_ref(x_2347);
x_2351 = lean_ctor_get(x_2348, 0);
lean_inc(x_2351);
lean_dec_ref(x_2348);
x_2352 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_2338, x_2350);
x_2353 = lean_ctor_get(x_2352, 1);
lean_inc(x_2353);
lean_dec_ref(x_2352);
x_2354 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_2335, x_2351, x_2341, x_2353);
x_2355 = lean_ctor_get(x_2354, 0);
lean_inc(x_2355);
x_2356 = lean_ctor_get(x_2354, 1);
lean_inc(x_2356);
lean_dec_ref(x_2354);
x_2357 = lean_ctor_get(x_2355, 2);
lean_inc_ref(x_2357);
x_2358 = lean_ctor_get(x_2355, 3);
lean_inc(x_2358);
x_2319 = x_2355;
x_2320 = x_2357;
x_2321 = x_2358;
x_2322 = x_2337;
x_2323 = x_2338;
x_2324 = x_2339;
x_2325 = x_2340;
x_2326 = x_2341;
x_2327 = x_2342;
x_2328 = x_2343;
x_2329 = x_2356;
goto block_2333;
}
}
else
{
lean_object* x_2359; lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; 
lean_dec(x_2346);
lean_dec_ref(x_2345);
lean_dec(x_2343);
lean_dec_ref(x_2342);
lean_dec(x_2341);
lean_dec_ref(x_2340);
lean_dec_ref(x_2339);
lean_dec(x_2338);
lean_dec_ref(x_2337);
lean_dec(x_2335);
lean_dec_ref(x_2139);
lean_dec_ref(x_1);
x_2359 = lean_ctor_get(x_2347, 0);
lean_inc(x_2359);
x_2360 = lean_ctor_get(x_2347, 1);
lean_inc(x_2360);
if (lean_is_exclusive(x_2347)) {
 lean_ctor_release(x_2347, 0);
 lean_ctor_release(x_2347, 1);
 x_2361 = x_2347;
} else {
 lean_dec_ref(x_2347);
 x_2361 = lean_box(0);
}
if (lean_is_scalar(x_2361)) {
 x_2362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2362 = x_2361;
}
lean_ctor_set(x_2362, 0, x_2359);
lean_ctor_set(x_2362, 1, x_2360);
return x_2362;
}
}
block_2366:
{
lean_object* x_2364; lean_object* x_2365; 
x_2364 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_2336);
x_2365 = lean_ctor_get(x_2364, 1);
lean_inc(x_2365);
lean_dec_ref(x_2364);
x_2337 = x_2;
x_2338 = x_3;
x_2339 = x_4;
x_2340 = x_5;
x_2341 = x_6;
x_2342 = x_2137;
x_2343 = x_8;
x_2344 = x_2365;
goto block_2363;
}
}
case 3:
{
lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; 
lean_dec_ref(x_2061);
x_2368 = lean_ctor_get(x_1, 0);
lean_inc(x_2368);
x_2369 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2369);
x_2370 = lean_st_ref_get(x_3, x_2080);
x_2371 = lean_ctor_get(x_2370, 0);
lean_inc(x_2371);
x_2372 = lean_ctor_get(x_2370, 1);
lean_inc(x_2372);
lean_dec_ref(x_2370);
x_2373 = lean_ctor_get(x_2371, 0);
lean_inc_ref(x_2373);
lean_dec(x_2371);
x_2374 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_2373, x_2368, x_2077);
lean_dec_ref(x_2373);
if (lean_obj_tag(x_2374) == 0)
{
lean_object* x_2375; lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; lean_object* x_2380; lean_object* x_2384; 
x_2375 = lean_ctor_get(x_2374, 0);
lean_inc(x_2375);
lean_dec_ref(x_2374);
x_2376 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_2077, x_2369, x_3, x_2372);
x_2377 = lean_ctor_get(x_2376, 0);
lean_inc(x_2377);
x_2378 = lean_ctor_get(x_2376, 1);
lean_inc(x_2378);
if (lean_is_exclusive(x_2376)) {
 lean_ctor_release(x_2376, 0);
 lean_ctor_release(x_2376, 1);
 x_2379 = x_2376;
} else {
 lean_dec_ref(x_2376);
 x_2379 = lean_box(0);
}
lean_inc(x_2377);
x_2384 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_2375, x_2377, x_2, x_3, x_4, x_5, x_6, x_2137, x_8, x_2378);
if (lean_obj_tag(x_2384) == 0)
{
lean_object* x_2385; 
x_2385 = lean_ctor_get(x_2384, 0);
lean_inc(x_2385);
if (lean_obj_tag(x_2385) == 0)
{
lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; uint8_t x_2391; 
lean_dec_ref(x_2137);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_2386 = lean_ctor_get(x_2384, 1);
lean_inc(x_2386);
lean_dec_ref(x_2384);
lean_inc(x_2375);
x_2387 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_2375, x_3, x_2386);
x_2388 = lean_ctor_get(x_2387, 1);
lean_inc(x_2388);
lean_dec_ref(x_2387);
x_2389 = lean_unsigned_to_nat(0u);
x_2390 = lean_array_get_size(x_2377);
x_2391 = lean_nat_dec_lt(x_2389, x_2390);
if (x_2391 == 0)
{
lean_dec(x_2390);
lean_dec(x_3);
x_2380 = x_2388;
goto block_2383;
}
else
{
uint8_t x_2392; 
x_2392 = lean_nat_dec_le(x_2390, x_2390);
if (x_2392 == 0)
{
lean_dec(x_2390);
lean_dec(x_3);
x_2380 = x_2388;
goto block_2383;
}
else
{
lean_object* x_2393; size_t x_2394; size_t x_2395; lean_object* x_2396; lean_object* x_2397; 
x_2393 = lean_box(0);
x_2394 = 0;
x_2395 = lean_usize_of_nat(x_2390);
lean_dec(x_2390);
x_2396 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_2377, x_2394, x_2395, x_2393, x_3, x_2388);
lean_dec(x_3);
x_2397 = lean_ctor_get(x_2396, 1);
lean_inc(x_2397);
lean_dec_ref(x_2396);
x_2380 = x_2397;
goto block_2383;
}
}
}
else
{
lean_object* x_2398; lean_object* x_2399; 
lean_dec(x_2379);
lean_dec(x_2377);
lean_dec(x_2375);
lean_dec_ref(x_1);
x_2398 = lean_ctor_get(x_2384, 1);
lean_inc(x_2398);
lean_dec_ref(x_2384);
x_2399 = lean_ctor_get(x_2385, 0);
lean_inc(x_2399);
lean_dec_ref(x_2385);
x_1 = x_2399;
x_7 = x_2137;
x_9 = x_2398;
goto _start;
}
}
else
{
lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; lean_object* x_2404; 
lean_dec(x_2379);
lean_dec(x_2377);
lean_dec(x_2375);
lean_dec_ref(x_2137);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2401 = lean_ctor_get(x_2384, 0);
lean_inc(x_2401);
x_2402 = lean_ctor_get(x_2384, 1);
lean_inc(x_2402);
if (lean_is_exclusive(x_2384)) {
 lean_ctor_release(x_2384, 0);
 lean_ctor_release(x_2384, 1);
 x_2403 = x_2384;
} else {
 lean_dec_ref(x_2384);
 x_2403 = lean_box(0);
}
if (lean_is_scalar(x_2403)) {
 x_2404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2404 = x_2403;
}
lean_ctor_set(x_2404, 0, x_2401);
lean_ctor_set(x_2404, 1, x_2402);
return x_2404;
}
block_2383:
{
lean_object* x_2381; lean_object* x_2382; 
x_2381 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_1, x_2375, x_2377);
lean_dec_ref(x_1);
if (lean_is_scalar(x_2379)) {
 x_2382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2382 = x_2379;
}
lean_ctor_set(x_2382, 0, x_2381);
lean_ctor_set(x_2382, 1, x_2380);
return x_2382;
}
}
else
{
lean_object* x_2405; 
lean_dec_ref(x_2369);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2405 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_2137, x_8, x_2372);
lean_dec(x_8);
lean_dec_ref(x_2137);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_2405;
}
}
case 4:
{
lean_object* x_2406; lean_object* x_2407; 
x_2406 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2406);
lean_inc(x_8);
lean_inc_ref(x_2137);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_2406);
x_2407 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_2406, x_2, x_3, x_4, x_5, x_6, x_2137, x_8, x_2080);
if (lean_obj_tag(x_2407) == 0)
{
lean_object* x_2408; 
x_2408 = lean_ctor_get(x_2407, 0);
lean_inc(x_2408);
if (lean_obj_tag(x_2408) == 0)
{
lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; 
x_2409 = lean_ctor_get(x_2407, 1);
lean_inc(x_2409);
lean_dec_ref(x_2407);
x_2410 = lean_st_ref_get(x_3, x_2409);
x_2411 = lean_ctor_get(x_2410, 0);
lean_inc(x_2411);
x_2412 = lean_ctor_get(x_2410, 1);
lean_inc(x_2412);
lean_dec_ref(x_2410);
x_2413 = lean_ctor_get(x_2406, 1);
lean_inc_ref(x_2413);
x_2414 = lean_ctor_get(x_2406, 2);
lean_inc(x_2414);
x_2415 = lean_ctor_get(x_2406, 3);
lean_inc_ref(x_2415);
lean_dec_ref(x_2406);
x_2416 = lean_ctor_get(x_2411, 0);
lean_inc_ref(x_2416);
lean_dec(x_2411);
x_2417 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_2416, x_2414, x_2077);
lean_dec_ref(x_2416);
if (lean_obj_tag(x_2417) == 0)
{
lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; 
x_2418 = lean_ctor_get(x_2417, 0);
lean_inc(x_2418);
lean_dec_ref(x_2417);
x_2419 = lean_st_ref_get(x_3, x_2412);
x_2420 = lean_ctor_get(x_2419, 0);
lean_inc(x_2420);
x_2421 = lean_ctor_get(x_2419, 1);
lean_inc(x_2421);
lean_dec_ref(x_2419);
x_2422 = lean_box(x_2077);
lean_inc(x_2418);
x_2423 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__1___boxed), 11, 2);
lean_closure_set(x_2423, 0, x_2418);
lean_closure_set(x_2423, 1, x_2422);
x_2424 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_2061, x_2415, x_2423);
lean_inc(x_8);
lean_inc_ref(x_2137);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_2425 = lean_apply_8(x_2424, x_2, x_3, x_4, x_5, x_6, x_2137, x_8, x_2421);
if (lean_obj_tag(x_2425) == 0)
{
lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; 
x_2426 = lean_ctor_get(x_2425, 0);
lean_inc(x_2426);
x_2427 = lean_ctor_get(x_2425, 1);
lean_inc(x_2427);
lean_dec_ref(x_2425);
lean_inc(x_6);
lean_inc(x_3);
x_2428 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_2426, x_2, x_3, x_4, x_5, x_6, x_2137, x_8, x_2427);
if (lean_obj_tag(x_2428) == 0)
{
lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; lean_object* x_2434; lean_object* x_2435; lean_object* x_2442; uint8_t x_2443; 
x_2429 = lean_ctor_get(x_2428, 0);
lean_inc(x_2429);
x_2430 = lean_ctor_get(x_2428, 1);
lean_inc(x_2430);
if (lean_is_exclusive(x_2428)) {
 lean_ctor_release(x_2428, 0);
 lean_ctor_release(x_2428, 1);
 x_2431 = x_2428;
} else {
 lean_dec_ref(x_2428);
 x_2431 = lean_box(0);
}
x_2432 = lean_ctor_get(x_2420, 0);
lean_inc_ref(x_2432);
lean_dec(x_2420);
x_2433 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_2432, x_2077, x_2413);
lean_dec_ref(x_2432);
x_2442 = lean_array_get_size(x_2429);
x_2443 = lean_nat_dec_eq(x_2442, x_2135);
lean_dec(x_2442);
if (x_2443 == 0)
{
lean_dec(x_2431);
lean_dec(x_6);
x_2434 = x_3;
x_2435 = x_2430;
goto block_2441;
}
else
{
lean_object* x_2444; lean_object* x_2445; 
x_2444 = lean_unsigned_to_nat(0u);
x_2445 = lean_array_fget(x_2429, x_2444);
if (lean_obj_tag(x_2445) == 0)
{
lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; lean_object* x_2454; lean_object* x_2455; uint8_t x_2464; lean_object* x_2465; uint8_t x_2467; 
lean_dec(x_2431);
x_2446 = lean_ctor_get(x_2445, 1);
lean_inc_ref(x_2446);
x_2447 = lean_ctor_get(x_2445, 2);
lean_inc_ref(x_2447);
lean_dec_ref(x_2445);
x_2454 = lean_array_get_size(x_2446);
x_2467 = lean_nat_dec_lt(x_2444, x_2454);
if (x_2467 == 0)
{
x_2464 = x_2077;
x_2465 = x_2430;
goto block_2466;
}
else
{
if (x_2467 == 0)
{
x_2464 = x_2077;
x_2465 = x_2430;
goto block_2466;
}
else
{
size_t x_2468; size_t x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; uint8_t x_2473; 
x_2468 = 0;
x_2469 = lean_usize_of_nat(x_2454);
x_2470 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_2446, x_2468, x_2469, x_3, x_2430);
x_2471 = lean_ctor_get(x_2470, 0);
lean_inc(x_2471);
x_2472 = lean_ctor_get(x_2470, 1);
lean_inc(x_2472);
lean_dec_ref(x_2470);
x_2473 = lean_unbox(x_2471);
lean_dec(x_2471);
x_2464 = x_2473;
x_2465 = x_2472;
goto block_2466;
}
}
block_2453:
{
lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2452; 
x_2449 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_2448);
lean_dec(x_3);
x_2450 = lean_ctor_get(x_2449, 1);
lean_inc(x_2450);
if (lean_is_exclusive(x_2449)) {
 lean_ctor_release(x_2449, 0);
 lean_ctor_release(x_2449, 1);
 x_2451 = x_2449;
} else {
 lean_dec_ref(x_2449);
 x_2451 = lean_box(0);
}
if (lean_is_scalar(x_2451)) {
 x_2452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2452 = x_2451;
}
lean_ctor_set(x_2452, 0, x_2447);
lean_ctor_set(x_2452, 1, x_2450);
return x_2452;
}
block_2463:
{
uint8_t x_2456; 
x_2456 = lean_nat_dec_lt(x_2444, x_2454);
if (x_2456 == 0)
{
lean_dec(x_2454);
lean_dec_ref(x_2446);
lean_dec(x_6);
x_2448 = x_2455;
goto block_2453;
}
else
{
uint8_t x_2457; 
x_2457 = lean_nat_dec_le(x_2454, x_2454);
if (x_2457 == 0)
{
lean_dec(x_2454);
lean_dec_ref(x_2446);
lean_dec(x_6);
x_2448 = x_2455;
goto block_2453;
}
else
{
lean_object* x_2458; size_t x_2459; size_t x_2460; lean_object* x_2461; lean_object* x_2462; 
x_2458 = lean_box(0);
x_2459 = 0;
x_2460 = lean_usize_of_nat(x_2454);
lean_dec(x_2454);
x_2461 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_2446, x_2459, x_2460, x_2458, x_6, x_2455);
lean_dec(x_6);
lean_dec_ref(x_2446);
x_2462 = lean_ctor_get(x_2461, 1);
lean_inc(x_2462);
lean_dec_ref(x_2461);
x_2448 = x_2462;
goto block_2453;
}
}
}
block_2466:
{
if (x_2464 == 0)
{
lean_dec_ref(x_2433);
lean_dec(x_2429);
lean_dec(x_2418);
lean_dec_ref(x_1);
x_2455 = x_2465;
goto block_2463;
}
else
{
if (x_2077 == 0)
{
lean_dec(x_2454);
lean_dec_ref(x_2447);
lean_dec_ref(x_2446);
lean_dec(x_6);
x_2434 = x_3;
x_2435 = x_2465;
goto block_2441;
}
else
{
lean_dec_ref(x_2433);
lean_dec(x_2429);
lean_dec(x_2418);
lean_dec_ref(x_1);
x_2455 = x_2465;
goto block_2463;
}
}
}
}
else
{
lean_object* x_2474; lean_object* x_2475; 
lean_dec_ref(x_2433);
lean_dec(x_2429);
lean_dec(x_2418);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_2474 = lean_ctor_get(x_2445, 0);
lean_inc_ref(x_2474);
lean_dec_ref(x_2445);
if (lean_is_scalar(x_2431)) {
 x_2475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2475 = x_2431;
}
lean_ctor_set(x_2475, 0, x_2474);
lean_ctor_set(x_2475, 1, x_2430);
return x_2475;
}
}
block_2441:
{
lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; 
lean_inc(x_2418);
x_2436 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_2418, x_2434, x_2435);
lean_dec(x_2434);
x_2437 = lean_ctor_get(x_2436, 1);
lean_inc(x_2437);
if (lean_is_exclusive(x_2436)) {
 lean_ctor_release(x_2436, 0);
 lean_ctor_release(x_2436, 1);
 x_2438 = x_2436;
} else {
 lean_dec_ref(x_2436);
 x_2438 = lean_box(0);
}
x_2439 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_1, x_2433, x_2418, x_2429);
if (lean_is_scalar(x_2438)) {
 x_2440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2440 = x_2438;
}
lean_ctor_set(x_2440, 0, x_2439);
lean_ctor_set(x_2440, 1, x_2437);
return x_2440;
}
}
else
{
lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; 
lean_dec(x_2420);
lean_dec(x_2418);
lean_dec_ref(x_2413);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_2476 = lean_ctor_get(x_2428, 0);
lean_inc(x_2476);
x_2477 = lean_ctor_get(x_2428, 1);
lean_inc(x_2477);
if (lean_is_exclusive(x_2428)) {
 lean_ctor_release(x_2428, 0);
 lean_ctor_release(x_2428, 1);
 x_2478 = x_2428;
} else {
 lean_dec_ref(x_2428);
 x_2478 = lean_box(0);
}
if (lean_is_scalar(x_2478)) {
 x_2479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2479 = x_2478;
}
lean_ctor_set(x_2479, 0, x_2476);
lean_ctor_set(x_2479, 1, x_2477);
return x_2479;
}
}
else
{
lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; 
lean_dec(x_2420);
lean_dec(x_2418);
lean_dec_ref(x_2413);
lean_dec_ref(x_2137);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2480 = lean_ctor_get(x_2425, 0);
lean_inc(x_2480);
x_2481 = lean_ctor_get(x_2425, 1);
lean_inc(x_2481);
if (lean_is_exclusive(x_2425)) {
 lean_ctor_release(x_2425, 0);
 lean_ctor_release(x_2425, 1);
 x_2482 = x_2425;
} else {
 lean_dec_ref(x_2425);
 x_2482 = lean_box(0);
}
if (lean_is_scalar(x_2482)) {
 x_2483 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2483 = x_2482;
}
lean_ctor_set(x_2483, 0, x_2480);
lean_ctor_set(x_2483, 1, x_2481);
return x_2483;
}
}
else
{
lean_object* x_2484; 
lean_dec_ref(x_2415);
lean_dec_ref(x_2413);
lean_dec_ref(x_2061);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2484 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_2137, x_8, x_2412);
lean_dec(x_8);
lean_dec_ref(x_2137);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_2484;
}
}
else
{
lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; 
lean_dec_ref(x_2406);
lean_dec_ref(x_2137);
lean_dec_ref(x_2061);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2485 = lean_ctor_get(x_2407, 1);
lean_inc(x_2485);
if (lean_is_exclusive(x_2407)) {
 lean_ctor_release(x_2407, 0);
 lean_ctor_release(x_2407, 1);
 x_2486 = x_2407;
} else {
 lean_dec_ref(x_2407);
 x_2486 = lean_box(0);
}
x_2487 = lean_ctor_get(x_2408, 0);
lean_inc(x_2487);
lean_dec_ref(x_2408);
if (lean_is_scalar(x_2486)) {
 x_2488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2488 = x_2486;
}
lean_ctor_set(x_2488, 0, x_2487);
lean_ctor_set(x_2488, 1, x_2485);
return x_2488;
}
}
else
{
lean_object* x_2489; lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; 
lean_dec_ref(x_2406);
lean_dec_ref(x_2137);
lean_dec_ref(x_2061);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2489 = lean_ctor_get(x_2407, 0);
lean_inc(x_2489);
x_2490 = lean_ctor_get(x_2407, 1);
lean_inc(x_2490);
if (lean_is_exclusive(x_2407)) {
 lean_ctor_release(x_2407, 0);
 lean_ctor_release(x_2407, 1);
 x_2491 = x_2407;
} else {
 lean_dec_ref(x_2407);
 x_2491 = lean_box(0);
}
if (lean_is_scalar(x_2491)) {
 x_2492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2492 = x_2491;
}
lean_ctor_set(x_2492, 0, x_2489);
lean_ctor_set(x_2492, 1, x_2490);
return x_2492;
}
}
case 5:
{
lean_object* x_2493; lean_object* x_2494; lean_object* x_2495; lean_object* x_2496; lean_object* x_2497; lean_object* x_2498; 
lean_dec_ref(x_2061);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_2493 = lean_ctor_get(x_1, 0);
lean_inc(x_2493);
x_2494 = lean_st_ref_get(x_3, x_2080);
x_2495 = lean_ctor_get(x_2494, 0);
lean_inc(x_2495);
x_2496 = lean_ctor_get(x_2494, 1);
lean_inc(x_2496);
lean_dec_ref(x_2494);
x_2497 = lean_ctor_get(x_2495, 0);
lean_inc_ref(x_2497);
lean_dec(x_2495);
x_2498 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_2497, x_2493, x_2077);
lean_dec_ref(x_2497);
if (lean_obj_tag(x_2498) == 0)
{
lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; lean_object* x_2503; lean_object* x_2504; 
lean_dec_ref(x_2137);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_2499 = lean_ctor_get(x_2498, 0);
lean_inc(x_2499);
lean_dec_ref(x_2498);
lean_inc(x_2499);
x_2500 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_2499, x_3, x_2496);
lean_dec(x_3);
x_2501 = lean_ctor_get(x_2500, 1);
lean_inc(x_2501);
if (lean_is_exclusive(x_2500)) {
 lean_ctor_release(x_2500, 0);
 lean_ctor_release(x_2500, 1);
 x_2502 = x_2500;
} else {
 lean_dec_ref(x_2500);
 x_2502 = lean_box(0);
}
x_2503 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_1, x_2499);
if (lean_is_scalar(x_2502)) {
 x_2504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2504 = x_2502;
}
lean_ctor_set(x_2504, 0, x_2503);
lean_ctor_set(x_2504, 1, x_2501);
return x_2504;
}
else
{
lean_object* x_2505; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_2505 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_2137, x_8, x_2496);
lean_dec(x_8);
lean_dec_ref(x_2137);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_2505;
}
}
case 6:
{
lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; lean_object* x_2511; lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; 
lean_dec_ref(x_2137);
lean_dec_ref(x_2061);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_2506 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2506);
x_2507 = lean_st_ref_get(x_3, x_2080);
lean_dec(x_3);
x_2508 = lean_ctor_get(x_2507, 0);
lean_inc(x_2508);
x_2509 = lean_ctor_get(x_2507, 1);
lean_inc(x_2509);
if (lean_is_exclusive(x_2507)) {
 lean_ctor_release(x_2507, 0);
 lean_ctor_release(x_2507, 1);
 x_2510 = x_2507;
} else {
 lean_dec_ref(x_2507);
 x_2510 = lean_box(0);
}
x_2511 = lean_ctor_get(x_2508, 0);
lean_inc_ref(x_2511);
lean_dec(x_2508);
x_2512 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_2511, x_2077, x_2506);
lean_dec_ref(x_2511);
x_2513 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(x_1, x_2512);
if (lean_is_scalar(x_2510)) {
 x_2514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2514 = x_2510;
}
lean_ctor_set(x_2514, 0, x_2513);
lean_ctor_set(x_2514, 1, x_2509);
return x_2514;
}
default: 
{
lean_object* x_2515; lean_object* x_2516; 
lean_dec_ref(x_2061);
x_2515 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2515);
x_2516 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2516);
x_2081 = x_2515;
x_2082 = x_2516;
x_2083 = x_2;
x_2084 = x_3;
x_2085 = x_4;
x_2086 = x_5;
x_2087 = x_6;
x_2088 = x_2137;
x_2089 = x_8;
goto block_2134;
}
}
block_2134:
{
lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; uint8_t x_2097; 
x_2090 = lean_ctor_get(x_2081, 0);
lean_inc(x_2090);
x_2091 = lean_ctor_get(x_2081, 2);
lean_inc_ref(x_2091);
x_2092 = lean_ctor_get(x_2081, 3);
lean_inc_ref(x_2092);
x_2093 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_2090, x_2084, x_2080);
lean_dec(x_2090);
x_2094 = lean_ctor_get(x_2093, 0);
lean_inc(x_2094);
x_2095 = lean_ctor_get(x_2093, 1);
lean_inc(x_2095);
lean_dec_ref(x_2093);
lean_inc(x_2094);
lean_inc_ref(x_1);
lean_inc_ref(x_2082);
x_2096 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_2096, 0, x_2082);
lean_closure_set(x_2096, 1, x_1);
lean_closure_set(x_2096, 2, x_2094);
x_2097 = lean_unbox(x_2094);
if (x_2097 == 0)
{
uint8_t x_2098; 
lean_dec(x_2094);
lean_dec_ref(x_2082);
x_2098 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_2098 == 0)
{
lean_dec_ref(x_2092);
lean_dec_ref(x_2091);
x_10 = x_2096;
x_11 = x_2081;
x_12 = x_2083;
x_13 = x_2084;
x_14 = x_2085;
x_15 = x_2086;
x_16 = x_2087;
x_17 = x_2088;
x_18 = x_2089;
x_19 = x_2095;
goto block_29;
}
else
{
uint8_t x_2099; 
x_2099 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_2092, x_2091);
lean_dec_ref(x_2091);
if (x_2099 == 0)
{
x_10 = x_2096;
x_11 = x_2081;
x_12 = x_2083;
x_13 = x_2084;
x_14 = x_2085;
x_15 = x_2086;
x_16 = x_2087;
x_17 = x_2088;
x_18 = x_2089;
x_19 = x_2095;
goto block_29;
}
else
{
lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; 
x_2100 = lean_st_ref_get(x_2084, x_2095);
x_2101 = lean_ctor_get(x_2100, 0);
lean_inc(x_2101);
x_2102 = lean_ctor_get(x_2100, 1);
lean_inc(x_2102);
lean_dec_ref(x_2100);
x_2103 = lean_ctor_get(x_2101, 0);
lean_inc_ref(x_2103);
lean_dec(x_2101);
lean_inc(x_2089);
lean_inc_ref(x_2088);
lean_inc(x_2087);
lean_inc_ref(x_2086);
x_2104 = l_Lean_Compiler_LCNF_normFunDeclImp(x_2077, x_2081, x_2103, x_2086, x_2087, x_2088, x_2089, x_2102);
if (lean_obj_tag(x_2104) == 0)
{
lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; 
x_2105 = lean_ctor_get(x_2104, 0);
lean_inc(x_2105);
x_2106 = lean_ctor_get(x_2104, 1);
lean_inc(x_2106);
lean_dec_ref(x_2104);
lean_inc(x_2089);
lean_inc_ref(x_2088);
lean_inc(x_2087);
lean_inc_ref(x_2086);
x_2107 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_2105, x_2086, x_2087, x_2088, x_2089, x_2106);
if (lean_obj_tag(x_2107) == 0)
{
lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; 
x_2108 = lean_ctor_get(x_2107, 0);
lean_inc(x_2108);
x_2109 = lean_ctor_get(x_2107, 1);
lean_inc(x_2109);
lean_dec_ref(x_2107);
x_2110 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_2084, x_2109);
x_2111 = lean_ctor_get(x_2110, 1);
lean_inc(x_2111);
lean_dec_ref(x_2110);
x_10 = x_2096;
x_11 = x_2108;
x_12 = x_2083;
x_13 = x_2084;
x_14 = x_2085;
x_15 = x_2086;
x_16 = x_2087;
x_17 = x_2088;
x_18 = x_2089;
x_19 = x_2111;
goto block_29;
}
else
{
lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; 
lean_dec_ref(x_2096);
lean_dec(x_2089);
lean_dec_ref(x_2088);
lean_dec(x_2087);
lean_dec_ref(x_2086);
lean_dec_ref(x_2085);
lean_dec(x_2084);
lean_dec_ref(x_2083);
x_2112 = lean_ctor_get(x_2107, 0);
lean_inc(x_2112);
x_2113 = lean_ctor_get(x_2107, 1);
lean_inc(x_2113);
if (lean_is_exclusive(x_2107)) {
 lean_ctor_release(x_2107, 0);
 lean_ctor_release(x_2107, 1);
 x_2114 = x_2107;
} else {
 lean_dec_ref(x_2107);
 x_2114 = lean_box(0);
}
if (lean_is_scalar(x_2114)) {
 x_2115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2115 = x_2114;
}
lean_ctor_set(x_2115, 0, x_2112);
lean_ctor_set(x_2115, 1, x_2113);
return x_2115;
}
}
else
{
lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; 
lean_dec_ref(x_2096);
lean_dec(x_2089);
lean_dec_ref(x_2088);
lean_dec(x_2087);
lean_dec_ref(x_2086);
lean_dec_ref(x_2085);
lean_dec(x_2084);
lean_dec_ref(x_2083);
x_2116 = lean_ctor_get(x_2104, 0);
lean_inc(x_2116);
x_2117 = lean_ctor_get(x_2104, 1);
lean_inc(x_2117);
if (lean_is_exclusive(x_2104)) {
 lean_ctor_release(x_2104, 0);
 lean_ctor_release(x_2104, 1);
 x_2118 = x_2104;
} else {
 lean_dec_ref(x_2104);
 x_2118 = lean_box(0);
}
if (lean_is_scalar(x_2118)) {
 x_2119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2119 = x_2118;
}
lean_ctor_set(x_2119, 0, x_2116);
lean_ctor_set(x_2119, 1, x_2117);
return x_2119;
}
}
}
}
else
{
lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; 
lean_dec_ref(x_2096);
lean_dec_ref(x_2092);
lean_dec_ref(x_2091);
x_2120 = lean_st_ref_get(x_2084, x_2095);
x_2121 = lean_ctor_get(x_2120, 0);
lean_inc(x_2121);
x_2122 = lean_ctor_get(x_2120, 1);
lean_inc(x_2122);
lean_dec_ref(x_2120);
x_2123 = lean_ctor_get(x_2121, 0);
lean_inc_ref(x_2123);
lean_dec(x_2121);
lean_inc(x_2089);
lean_inc_ref(x_2088);
lean_inc(x_2087);
lean_inc_ref(x_2086);
x_2124 = l_Lean_Compiler_LCNF_normFunDeclImp(x_2077, x_2081, x_2123, x_2086, x_2087, x_2088, x_2089, x_2122);
if (lean_obj_tag(x_2124) == 0)
{
lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; uint8_t x_2128; lean_object* x_2129; 
x_2125 = lean_ctor_get(x_2124, 0);
lean_inc(x_2125);
x_2126 = lean_ctor_get(x_2124, 1);
lean_inc(x_2126);
lean_dec_ref(x_2124);
x_2127 = lean_box(0);
x_2128 = lean_unbox(x_2094);
lean_dec(x_2094);
x_2129 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_2082, x_1, x_2128, x_2125, x_2127, x_2083, x_2084, x_2085, x_2086, x_2087, x_2088, x_2089, x_2126);
lean_dec_ref(x_1);
return x_2129;
}
else
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; 
lean_dec(x_2094);
lean_dec(x_2089);
lean_dec_ref(x_2088);
lean_dec(x_2087);
lean_dec_ref(x_2086);
lean_dec_ref(x_2085);
lean_dec(x_2084);
lean_dec_ref(x_2083);
lean_dec_ref(x_2082);
lean_dec_ref(x_1);
x_2130 = lean_ctor_get(x_2124, 0);
lean_inc(x_2130);
x_2131 = lean_ctor_get(x_2124, 1);
lean_inc(x_2131);
if (lean_is_exclusive(x_2124)) {
 lean_ctor_release(x_2124, 0);
 lean_ctor_release(x_2124, 1);
 x_2132 = x_2124;
} else {
 lean_dec_ref(x_2124);
 x_2132 = lean_box(0);
}
if (lean_is_scalar(x_2132)) {
 x_2133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2133 = x_2132;
}
lean_ctor_set(x_2133, 0, x_2130);
lean_ctor_set(x_2133, 1, x_2131);
return x_2133;
}
}
}
}
else
{
lean_object* x_2517; 
lean_dec_ref(x_2076);
lean_dec(x_2074);
lean_dec(x_2072);
lean_dec(x_2071);
lean_dec(x_2070);
lean_dec(x_2069);
lean_dec(x_2068);
lean_dec(x_2067);
lean_dec(x_2066);
lean_dec(x_2065);
lean_dec(x_2064);
lean_dec_ref(x_2063);
lean_dec_ref(x_2062);
lean_dec_ref(x_2061);
lean_dec_ref(x_1);
x_2517 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2517;
}
}
}
else
{
lean_object* x_2518; lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; lean_object* x_2522; lean_object* x_2523; lean_object* x_2524; lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; lean_object* x_2529; lean_object* x_2530; lean_object* x_2531; lean_object* x_2532; lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; lean_object* x_2547; lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; lean_object* x_2554; lean_object* x_2555; lean_object* x_2556; lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; lean_object* x_2561; lean_object* x_2562; lean_object* x_2563; uint8_t x_2564; lean_object* x_2565; uint8_t x_2566; lean_object* x_2567; uint8_t x_2568; 
x_2518 = lean_ctor_get(x_48, 0);
lean_inc(x_2518);
lean_dec(x_48);
x_2519 = lean_ctor_get(x_2518, 0);
lean_inc_ref(x_2519);
x_2520 = lean_ctor_get(x_2518, 2);
lean_inc_ref(x_2520);
x_2521 = lean_ctor_get(x_2518, 3);
lean_inc_ref(x_2521);
x_2522 = lean_ctor_get(x_2518, 4);
lean_inc_ref(x_2522);
if (lean_is_exclusive(x_2518)) {
 lean_ctor_release(x_2518, 0);
 lean_ctor_release(x_2518, 1);
 lean_ctor_release(x_2518, 2);
 lean_ctor_release(x_2518, 3);
 lean_ctor_release(x_2518, 4);
 x_2523 = x_2518;
} else {
 lean_dec_ref(x_2518);
 x_2523 = lean_box(0);
}
x_2524 = l_Lean_Compiler_LCNF_Simp_simp___closed__4;
x_2525 = l_Lean_Compiler_LCNF_Simp_simp___closed__5;
lean_inc_ref(x_2519);
x_2526 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_2526, 0, x_2519);
x_2527 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_2527, 0, x_2519);
x_2528 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2528, 0, x_2526);
lean_ctor_set(x_2528, 1, x_2527);
x_2529 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_2529, 0, x_2522);
x_2530 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_2530, 0, x_2521);
x_2531 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_2531, 0, x_2520);
if (lean_is_scalar(x_2523)) {
 x_2532 = lean_alloc_ctor(0, 5, 0);
} else {
 x_2532 = x_2523;
}
lean_ctor_set(x_2532, 0, x_2528);
lean_ctor_set(x_2532, 1, x_2524);
lean_ctor_set(x_2532, 2, x_2531);
lean_ctor_set(x_2532, 3, x_2530);
lean_ctor_set(x_2532, 4, x_2529);
x_2533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2533, 0, x_2532);
lean_ctor_set(x_2533, 1, x_2525);
x_2534 = l_ReaderT_instMonad___redArg(x_2533);
x_2535 = l_ReaderT_instMonad___redArg(x_2534);
x_2536 = lean_ctor_get(x_2535, 0);
lean_inc_ref(x_2536);
if (lean_is_exclusive(x_2535)) {
 lean_ctor_release(x_2535, 0);
 lean_ctor_release(x_2535, 1);
 x_2537 = x_2535;
} else {
 lean_dec_ref(x_2535);
 x_2537 = lean_box(0);
}
x_2538 = lean_ctor_get(x_2536, 0);
lean_inc_ref(x_2538);
x_2539 = lean_ctor_get(x_2536, 2);
lean_inc_ref(x_2539);
x_2540 = lean_ctor_get(x_2536, 3);
lean_inc_ref(x_2540);
x_2541 = lean_ctor_get(x_2536, 4);
lean_inc_ref(x_2541);
if (lean_is_exclusive(x_2536)) {
 lean_ctor_release(x_2536, 0);
 lean_ctor_release(x_2536, 1);
 lean_ctor_release(x_2536, 2);
 lean_ctor_release(x_2536, 3);
 lean_ctor_release(x_2536, 4);
 x_2542 = x_2536;
} else {
 lean_dec_ref(x_2536);
 x_2542 = lean_box(0);
}
x_2543 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_2544 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_2538);
x_2545 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_2545, 0, x_2538);
x_2546 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_2546, 0, x_2538);
x_2547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2547, 0, x_2545);
lean_ctor_set(x_2547, 1, x_2546);
x_2548 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_2548, 0, x_2541);
x_2549 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_2549, 0, x_2540);
x_2550 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_2550, 0, x_2539);
if (lean_is_scalar(x_2542)) {
 x_2551 = lean_alloc_ctor(0, 5, 0);
} else {
 x_2551 = x_2542;
}
lean_ctor_set(x_2551, 0, x_2547);
lean_ctor_set(x_2551, 1, x_2543);
lean_ctor_set(x_2551, 2, x_2550);
lean_ctor_set(x_2551, 3, x_2549);
lean_ctor_set(x_2551, 4, x_2548);
if (lean_is_scalar(x_2537)) {
 x_2552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2552 = x_2537;
}
lean_ctor_set(x_2552, 0, x_2551);
lean_ctor_set(x_2552, 1, x_2544);
x_2553 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_2553);
x_2554 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_2554);
x_2555 = lean_ctor_get(x_7, 2);
lean_inc(x_2555);
x_2556 = lean_ctor_get(x_7, 3);
lean_inc(x_2556);
x_2557 = lean_ctor_get(x_7, 4);
lean_inc(x_2557);
x_2558 = lean_ctor_get(x_7, 5);
lean_inc(x_2558);
x_2559 = lean_ctor_get(x_7, 6);
lean_inc(x_2559);
x_2560 = lean_ctor_get(x_7, 7);
lean_inc(x_2560);
x_2561 = lean_ctor_get(x_7, 8);
lean_inc(x_2561);
x_2562 = lean_ctor_get(x_7, 9);
lean_inc(x_2562);
x_2563 = lean_ctor_get(x_7, 10);
lean_inc(x_2563);
x_2564 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_2565 = lean_ctor_get(x_7, 11);
lean_inc(x_2565);
x_2566 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_2567 = lean_ctor_get(x_7, 12);
lean_inc_ref(x_2567);
x_2568 = lean_nat_dec_eq(x_2556, x_2557);
if (x_2568 == 0)
{
lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; lean_object* x_2578; lean_object* x_2579; lean_object* x_2580; lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; 
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 lean_ctor_release(x_7, 9);
 lean_ctor_release(x_7, 10);
 lean_ctor_release(x_7, 11);
 lean_ctor_release(x_7, 12);
 x_2569 = x_7;
} else {
 lean_dec_ref(x_7);
 x_2569 = lean_box(0);
}
x_2570 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
x_2571 = lean_ctor_get(x_2570, 1);
lean_inc(x_2571);
lean_dec_ref(x_2570);
x_2626 = lean_unsigned_to_nat(1u);
x_2627 = lean_nat_add(x_2556, x_2626);
lean_dec(x_2556);
if (lean_is_scalar(x_2569)) {
 x_2628 = lean_alloc_ctor(0, 13, 2);
} else {
 x_2628 = x_2569;
}
lean_ctor_set(x_2628, 0, x_2553);
lean_ctor_set(x_2628, 1, x_2554);
lean_ctor_set(x_2628, 2, x_2555);
lean_ctor_set(x_2628, 3, x_2627);
lean_ctor_set(x_2628, 4, x_2557);
lean_ctor_set(x_2628, 5, x_2558);
lean_ctor_set(x_2628, 6, x_2559);
lean_ctor_set(x_2628, 7, x_2560);
lean_ctor_set(x_2628, 8, x_2561);
lean_ctor_set(x_2628, 9, x_2562);
lean_ctor_set(x_2628, 10, x_2563);
lean_ctor_set(x_2628, 11, x_2565);
lean_ctor_set(x_2628, 12, x_2567);
lean_ctor_set_uint8(x_2628, sizeof(void*)*13, x_2564);
lean_ctor_set_uint8(x_2628, sizeof(void*)*13 + 1, x_2566);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; lean_object* x_2633; lean_object* x_2634; lean_object* x_2635; lean_object* x_2636; lean_object* x_2637; lean_object* x_2638; uint8_t x_2639; lean_object* x_2640; lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; lean_object* x_2655; lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; uint8_t x_2664; lean_object* x_2810; lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; lean_object* x_2815; lean_object* x_2816; lean_object* x_2817; lean_object* x_2818; lean_object* x_2819; lean_object* x_2820; lean_object* x_2825; lean_object* x_2826; lean_object* x_2827; lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; uint8_t x_2858; 
lean_dec_ref(x_2552);
x_2629 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2629);
x_2630 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2630);
lean_inc_ref(x_2629);
x_2825 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_2568, x_2629, x_3, x_5, x_6, x_2628, x_8, x_2571);
x_2826 = lean_ctor_get(x_2825, 0);
lean_inc(x_2826);
x_2827 = lean_ctor_get(x_2825, 1);
lean_inc(x_2827);
lean_dec_ref(x_2825);
x_2858 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2069_(x_2629, x_2826);
lean_dec_ref(x_2629);
if (x_2858 == 0)
{
goto block_2857;
}
else
{
if (x_2568 == 0)
{
x_2828 = x_2;
x_2829 = x_3;
x_2830 = x_4;
x_2831 = x_5;
x_2832 = x_6;
x_2833 = x_2628;
x_2834 = x_8;
x_2835 = x_2827;
goto block_2854;
}
else
{
goto block_2857;
}
}
block_2654:
{
lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; lean_object* x_2652; 
x_2648 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_2648, 0, x_2647);
lean_ctor_set(x_2648, 1, x_2636);
lean_ctor_set(x_2648, 2, x_2637);
lean_ctor_set(x_2648, 3, x_2638);
lean_ctor_set(x_2648, 4, x_2640);
lean_ctor_set(x_2648, 5, x_2641);
lean_ctor_set(x_2648, 6, x_2642);
lean_ctor_set_uint8(x_2648, sizeof(void*)*7, x_2639);
x_2649 = lean_st_ref_set(x_2634, x_2648, x_2645);
x_2650 = lean_ctor_get(x_2649, 1);
lean_inc(x_2650);
lean_dec_ref(x_2649);
x_2651 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_2635, x_2634, x_2631, x_2650);
lean_dec_ref(x_2635);
x_2652 = lean_ctor_get(x_2651, 1);
lean_inc(x_2652);
lean_dec_ref(x_2651);
x_1 = x_2630;
x_2 = x_2644;
x_3 = x_2634;
x_4 = x_2646;
x_5 = x_2643;
x_6 = x_2631;
x_7 = x_2633;
x_8 = x_2632;
x_9 = x_2652;
goto _start;
}
block_2809:
{
if (x_2664 == 0)
{
lean_object* x_2665; 
lean_inc(x_2657);
lean_inc_ref(x_2659);
lean_inc(x_2655);
lean_inc_ref(x_2662);
lean_inc_ref(x_2660);
x_2665 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_2660, x_2662, x_2655, x_2659, x_2657, x_2656);
if (lean_obj_tag(x_2665) == 0)
{
lean_object* x_2666; 
x_2666 = lean_ctor_get(x_2665, 0);
lean_inc(x_2666);
if (lean_obj_tag(x_2666) == 0)
{
lean_object* x_2667; lean_object* x_2668; 
x_2667 = lean_ctor_get(x_2665, 1);
lean_inc(x_2667);
lean_dec_ref(x_2665);
lean_inc(x_2657);
lean_inc_ref(x_2659);
lean_inc(x_2655);
lean_inc_ref(x_2662);
lean_inc_ref(x_2660);
x_2668 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_2660, x_2661, x_2658, x_2662, x_2655, x_2659, x_2657, x_2667);
if (lean_obj_tag(x_2668) == 0)
{
lean_object* x_2669; 
x_2669 = lean_ctor_get(x_2668, 0);
lean_inc(x_2669);
if (lean_obj_tag(x_2669) == 0)
{
lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; lean_object* x_2673; lean_object* x_2674; 
x_2670 = lean_ctor_get(x_2668, 1);
lean_inc(x_2670);
lean_dec_ref(x_2668);
x_2671 = lean_ctor_get(x_2660, 0);
lean_inc(x_2671);
x_2672 = lean_ctor_get(x_2660, 3);
lean_inc(x_2672);
lean_inc(x_2672);
x_2673 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_2672, x_2670);
x_2674 = lean_ctor_get(x_2673, 0);
lean_inc(x_2674);
if (lean_obj_tag(x_2674) == 0)
{
lean_object* x_2675; lean_object* x_2676; 
x_2675 = lean_ctor_get(x_2673, 1);
lean_inc(x_2675);
lean_dec_ref(x_2673);
lean_inc(x_2657);
lean_inc_ref(x_2659);
lean_inc(x_2655);
lean_inc_ref(x_2662);
lean_inc_ref(x_2663);
lean_inc(x_2658);
lean_inc_ref(x_2661);
lean_inc_ref(x_2630);
lean_inc_ref(x_2660);
x_2676 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_2660, x_2630, x_2661, x_2658, x_2663, x_2662, x_2655, x_2659, x_2657, x_2675);
if (lean_obj_tag(x_2676) == 0)
{
lean_object* x_2677; 
x_2677 = lean_ctor_get(x_2676, 0);
lean_inc(x_2677);
if (lean_obj_tag(x_2677) == 0)
{
lean_object* x_2678; lean_object* x_2679; 
x_2678 = lean_ctor_get(x_2676, 1);
lean_inc(x_2678);
lean_dec_ref(x_2676);
lean_inc(x_2657);
lean_inc_ref(x_2659);
lean_inc(x_2655);
lean_inc_ref(x_2662);
lean_inc_ref(x_2663);
lean_inc(x_2658);
lean_inc_ref(x_2661);
x_2679 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_2672, x_2661, x_2658, x_2663, x_2662, x_2655, x_2659, x_2657, x_2678);
if (lean_obj_tag(x_2679) == 0)
{
lean_object* x_2680; 
x_2680 = lean_ctor_get(x_2679, 0);
lean_inc(x_2680);
if (lean_obj_tag(x_2680) == 0)
{
lean_object* x_2681; lean_object* x_2682; 
x_2681 = lean_ctor_get(x_2679, 1);
lean_inc(x_2681);
lean_dec_ref(x_2679);
lean_inc(x_2657);
lean_inc_ref(x_2659);
lean_inc(x_2655);
lean_inc_ref(x_2662);
lean_inc_ref(x_2663);
lean_inc(x_2658);
lean_inc_ref(x_2661);
x_2682 = l_Lean_Compiler_LCNF_Simp_simp(x_2630, x_2661, x_2658, x_2663, x_2662, x_2655, x_2659, x_2657, x_2681);
if (lean_obj_tag(x_2682) == 0)
{
lean_object* x_2683; lean_object* x_2684; lean_object* x_2685; lean_object* x_2686; uint8_t x_2687; 
x_2683 = lean_ctor_get(x_2682, 0);
lean_inc(x_2683);
x_2684 = lean_ctor_get(x_2682, 1);
lean_inc(x_2684);
lean_dec_ref(x_2682);
x_2685 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_2671, x_2658, x_2684);
lean_dec(x_2671);
x_2686 = lean_ctor_get(x_2685, 0);
lean_inc(x_2686);
x_2687 = lean_unbox(x_2686);
lean_dec(x_2686);
if (x_2687 == 0)
{
lean_object* x_2688; lean_object* x_2689; lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; 
lean_dec_ref(x_2663);
lean_dec_ref(x_2662);
lean_dec_ref(x_2661);
lean_dec_ref(x_2659);
lean_dec(x_2657);
lean_dec_ref(x_1);
x_2688 = lean_ctor_get(x_2685, 1);
lean_inc(x_2688);
lean_dec_ref(x_2685);
x_2689 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_2660, x_2658, x_2655, x_2688);
lean_dec(x_2655);
lean_dec(x_2658);
lean_dec_ref(x_2660);
x_2690 = lean_ctor_get(x_2689, 1);
lean_inc(x_2690);
if (lean_is_exclusive(x_2689)) {
 lean_ctor_release(x_2689, 0);
 lean_ctor_release(x_2689, 1);
 x_2691 = x_2689;
} else {
 lean_dec_ref(x_2689);
 x_2691 = lean_box(0);
}
if (lean_is_scalar(x_2691)) {
 x_2692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2692 = x_2691;
}
lean_ctor_set(x_2692, 0, x_2683);
lean_ctor_set(x_2692, 1, x_2690);
return x_2692;
}
else
{
lean_object* x_2693; lean_object* x_2694; lean_object* x_2695; lean_object* x_2696; lean_object* x_2697; lean_object* x_2698; 
x_2693 = lean_ctor_get(x_2685, 1);
lean_inc(x_2693);
lean_dec_ref(x_2685);
lean_inc_ref(x_2660);
x_2694 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_2660, x_2661, x_2658, x_2663, x_2662, x_2655, x_2659, x_2657, x_2693);
lean_dec(x_2657);
lean_dec_ref(x_2659);
lean_dec(x_2655);
lean_dec_ref(x_2662);
lean_dec_ref(x_2663);
lean_dec(x_2658);
lean_dec_ref(x_2661);
x_2695 = lean_ctor_get(x_2694, 1);
lean_inc(x_2695);
if (lean_is_exclusive(x_2694)) {
 lean_ctor_release(x_2694, 0);
 lean_ctor_release(x_2694, 1);
 x_2696 = x_2694;
} else {
 lean_dec_ref(x_2694);
 x_2696 = lean_box(0);
}
x_2697 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_2660, x_2683);
lean_dec_ref(x_1);
if (lean_is_scalar(x_2696)) {
 x_2698 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2698 = x_2696;
}
lean_ctor_set(x_2698, 0, x_2697);
lean_ctor_set(x_2698, 1, x_2695);
return x_2698;
}
}
else
{
lean_dec(x_2671);
lean_dec_ref(x_2663);
lean_dec_ref(x_2662);
lean_dec_ref(x_2661);
lean_dec_ref(x_2660);
lean_dec_ref(x_2659);
lean_dec(x_2658);
lean_dec(x_2657);
lean_dec(x_2655);
lean_dec_ref(x_1);
return x_2682;
}
}
else
{
lean_object* x_2699; lean_object* x_2700; lean_object* x_2701; lean_object* x_2702; lean_object* x_2703; 
lean_dec_ref(x_1);
x_2699 = lean_ctor_get(x_2680, 0);
lean_inc(x_2699);
lean_dec_ref(x_2680);
x_2700 = lean_ctor_get(x_2679, 1);
lean_inc(x_2700);
lean_dec_ref(x_2679);
x_2701 = lean_ctor_get(x_2699, 0);
lean_inc(x_2701);
x_2702 = lean_ctor_get(x_2699, 1);
lean_inc(x_2702);
lean_dec(x_2699);
x_2703 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_2671, x_2702, x_2658, x_2655, x_2659, x_2657, x_2700);
if (lean_obj_tag(x_2703) == 0)
{
lean_object* x_2704; lean_object* x_2705; lean_object* x_2706; lean_object* x_2707; 
x_2704 = lean_ctor_get(x_2703, 1);
lean_inc(x_2704);
lean_dec_ref(x_2703);
x_2705 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_2660, x_2658, x_2655, x_2704);
lean_dec_ref(x_2660);
x_2706 = lean_ctor_get(x_2705, 1);
lean_inc(x_2706);
lean_dec_ref(x_2705);
lean_inc(x_2657);
lean_inc_ref(x_2659);
lean_inc(x_2655);
lean_inc_ref(x_2662);
lean_inc_ref(x_2663);
lean_inc(x_2658);
lean_inc_ref(x_2661);
x_2707 = l_Lean_Compiler_LCNF_Simp_simp(x_2630, x_2661, x_2658, x_2663, x_2662, x_2655, x_2659, x_2657, x_2706);
if (lean_obj_tag(x_2707) == 0)
{
lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; 
x_2708 = lean_ctor_get(x_2707, 0);
lean_inc(x_2708);
x_2709 = lean_ctor_get(x_2707, 1);
lean_inc(x_2709);
lean_dec_ref(x_2707);
x_2710 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_2701, x_2708, x_2661, x_2658, x_2663, x_2662, x_2655, x_2659, x_2657, x_2709);
lean_dec(x_2657);
lean_dec_ref(x_2659);
lean_dec(x_2655);
lean_dec_ref(x_2662);
lean_dec_ref(x_2663);
lean_dec(x_2658);
lean_dec_ref(x_2661);
lean_dec(x_2701);
return x_2710;
}
else
{
lean_dec(x_2701);
lean_dec_ref(x_2663);
lean_dec_ref(x_2662);
lean_dec_ref(x_2661);
lean_dec_ref(x_2659);
lean_dec(x_2658);
lean_dec(x_2657);
lean_dec(x_2655);
return x_2707;
}
}
else
{
lean_object* x_2711; lean_object* x_2712; lean_object* x_2713; lean_object* x_2714; 
lean_dec(x_2701);
lean_dec_ref(x_2663);
lean_dec_ref(x_2662);
lean_dec_ref(x_2661);
lean_dec_ref(x_2660);
lean_dec_ref(x_2659);
lean_dec(x_2658);
lean_dec(x_2657);
lean_dec(x_2655);
lean_dec_ref(x_2630);
x_2711 = lean_ctor_get(x_2703, 0);
lean_inc(x_2711);
x_2712 = lean_ctor_get(x_2703, 1);
lean_inc(x_2712);
if (lean_is_exclusive(x_2703)) {
 lean_ctor_release(x_2703, 0);
 lean_ctor_release(x_2703, 1);
 x_2713 = x_2703;
} else {
 lean_dec_ref(x_2703);
 x_2713 = lean_box(0);
}
if (lean_is_scalar(x_2713)) {
 x_2714 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2714 = x_2713;
}
lean_ctor_set(x_2714, 0, x_2711);
lean_ctor_set(x_2714, 1, x_2712);
return x_2714;
}
}
}
else
{
lean_object* x_2715; lean_object* x_2716; lean_object* x_2717; lean_object* x_2718; 
lean_dec(x_2671);
lean_dec_ref(x_2663);
lean_dec_ref(x_2662);
lean_dec_ref(x_2661);
lean_dec_ref(x_2660);
lean_dec_ref(x_2659);
lean_dec(x_2658);
lean_dec(x_2657);
lean_dec(x_2655);
lean_dec_ref(x_2630);
lean_dec_ref(x_1);
x_2715 = lean_ctor_get(x_2679, 0);
lean_inc(x_2715);
x_2716 = lean_ctor_get(x_2679, 1);
lean_inc(x_2716);
if (lean_is_exclusive(x_2679)) {
 lean_ctor_release(x_2679, 0);
 lean_ctor_release(x_2679, 1);
 x_2717 = x_2679;
} else {
 lean_dec_ref(x_2679);
 x_2717 = lean_box(0);
}
if (lean_is_scalar(x_2717)) {
 x_2718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2718 = x_2717;
}
lean_ctor_set(x_2718, 0, x_2715);
lean_ctor_set(x_2718, 1, x_2716);
return x_2718;
}
}
else
{
lean_object* x_2719; lean_object* x_2720; lean_object* x_2721; lean_object* x_2722; lean_object* x_2723; lean_object* x_2724; 
lean_dec(x_2672);
lean_dec(x_2671);
lean_dec_ref(x_2663);
lean_dec_ref(x_2662);
lean_dec_ref(x_2661);
lean_dec_ref(x_2659);
lean_dec(x_2657);
lean_dec_ref(x_2630);
lean_dec_ref(x_1);
x_2719 = lean_ctor_get(x_2676, 1);
lean_inc(x_2719);
lean_dec_ref(x_2676);
x_2720 = lean_ctor_get(x_2677, 0);
lean_inc(x_2720);
lean_dec_ref(x_2677);
x_2721 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_2660, x_2658, x_2655, x_2719);
lean_dec(x_2655);
lean_dec(x_2658);
lean_dec_ref(x_2660);
x_2722 = lean_ctor_get(x_2721, 1);
lean_inc(x_2722);
if (lean_is_exclusive(x_2721)) {
 lean_ctor_release(x_2721, 0);
 lean_ctor_release(x_2721, 1);
 x_2723 = x_2721;
} else {
 lean_dec_ref(x_2721);
 x_2723 = lean_box(0);
}
if (lean_is_scalar(x_2723)) {
 x_2724 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2724 = x_2723;
}
lean_ctor_set(x_2724, 0, x_2720);
lean_ctor_set(x_2724, 1, x_2722);
return x_2724;
}
}
else
{
lean_object* x_2725; lean_object* x_2726; lean_object* x_2727; lean_object* x_2728; 
lean_dec(x_2672);
lean_dec(x_2671);
lean_dec_ref(x_2663);
lean_dec_ref(x_2662);
lean_dec_ref(x_2661);
lean_dec_ref(x_2660);
lean_dec_ref(x_2659);
lean_dec(x_2658);
lean_dec(x_2657);
lean_dec(x_2655);
lean_dec_ref(x_2630);
lean_dec_ref(x_1);
x_2725 = lean_ctor_get(x_2676, 0);
lean_inc(x_2725);
x_2726 = lean_ctor_get(x_2676, 1);
lean_inc(x_2726);
if (lean_is_exclusive(x_2676)) {
 lean_ctor_release(x_2676, 0);
 lean_ctor_release(x_2676, 1);
 x_2727 = x_2676;
} else {
 lean_dec_ref(x_2676);
 x_2727 = lean_box(0);
}
if (lean_is_scalar(x_2727)) {
 x_2728 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2728 = x_2727;
}
lean_ctor_set(x_2728, 0, x_2725);
lean_ctor_set(x_2728, 1, x_2726);
return x_2728;
}
}
else
{
lean_object* x_2729; lean_object* x_2730; lean_object* x_2731; 
lean_dec(x_2672);
lean_dec_ref(x_1);
x_2729 = lean_ctor_get(x_2673, 1);
lean_inc(x_2729);
lean_dec_ref(x_2673);
x_2730 = lean_ctor_get(x_2674, 0);
lean_inc(x_2730);
lean_dec_ref(x_2674);
x_2731 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_2671, x_2730, x_2658, x_2655, x_2659, x_2657, x_2729);
if (lean_obj_tag(x_2731) == 0)
{
lean_object* x_2732; lean_object* x_2733; lean_object* x_2734; 
x_2732 = lean_ctor_get(x_2731, 1);
lean_inc(x_2732);
lean_dec_ref(x_2731);
x_2733 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_2660, x_2658, x_2655, x_2732);
lean_dec_ref(x_2660);
x_2734 = lean_ctor_get(x_2733, 1);
lean_inc(x_2734);
lean_dec_ref(x_2733);
x_1 = x_2630;
x_2 = x_2661;
x_3 = x_2658;
x_4 = x_2663;
x_5 = x_2662;
x_6 = x_2655;
x_7 = x_2659;
x_8 = x_2657;
x_9 = x_2734;
goto _start;
}
else
{
lean_object* x_2736; lean_object* x_2737; lean_object* x_2738; lean_object* x_2739; 
lean_dec_ref(x_2663);
lean_dec_ref(x_2662);
lean_dec_ref(x_2661);
lean_dec_ref(x_2660);
lean_dec_ref(x_2659);
lean_dec(x_2658);
lean_dec(x_2657);
lean_dec(x_2655);
lean_dec_ref(x_2630);
x_2736 = lean_ctor_get(x_2731, 0);
lean_inc(x_2736);
x_2737 = lean_ctor_get(x_2731, 1);
lean_inc(x_2737);
if (lean_is_exclusive(x_2731)) {
 lean_ctor_release(x_2731, 0);
 lean_ctor_release(x_2731, 1);
 x_2738 = x_2731;
} else {
 lean_dec_ref(x_2731);
 x_2738 = lean_box(0);
}
if (lean_is_scalar(x_2738)) {
 x_2739 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2739 = x_2738;
}
lean_ctor_set(x_2739, 0, x_2736);
lean_ctor_set(x_2739, 1, x_2737);
return x_2739;
}
}
}
else
{
lean_object* x_2740; lean_object* x_2741; lean_object* x_2742; lean_object* x_2743; 
lean_dec_ref(x_2660);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_2740 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2740 = lean_box(0);
}
x_2741 = lean_ctor_get(x_2668, 1);
lean_inc(x_2741);
lean_dec_ref(x_2668);
x_2742 = lean_ctor_get(x_2669, 0);
lean_inc(x_2742);
lean_dec_ref(x_2669);
if (lean_is_scalar(x_2740)) {
 x_2743 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2743 = x_2740;
 lean_ctor_set_tag(x_2743, 1);
}
lean_ctor_set(x_2743, 0, x_2742);
lean_ctor_set(x_2743, 1, x_2630);
x_1 = x_2743;
x_2 = x_2661;
x_3 = x_2658;
x_4 = x_2663;
x_5 = x_2662;
x_6 = x_2655;
x_7 = x_2659;
x_8 = x_2657;
x_9 = x_2741;
goto _start;
}
}
else
{
lean_object* x_2745; lean_object* x_2746; lean_object* x_2747; lean_object* x_2748; 
lean_dec_ref(x_2663);
lean_dec_ref(x_2662);
lean_dec_ref(x_2661);
lean_dec_ref(x_2660);
lean_dec_ref(x_2659);
lean_dec(x_2658);
lean_dec(x_2657);
lean_dec(x_2655);
lean_dec_ref(x_2630);
lean_dec_ref(x_1);
x_2745 = lean_ctor_get(x_2668, 0);
lean_inc(x_2745);
x_2746 = lean_ctor_get(x_2668, 1);
lean_inc(x_2746);
if (lean_is_exclusive(x_2668)) {
 lean_ctor_release(x_2668, 0);
 lean_ctor_release(x_2668, 1);
 x_2747 = x_2668;
} else {
 lean_dec_ref(x_2668);
 x_2747 = lean_box(0);
}
if (lean_is_scalar(x_2747)) {
 x_2748 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2748 = x_2747;
}
lean_ctor_set(x_2748, 0, x_2745);
lean_ctor_set(x_2748, 1, x_2746);
return x_2748;
}
}
else
{
lean_object* x_2749; lean_object* x_2750; lean_object* x_2751; lean_object* x_2752; lean_object* x_2753; 
lean_dec_ref(x_2660);
lean_dec_ref(x_1);
x_2749 = lean_ctor_get(x_2665, 1);
lean_inc(x_2749);
lean_dec_ref(x_2665);
x_2750 = lean_ctor_get(x_2666, 0);
lean_inc(x_2750);
lean_dec_ref(x_2666);
x_2751 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_2658, x_2749);
x_2752 = lean_ctor_get(x_2751, 1);
lean_inc(x_2752);
lean_dec_ref(x_2751);
lean_inc(x_2657);
lean_inc_ref(x_2659);
lean_inc(x_2655);
lean_inc_ref(x_2662);
lean_inc_ref(x_2663);
lean_inc(x_2658);
lean_inc_ref(x_2661);
x_2753 = l_Lean_Compiler_LCNF_Simp_simp(x_2630, x_2661, x_2658, x_2663, x_2662, x_2655, x_2659, x_2657, x_2752);
if (lean_obj_tag(x_2753) == 0)
{
lean_object* x_2754; lean_object* x_2755; lean_object* x_2756; 
x_2754 = lean_ctor_get(x_2753, 0);
lean_inc(x_2754);
x_2755 = lean_ctor_get(x_2753, 1);
lean_inc(x_2755);
lean_dec_ref(x_2753);
x_2756 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_2750, x_2754, x_2661, x_2658, x_2663, x_2662, x_2655, x_2659, x_2657, x_2755);
lean_dec(x_2657);
lean_dec_ref(x_2659);
lean_dec(x_2655);
lean_dec_ref(x_2662);
lean_dec_ref(x_2663);
lean_dec(x_2658);
lean_dec_ref(x_2661);
lean_dec(x_2750);
return x_2756;
}
else
{
lean_dec(x_2750);
lean_dec_ref(x_2663);
lean_dec_ref(x_2662);
lean_dec_ref(x_2661);
lean_dec_ref(x_2659);
lean_dec(x_2658);
lean_dec(x_2657);
lean_dec(x_2655);
return x_2753;
}
}
}
else
{
lean_object* x_2757; lean_object* x_2758; lean_object* x_2759; lean_object* x_2760; 
lean_dec_ref(x_2663);
lean_dec_ref(x_2662);
lean_dec_ref(x_2661);
lean_dec_ref(x_2660);
lean_dec_ref(x_2659);
lean_dec(x_2658);
lean_dec(x_2657);
lean_dec(x_2655);
lean_dec_ref(x_2630);
lean_dec_ref(x_1);
x_2757 = lean_ctor_get(x_2665, 0);
lean_inc(x_2757);
x_2758 = lean_ctor_get(x_2665, 1);
lean_inc(x_2758);
if (lean_is_exclusive(x_2665)) {
 lean_ctor_release(x_2665, 0);
 lean_ctor_release(x_2665, 1);
 x_2759 = x_2665;
} else {
 lean_dec_ref(x_2665);
 x_2759 = lean_box(0);
}
if (lean_is_scalar(x_2759)) {
 x_2760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2760 = x_2759;
}
lean_ctor_set(x_2760, 0, x_2757);
lean_ctor_set(x_2760, 1, x_2758);
return x_2760;
}
}
else
{
lean_object* x_2761; lean_object* x_2762; lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; uint8_t x_2768; lean_object* x_2769; lean_object* x_2770; lean_object* x_2771; lean_object* x_2772; lean_object* x_2773; lean_object* x_2774; lean_object* x_2775; lean_object* x_2776; lean_object* x_2777; uint64_t x_2778; uint64_t x_2779; uint64_t x_2780; uint64_t x_2781; uint64_t x_2782; uint64_t x_2783; uint64_t x_2784; size_t x_2785; size_t x_2786; size_t x_2787; size_t x_2788; size_t x_2789; lean_object* x_2790; uint8_t x_2791; 
lean_dec_ref(x_1);
x_2761 = lean_st_ref_take(x_2658, x_2656);
x_2762 = lean_ctor_get(x_2761, 0);
lean_inc(x_2762);
x_2763 = lean_ctor_get(x_2762, 0);
lean_inc_ref(x_2763);
x_2764 = lean_ctor_get(x_2761, 1);
lean_inc(x_2764);
lean_dec_ref(x_2761);
x_2765 = lean_ctor_get(x_2762, 1);
lean_inc_ref(x_2765);
x_2766 = lean_ctor_get(x_2762, 2);
lean_inc(x_2766);
x_2767 = lean_ctor_get(x_2762, 3);
lean_inc_ref(x_2767);
x_2768 = lean_ctor_get_uint8(x_2762, sizeof(void*)*7);
x_2769 = lean_ctor_get(x_2762, 4);
lean_inc(x_2769);
x_2770 = lean_ctor_get(x_2762, 5);
lean_inc(x_2770);
x_2771 = lean_ctor_get(x_2762, 6);
lean_inc(x_2771);
lean_dec(x_2762);
x_2772 = lean_ctor_get(x_2763, 0);
lean_inc(x_2772);
x_2773 = lean_ctor_get(x_2763, 1);
lean_inc_ref(x_2773);
if (lean_is_exclusive(x_2763)) {
 lean_ctor_release(x_2763, 0);
 lean_ctor_release(x_2763, 1);
 x_2774 = x_2763;
} else {
 lean_dec_ref(x_2763);
 x_2774 = lean_box(0);
}
x_2775 = lean_ctor_get(x_2660, 0);
lean_inc(x_2775);
x_2776 = lean_box(0);
x_2777 = lean_array_get_size(x_2773);
x_2778 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_2775);
x_2779 = 32;
x_2780 = lean_uint64_shift_right(x_2778, x_2779);
x_2781 = lean_uint64_xor(x_2778, x_2780);
x_2782 = 16;
x_2783 = lean_uint64_shift_right(x_2781, x_2782);
x_2784 = lean_uint64_xor(x_2781, x_2783);
x_2785 = lean_uint64_to_usize(x_2784);
x_2786 = lean_usize_of_nat(x_2777);
lean_dec(x_2777);
x_2787 = 1;
x_2788 = lean_usize_sub(x_2786, x_2787);
x_2789 = lean_usize_land(x_2785, x_2788);
x_2790 = lean_array_uget(x_2773, x_2789);
x_2791 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_2775, x_2790);
if (x_2791 == 0)
{
lean_object* x_2792; lean_object* x_2793; lean_object* x_2794; lean_object* x_2795; lean_object* x_2796; lean_object* x_2797; lean_object* x_2798; lean_object* x_2799; uint8_t x_2800; 
x_2792 = lean_nat_add(x_2772, x_2626);
lean_dec(x_2772);
x_2793 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2793, 0, x_2775);
lean_ctor_set(x_2793, 1, x_2776);
lean_ctor_set(x_2793, 2, x_2790);
x_2794 = lean_array_uset(x_2773, x_2789, x_2793);
x_2795 = lean_unsigned_to_nat(4u);
x_2796 = lean_nat_mul(x_2792, x_2795);
x_2797 = lean_unsigned_to_nat(3u);
x_2798 = lean_nat_div(x_2796, x_2797);
lean_dec(x_2796);
x_2799 = lean_array_get_size(x_2794);
x_2800 = lean_nat_dec_le(x_2798, x_2799);
lean_dec(x_2799);
lean_dec(x_2798);
if (x_2800 == 0)
{
lean_object* x_2801; lean_object* x_2802; 
x_2801 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_2794);
if (lean_is_scalar(x_2774)) {
 x_2802 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2802 = x_2774;
}
lean_ctor_set(x_2802, 0, x_2792);
lean_ctor_set(x_2802, 1, x_2801);
x_2631 = x_2655;
x_2632 = x_2657;
x_2633 = x_2659;
x_2634 = x_2658;
x_2635 = x_2660;
x_2636 = x_2765;
x_2637 = x_2766;
x_2638 = x_2767;
x_2639 = x_2768;
x_2640 = x_2769;
x_2641 = x_2770;
x_2642 = x_2771;
x_2643 = x_2662;
x_2644 = x_2661;
x_2645 = x_2764;
x_2646 = x_2663;
x_2647 = x_2802;
goto block_2654;
}
else
{
lean_object* x_2803; 
if (lean_is_scalar(x_2774)) {
 x_2803 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2803 = x_2774;
}
lean_ctor_set(x_2803, 0, x_2792);
lean_ctor_set(x_2803, 1, x_2794);
x_2631 = x_2655;
x_2632 = x_2657;
x_2633 = x_2659;
x_2634 = x_2658;
x_2635 = x_2660;
x_2636 = x_2765;
x_2637 = x_2766;
x_2638 = x_2767;
x_2639 = x_2768;
x_2640 = x_2769;
x_2641 = x_2770;
x_2642 = x_2771;
x_2643 = x_2662;
x_2644 = x_2661;
x_2645 = x_2764;
x_2646 = x_2663;
x_2647 = x_2803;
goto block_2654;
}
}
else
{
lean_object* x_2804; lean_object* x_2805; lean_object* x_2806; lean_object* x_2807; lean_object* x_2808; 
x_2804 = lean_box(0);
x_2805 = lean_array_uset(x_2773, x_2789, x_2804);
x_2806 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_2775, x_2776, x_2790);
x_2807 = lean_array_uset(x_2805, x_2789, x_2806);
if (lean_is_scalar(x_2774)) {
 x_2808 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2808 = x_2774;
}
lean_ctor_set(x_2808, 0, x_2772);
lean_ctor_set(x_2808, 1, x_2807);
x_2631 = x_2655;
x_2632 = x_2657;
x_2633 = x_2659;
x_2634 = x_2658;
x_2635 = x_2660;
x_2636 = x_2765;
x_2637 = x_2766;
x_2638 = x_2767;
x_2639 = x_2768;
x_2640 = x_2769;
x_2641 = x_2770;
x_2642 = x_2771;
x_2643 = x_2662;
x_2644 = x_2661;
x_2645 = x_2764;
x_2646 = x_2663;
x_2647 = x_2808;
goto block_2654;
}
}
}
block_2824:
{
uint8_t x_2821; 
x_2821 = l_Lean_Expr_isErased(x_2811);
lean_dec_ref(x_2811);
if (x_2821 == 0)
{
lean_dec(x_2812);
x_2655 = x_2817;
x_2656 = x_2820;
x_2657 = x_2819;
x_2658 = x_2814;
x_2659 = x_2818;
x_2660 = x_2810;
x_2661 = x_2813;
x_2662 = x_2816;
x_2663 = x_2815;
x_2664 = x_2568;
goto block_2809;
}
else
{
lean_object* x_2822; uint8_t x_2823; 
x_2822 = lean_box(1);
x_2823 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1209_(x_2812, x_2822);
lean_dec(x_2812);
if (x_2823 == 0)
{
x_2655 = x_2817;
x_2656 = x_2820;
x_2657 = x_2819;
x_2658 = x_2814;
x_2659 = x_2818;
x_2660 = x_2810;
x_2661 = x_2813;
x_2662 = x_2816;
x_2663 = x_2815;
x_2664 = x_2821;
goto block_2809;
}
else
{
x_2655 = x_2817;
x_2656 = x_2820;
x_2657 = x_2819;
x_2658 = x_2814;
x_2659 = x_2818;
x_2660 = x_2810;
x_2661 = x_2813;
x_2662 = x_2816;
x_2663 = x_2815;
x_2664 = x_2568;
goto block_2809;
}
}
}
block_2854:
{
lean_object* x_2836; lean_object* x_2837; lean_object* x_2838; 
x_2836 = lean_ctor_get(x_2826, 2);
lean_inc_ref(x_2836);
x_2837 = lean_ctor_get(x_2826, 3);
lean_inc(x_2837);
lean_inc(x_2834);
lean_inc_ref(x_2833);
lean_inc(x_2832);
lean_inc_ref(x_2831);
lean_inc_ref(x_2830);
lean_inc(x_2837);
x_2838 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_2837, x_2828, x_2830, x_2831, x_2832, x_2833, x_2834, x_2835);
if (lean_obj_tag(x_2838) == 0)
{
lean_object* x_2839; 
x_2839 = lean_ctor_get(x_2838, 0);
lean_inc(x_2839);
if (lean_obj_tag(x_2839) == 0)
{
lean_object* x_2840; 
x_2840 = lean_ctor_get(x_2838, 1);
lean_inc(x_2840);
lean_dec_ref(x_2838);
x_2810 = x_2826;
x_2811 = x_2836;
x_2812 = x_2837;
x_2813 = x_2828;
x_2814 = x_2829;
x_2815 = x_2830;
x_2816 = x_2831;
x_2817 = x_2832;
x_2818 = x_2833;
x_2819 = x_2834;
x_2820 = x_2840;
goto block_2824;
}
else
{
lean_object* x_2841; lean_object* x_2842; lean_object* x_2843; lean_object* x_2844; lean_object* x_2845; lean_object* x_2846; lean_object* x_2847; lean_object* x_2848; lean_object* x_2849; 
lean_dec(x_2837);
lean_dec_ref(x_2836);
x_2841 = lean_ctor_get(x_2838, 1);
lean_inc(x_2841);
lean_dec_ref(x_2838);
x_2842 = lean_ctor_get(x_2839, 0);
lean_inc(x_2842);
lean_dec_ref(x_2839);
x_2843 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_2829, x_2841);
x_2844 = lean_ctor_get(x_2843, 1);
lean_inc(x_2844);
lean_dec_ref(x_2843);
x_2845 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_2826, x_2842, x_2832, x_2844);
x_2846 = lean_ctor_get(x_2845, 0);
lean_inc(x_2846);
x_2847 = lean_ctor_get(x_2845, 1);
lean_inc(x_2847);
lean_dec_ref(x_2845);
x_2848 = lean_ctor_get(x_2846, 2);
lean_inc_ref(x_2848);
x_2849 = lean_ctor_get(x_2846, 3);
lean_inc(x_2849);
x_2810 = x_2846;
x_2811 = x_2848;
x_2812 = x_2849;
x_2813 = x_2828;
x_2814 = x_2829;
x_2815 = x_2830;
x_2816 = x_2831;
x_2817 = x_2832;
x_2818 = x_2833;
x_2819 = x_2834;
x_2820 = x_2847;
goto block_2824;
}
}
else
{
lean_object* x_2850; lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; 
lean_dec(x_2837);
lean_dec_ref(x_2836);
lean_dec(x_2834);
lean_dec_ref(x_2833);
lean_dec(x_2832);
lean_dec_ref(x_2831);
lean_dec_ref(x_2830);
lean_dec(x_2829);
lean_dec_ref(x_2828);
lean_dec(x_2826);
lean_dec_ref(x_2630);
lean_dec_ref(x_1);
x_2850 = lean_ctor_get(x_2838, 0);
lean_inc(x_2850);
x_2851 = lean_ctor_get(x_2838, 1);
lean_inc(x_2851);
if (lean_is_exclusive(x_2838)) {
 lean_ctor_release(x_2838, 0);
 lean_ctor_release(x_2838, 1);
 x_2852 = x_2838;
} else {
 lean_dec_ref(x_2838);
 x_2852 = lean_box(0);
}
if (lean_is_scalar(x_2852)) {
 x_2853 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2853 = x_2852;
}
lean_ctor_set(x_2853, 0, x_2850);
lean_ctor_set(x_2853, 1, x_2851);
return x_2853;
}
}
block_2857:
{
lean_object* x_2855; lean_object* x_2856; 
x_2855 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_2827);
x_2856 = lean_ctor_get(x_2855, 1);
lean_inc(x_2856);
lean_dec_ref(x_2855);
x_2828 = x_2;
x_2829 = x_3;
x_2830 = x_4;
x_2831 = x_5;
x_2832 = x_6;
x_2833 = x_2628;
x_2834 = x_8;
x_2835 = x_2856;
goto block_2854;
}
}
case 3:
{
lean_object* x_2859; lean_object* x_2860; lean_object* x_2861; lean_object* x_2862; lean_object* x_2863; lean_object* x_2864; lean_object* x_2865; 
lean_dec_ref(x_2552);
x_2859 = lean_ctor_get(x_1, 0);
lean_inc(x_2859);
x_2860 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2860);
x_2861 = lean_st_ref_get(x_3, x_2571);
x_2862 = lean_ctor_get(x_2861, 0);
lean_inc(x_2862);
x_2863 = lean_ctor_get(x_2861, 1);
lean_inc(x_2863);
lean_dec_ref(x_2861);
x_2864 = lean_ctor_get(x_2862, 0);
lean_inc_ref(x_2864);
lean_dec(x_2862);
x_2865 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_2864, x_2859, x_2568);
lean_dec_ref(x_2864);
if (lean_obj_tag(x_2865) == 0)
{
lean_object* x_2866; lean_object* x_2867; lean_object* x_2868; lean_object* x_2869; lean_object* x_2870; lean_object* x_2871; lean_object* x_2875; 
x_2866 = lean_ctor_get(x_2865, 0);
lean_inc(x_2866);
lean_dec_ref(x_2865);
x_2867 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_2568, x_2860, x_3, x_2863);
x_2868 = lean_ctor_get(x_2867, 0);
lean_inc(x_2868);
x_2869 = lean_ctor_get(x_2867, 1);
lean_inc(x_2869);
if (lean_is_exclusive(x_2867)) {
 lean_ctor_release(x_2867, 0);
 lean_ctor_release(x_2867, 1);
 x_2870 = x_2867;
} else {
 lean_dec_ref(x_2867);
 x_2870 = lean_box(0);
}
lean_inc(x_2868);
x_2875 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_2866, x_2868, x_2, x_3, x_4, x_5, x_6, x_2628, x_8, x_2869);
if (lean_obj_tag(x_2875) == 0)
{
lean_object* x_2876; 
x_2876 = lean_ctor_get(x_2875, 0);
lean_inc(x_2876);
if (lean_obj_tag(x_2876) == 0)
{
lean_object* x_2877; lean_object* x_2878; lean_object* x_2879; lean_object* x_2880; lean_object* x_2881; uint8_t x_2882; 
lean_dec_ref(x_2628);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_2877 = lean_ctor_get(x_2875, 1);
lean_inc(x_2877);
lean_dec_ref(x_2875);
lean_inc(x_2866);
x_2878 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_2866, x_3, x_2877);
x_2879 = lean_ctor_get(x_2878, 1);
lean_inc(x_2879);
lean_dec_ref(x_2878);
x_2880 = lean_unsigned_to_nat(0u);
x_2881 = lean_array_get_size(x_2868);
x_2882 = lean_nat_dec_lt(x_2880, x_2881);
if (x_2882 == 0)
{
lean_dec(x_2881);
lean_dec(x_3);
x_2871 = x_2879;
goto block_2874;
}
else
{
uint8_t x_2883; 
x_2883 = lean_nat_dec_le(x_2881, x_2881);
if (x_2883 == 0)
{
lean_dec(x_2881);
lean_dec(x_3);
x_2871 = x_2879;
goto block_2874;
}
else
{
lean_object* x_2884; size_t x_2885; size_t x_2886; lean_object* x_2887; lean_object* x_2888; 
x_2884 = lean_box(0);
x_2885 = 0;
x_2886 = lean_usize_of_nat(x_2881);
lean_dec(x_2881);
x_2887 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_2868, x_2885, x_2886, x_2884, x_3, x_2879);
lean_dec(x_3);
x_2888 = lean_ctor_get(x_2887, 1);
lean_inc(x_2888);
lean_dec_ref(x_2887);
x_2871 = x_2888;
goto block_2874;
}
}
}
else
{
lean_object* x_2889; lean_object* x_2890; 
lean_dec(x_2870);
lean_dec(x_2868);
lean_dec(x_2866);
lean_dec_ref(x_1);
x_2889 = lean_ctor_get(x_2875, 1);
lean_inc(x_2889);
lean_dec_ref(x_2875);
x_2890 = lean_ctor_get(x_2876, 0);
lean_inc(x_2890);
lean_dec_ref(x_2876);
x_1 = x_2890;
x_7 = x_2628;
x_9 = x_2889;
goto _start;
}
}
else
{
lean_object* x_2892; lean_object* x_2893; lean_object* x_2894; lean_object* x_2895; 
lean_dec(x_2870);
lean_dec(x_2868);
lean_dec(x_2866);
lean_dec_ref(x_2628);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2892 = lean_ctor_get(x_2875, 0);
lean_inc(x_2892);
x_2893 = lean_ctor_get(x_2875, 1);
lean_inc(x_2893);
if (lean_is_exclusive(x_2875)) {
 lean_ctor_release(x_2875, 0);
 lean_ctor_release(x_2875, 1);
 x_2894 = x_2875;
} else {
 lean_dec_ref(x_2875);
 x_2894 = lean_box(0);
}
if (lean_is_scalar(x_2894)) {
 x_2895 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2895 = x_2894;
}
lean_ctor_set(x_2895, 0, x_2892);
lean_ctor_set(x_2895, 1, x_2893);
return x_2895;
}
block_2874:
{
lean_object* x_2872; lean_object* x_2873; 
x_2872 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_1, x_2866, x_2868);
lean_dec_ref(x_1);
if (lean_is_scalar(x_2870)) {
 x_2873 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2873 = x_2870;
}
lean_ctor_set(x_2873, 0, x_2872);
lean_ctor_set(x_2873, 1, x_2871);
return x_2873;
}
}
else
{
lean_object* x_2896; 
lean_dec_ref(x_2860);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2896 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_2628, x_8, x_2863);
lean_dec(x_8);
lean_dec_ref(x_2628);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_2896;
}
}
case 4:
{
lean_object* x_2897; lean_object* x_2898; 
x_2897 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2897);
lean_inc(x_8);
lean_inc_ref(x_2628);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_2897);
x_2898 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_2897, x_2, x_3, x_4, x_5, x_6, x_2628, x_8, x_2571);
if (lean_obj_tag(x_2898) == 0)
{
lean_object* x_2899; 
x_2899 = lean_ctor_get(x_2898, 0);
lean_inc(x_2899);
if (lean_obj_tag(x_2899) == 0)
{
lean_object* x_2900; lean_object* x_2901; lean_object* x_2902; lean_object* x_2903; lean_object* x_2904; lean_object* x_2905; lean_object* x_2906; lean_object* x_2907; lean_object* x_2908; 
x_2900 = lean_ctor_get(x_2898, 1);
lean_inc(x_2900);
lean_dec_ref(x_2898);
x_2901 = lean_st_ref_get(x_3, x_2900);
x_2902 = lean_ctor_get(x_2901, 0);
lean_inc(x_2902);
x_2903 = lean_ctor_get(x_2901, 1);
lean_inc(x_2903);
lean_dec_ref(x_2901);
x_2904 = lean_ctor_get(x_2897, 1);
lean_inc_ref(x_2904);
x_2905 = lean_ctor_get(x_2897, 2);
lean_inc(x_2905);
x_2906 = lean_ctor_get(x_2897, 3);
lean_inc_ref(x_2906);
lean_dec_ref(x_2897);
x_2907 = lean_ctor_get(x_2902, 0);
lean_inc_ref(x_2907);
lean_dec(x_2902);
x_2908 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_2907, x_2905, x_2568);
lean_dec_ref(x_2907);
if (lean_obj_tag(x_2908) == 0)
{
lean_object* x_2909; lean_object* x_2910; lean_object* x_2911; lean_object* x_2912; lean_object* x_2913; lean_object* x_2914; lean_object* x_2915; lean_object* x_2916; 
x_2909 = lean_ctor_get(x_2908, 0);
lean_inc(x_2909);
lean_dec_ref(x_2908);
x_2910 = lean_st_ref_get(x_3, x_2903);
x_2911 = lean_ctor_get(x_2910, 0);
lean_inc(x_2911);
x_2912 = lean_ctor_get(x_2910, 1);
lean_inc(x_2912);
lean_dec_ref(x_2910);
x_2913 = lean_box(x_2568);
lean_inc(x_2909);
x_2914 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__1___boxed), 11, 2);
lean_closure_set(x_2914, 0, x_2909);
lean_closure_set(x_2914, 1, x_2913);
x_2915 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_2552, x_2906, x_2914);
lean_inc(x_8);
lean_inc_ref(x_2628);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_2916 = lean_apply_8(x_2915, x_2, x_3, x_4, x_5, x_6, x_2628, x_8, x_2912);
if (lean_obj_tag(x_2916) == 0)
{
lean_object* x_2917; lean_object* x_2918; lean_object* x_2919; 
x_2917 = lean_ctor_get(x_2916, 0);
lean_inc(x_2917);
x_2918 = lean_ctor_get(x_2916, 1);
lean_inc(x_2918);
lean_dec_ref(x_2916);
lean_inc(x_6);
lean_inc(x_3);
x_2919 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_2917, x_2, x_3, x_4, x_5, x_6, x_2628, x_8, x_2918);
if (lean_obj_tag(x_2919) == 0)
{
lean_object* x_2920; lean_object* x_2921; lean_object* x_2922; lean_object* x_2923; lean_object* x_2924; lean_object* x_2925; lean_object* x_2926; lean_object* x_2933; uint8_t x_2934; 
x_2920 = lean_ctor_get(x_2919, 0);
lean_inc(x_2920);
x_2921 = lean_ctor_get(x_2919, 1);
lean_inc(x_2921);
if (lean_is_exclusive(x_2919)) {
 lean_ctor_release(x_2919, 0);
 lean_ctor_release(x_2919, 1);
 x_2922 = x_2919;
} else {
 lean_dec_ref(x_2919);
 x_2922 = lean_box(0);
}
x_2923 = lean_ctor_get(x_2911, 0);
lean_inc_ref(x_2923);
lean_dec(x_2911);
x_2924 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_2923, x_2568, x_2904);
lean_dec_ref(x_2923);
x_2933 = lean_array_get_size(x_2920);
x_2934 = lean_nat_dec_eq(x_2933, x_2626);
lean_dec(x_2933);
if (x_2934 == 0)
{
lean_dec(x_2922);
lean_dec(x_6);
x_2925 = x_3;
x_2926 = x_2921;
goto block_2932;
}
else
{
lean_object* x_2935; lean_object* x_2936; 
x_2935 = lean_unsigned_to_nat(0u);
x_2936 = lean_array_fget(x_2920, x_2935);
if (lean_obj_tag(x_2936) == 0)
{
lean_object* x_2937; lean_object* x_2938; lean_object* x_2939; lean_object* x_2945; lean_object* x_2946; uint8_t x_2955; lean_object* x_2956; uint8_t x_2958; 
lean_dec(x_2922);
x_2937 = lean_ctor_get(x_2936, 1);
lean_inc_ref(x_2937);
x_2938 = lean_ctor_get(x_2936, 2);
lean_inc_ref(x_2938);
lean_dec_ref(x_2936);
x_2945 = lean_array_get_size(x_2937);
x_2958 = lean_nat_dec_lt(x_2935, x_2945);
if (x_2958 == 0)
{
x_2955 = x_2568;
x_2956 = x_2921;
goto block_2957;
}
else
{
if (x_2958 == 0)
{
x_2955 = x_2568;
x_2956 = x_2921;
goto block_2957;
}
else
{
size_t x_2959; size_t x_2960; lean_object* x_2961; lean_object* x_2962; lean_object* x_2963; uint8_t x_2964; 
x_2959 = 0;
x_2960 = lean_usize_of_nat(x_2945);
x_2961 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_2937, x_2959, x_2960, x_3, x_2921);
x_2962 = lean_ctor_get(x_2961, 0);
lean_inc(x_2962);
x_2963 = lean_ctor_get(x_2961, 1);
lean_inc(x_2963);
lean_dec_ref(x_2961);
x_2964 = lean_unbox(x_2962);
lean_dec(x_2962);
x_2955 = x_2964;
x_2956 = x_2963;
goto block_2957;
}
}
block_2944:
{
lean_object* x_2940; lean_object* x_2941; lean_object* x_2942; lean_object* x_2943; 
x_2940 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_2939);
lean_dec(x_3);
x_2941 = lean_ctor_get(x_2940, 1);
lean_inc(x_2941);
if (lean_is_exclusive(x_2940)) {
 lean_ctor_release(x_2940, 0);
 lean_ctor_release(x_2940, 1);
 x_2942 = x_2940;
} else {
 lean_dec_ref(x_2940);
 x_2942 = lean_box(0);
}
if (lean_is_scalar(x_2942)) {
 x_2943 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2943 = x_2942;
}
lean_ctor_set(x_2943, 0, x_2938);
lean_ctor_set(x_2943, 1, x_2941);
return x_2943;
}
block_2954:
{
uint8_t x_2947; 
x_2947 = lean_nat_dec_lt(x_2935, x_2945);
if (x_2947 == 0)
{
lean_dec(x_2945);
lean_dec_ref(x_2937);
lean_dec(x_6);
x_2939 = x_2946;
goto block_2944;
}
else
{
uint8_t x_2948; 
x_2948 = lean_nat_dec_le(x_2945, x_2945);
if (x_2948 == 0)
{
lean_dec(x_2945);
lean_dec_ref(x_2937);
lean_dec(x_6);
x_2939 = x_2946;
goto block_2944;
}
else
{
lean_object* x_2949; size_t x_2950; size_t x_2951; lean_object* x_2952; lean_object* x_2953; 
x_2949 = lean_box(0);
x_2950 = 0;
x_2951 = lean_usize_of_nat(x_2945);
lean_dec(x_2945);
x_2952 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_2937, x_2950, x_2951, x_2949, x_6, x_2946);
lean_dec(x_6);
lean_dec_ref(x_2937);
x_2953 = lean_ctor_get(x_2952, 1);
lean_inc(x_2953);
lean_dec_ref(x_2952);
x_2939 = x_2953;
goto block_2944;
}
}
}
block_2957:
{
if (x_2955 == 0)
{
lean_dec_ref(x_2924);
lean_dec(x_2920);
lean_dec(x_2909);
lean_dec_ref(x_1);
x_2946 = x_2956;
goto block_2954;
}
else
{
if (x_2568 == 0)
{
lean_dec(x_2945);
lean_dec_ref(x_2938);
lean_dec_ref(x_2937);
lean_dec(x_6);
x_2925 = x_3;
x_2926 = x_2956;
goto block_2932;
}
else
{
lean_dec_ref(x_2924);
lean_dec(x_2920);
lean_dec(x_2909);
lean_dec_ref(x_1);
x_2946 = x_2956;
goto block_2954;
}
}
}
}
else
{
lean_object* x_2965; lean_object* x_2966; 
lean_dec_ref(x_2924);
lean_dec(x_2920);
lean_dec(x_2909);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_2965 = lean_ctor_get(x_2936, 0);
lean_inc_ref(x_2965);
lean_dec_ref(x_2936);
if (lean_is_scalar(x_2922)) {
 x_2966 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2966 = x_2922;
}
lean_ctor_set(x_2966, 0, x_2965);
lean_ctor_set(x_2966, 1, x_2921);
return x_2966;
}
}
block_2932:
{
lean_object* x_2927; lean_object* x_2928; lean_object* x_2929; lean_object* x_2930; lean_object* x_2931; 
lean_inc(x_2909);
x_2927 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_2909, x_2925, x_2926);
lean_dec(x_2925);
x_2928 = lean_ctor_get(x_2927, 1);
lean_inc(x_2928);
if (lean_is_exclusive(x_2927)) {
 lean_ctor_release(x_2927, 0);
 lean_ctor_release(x_2927, 1);
 x_2929 = x_2927;
} else {
 lean_dec_ref(x_2927);
 x_2929 = lean_box(0);
}
x_2930 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_1, x_2924, x_2909, x_2920);
if (lean_is_scalar(x_2929)) {
 x_2931 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2931 = x_2929;
}
lean_ctor_set(x_2931, 0, x_2930);
lean_ctor_set(x_2931, 1, x_2928);
return x_2931;
}
}
else
{
lean_object* x_2967; lean_object* x_2968; lean_object* x_2969; lean_object* x_2970; 
lean_dec(x_2911);
lean_dec(x_2909);
lean_dec_ref(x_2904);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_2967 = lean_ctor_get(x_2919, 0);
lean_inc(x_2967);
x_2968 = lean_ctor_get(x_2919, 1);
lean_inc(x_2968);
if (lean_is_exclusive(x_2919)) {
 lean_ctor_release(x_2919, 0);
 lean_ctor_release(x_2919, 1);
 x_2969 = x_2919;
} else {
 lean_dec_ref(x_2919);
 x_2969 = lean_box(0);
}
if (lean_is_scalar(x_2969)) {
 x_2970 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2970 = x_2969;
}
lean_ctor_set(x_2970, 0, x_2967);
lean_ctor_set(x_2970, 1, x_2968);
return x_2970;
}
}
else
{
lean_object* x_2971; lean_object* x_2972; lean_object* x_2973; lean_object* x_2974; 
lean_dec(x_2911);
lean_dec(x_2909);
lean_dec_ref(x_2904);
lean_dec_ref(x_2628);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2971 = lean_ctor_get(x_2916, 0);
lean_inc(x_2971);
x_2972 = lean_ctor_get(x_2916, 1);
lean_inc(x_2972);
if (lean_is_exclusive(x_2916)) {
 lean_ctor_release(x_2916, 0);
 lean_ctor_release(x_2916, 1);
 x_2973 = x_2916;
} else {
 lean_dec_ref(x_2916);
 x_2973 = lean_box(0);
}
if (lean_is_scalar(x_2973)) {
 x_2974 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2974 = x_2973;
}
lean_ctor_set(x_2974, 0, x_2971);
lean_ctor_set(x_2974, 1, x_2972);
return x_2974;
}
}
else
{
lean_object* x_2975; 
lean_dec_ref(x_2906);
lean_dec_ref(x_2904);
lean_dec_ref(x_2552);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2975 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_2628, x_8, x_2903);
lean_dec(x_8);
lean_dec_ref(x_2628);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_2975;
}
}
else
{
lean_object* x_2976; lean_object* x_2977; lean_object* x_2978; lean_object* x_2979; 
lean_dec_ref(x_2897);
lean_dec_ref(x_2628);
lean_dec_ref(x_2552);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2976 = lean_ctor_get(x_2898, 1);
lean_inc(x_2976);
if (lean_is_exclusive(x_2898)) {
 lean_ctor_release(x_2898, 0);
 lean_ctor_release(x_2898, 1);
 x_2977 = x_2898;
} else {
 lean_dec_ref(x_2898);
 x_2977 = lean_box(0);
}
x_2978 = lean_ctor_get(x_2899, 0);
lean_inc(x_2978);
lean_dec_ref(x_2899);
if (lean_is_scalar(x_2977)) {
 x_2979 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2979 = x_2977;
}
lean_ctor_set(x_2979, 0, x_2978);
lean_ctor_set(x_2979, 1, x_2976);
return x_2979;
}
}
else
{
lean_object* x_2980; lean_object* x_2981; lean_object* x_2982; lean_object* x_2983; 
lean_dec_ref(x_2897);
lean_dec_ref(x_2628);
lean_dec_ref(x_2552);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_2980 = lean_ctor_get(x_2898, 0);
lean_inc(x_2980);
x_2981 = lean_ctor_get(x_2898, 1);
lean_inc(x_2981);
if (lean_is_exclusive(x_2898)) {
 lean_ctor_release(x_2898, 0);
 lean_ctor_release(x_2898, 1);
 x_2982 = x_2898;
} else {
 lean_dec_ref(x_2898);
 x_2982 = lean_box(0);
}
if (lean_is_scalar(x_2982)) {
 x_2983 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2983 = x_2982;
}
lean_ctor_set(x_2983, 0, x_2980);
lean_ctor_set(x_2983, 1, x_2981);
return x_2983;
}
}
case 5:
{
lean_object* x_2984; lean_object* x_2985; lean_object* x_2986; lean_object* x_2987; lean_object* x_2988; lean_object* x_2989; 
lean_dec_ref(x_2552);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_2984 = lean_ctor_get(x_1, 0);
lean_inc(x_2984);
x_2985 = lean_st_ref_get(x_3, x_2571);
x_2986 = lean_ctor_get(x_2985, 0);
lean_inc(x_2986);
x_2987 = lean_ctor_get(x_2985, 1);
lean_inc(x_2987);
lean_dec_ref(x_2985);
x_2988 = lean_ctor_get(x_2986, 0);
lean_inc_ref(x_2988);
lean_dec(x_2986);
x_2989 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_2988, x_2984, x_2568);
lean_dec_ref(x_2988);
if (lean_obj_tag(x_2989) == 0)
{
lean_object* x_2990; lean_object* x_2991; lean_object* x_2992; lean_object* x_2993; lean_object* x_2994; lean_object* x_2995; 
lean_dec_ref(x_2628);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_2990 = lean_ctor_get(x_2989, 0);
lean_inc(x_2990);
lean_dec_ref(x_2989);
lean_inc(x_2990);
x_2991 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_2990, x_3, x_2987);
lean_dec(x_3);
x_2992 = lean_ctor_get(x_2991, 1);
lean_inc(x_2992);
if (lean_is_exclusive(x_2991)) {
 lean_ctor_release(x_2991, 0);
 lean_ctor_release(x_2991, 1);
 x_2993 = x_2991;
} else {
 lean_dec_ref(x_2991);
 x_2993 = lean_box(0);
}
x_2994 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_1, x_2990);
if (lean_is_scalar(x_2993)) {
 x_2995 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2995 = x_2993;
}
lean_ctor_set(x_2995, 0, x_2994);
lean_ctor_set(x_2995, 1, x_2992);
return x_2995;
}
else
{
lean_object* x_2996; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_2996 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_2628, x_8, x_2987);
lean_dec(x_8);
lean_dec_ref(x_2628);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_2996;
}
}
case 6:
{
lean_object* x_2997; lean_object* x_2998; lean_object* x_2999; lean_object* x_3000; lean_object* x_3001; lean_object* x_3002; lean_object* x_3003; lean_object* x_3004; lean_object* x_3005; 
lean_dec_ref(x_2628);
lean_dec_ref(x_2552);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_2997 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2997);
x_2998 = lean_st_ref_get(x_3, x_2571);
lean_dec(x_3);
x_2999 = lean_ctor_get(x_2998, 0);
lean_inc(x_2999);
x_3000 = lean_ctor_get(x_2998, 1);
lean_inc(x_3000);
if (lean_is_exclusive(x_2998)) {
 lean_ctor_release(x_2998, 0);
 lean_ctor_release(x_2998, 1);
 x_3001 = x_2998;
} else {
 lean_dec_ref(x_2998);
 x_3001 = lean_box(0);
}
x_3002 = lean_ctor_get(x_2999, 0);
lean_inc_ref(x_3002);
lean_dec(x_2999);
x_3003 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_3002, x_2568, x_2997);
lean_dec_ref(x_3002);
x_3004 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(x_1, x_3003);
if (lean_is_scalar(x_3001)) {
 x_3005 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3005 = x_3001;
}
lean_ctor_set(x_3005, 0, x_3004);
lean_ctor_set(x_3005, 1, x_3000);
return x_3005;
}
default: 
{
lean_object* x_3006; lean_object* x_3007; 
lean_dec_ref(x_2552);
x_3006 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3006);
x_3007 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3007);
x_2572 = x_3006;
x_2573 = x_3007;
x_2574 = x_2;
x_2575 = x_3;
x_2576 = x_4;
x_2577 = x_5;
x_2578 = x_6;
x_2579 = x_2628;
x_2580 = x_8;
goto block_2625;
}
}
block_2625:
{
lean_object* x_2581; lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; uint8_t x_2588; 
x_2581 = lean_ctor_get(x_2572, 0);
lean_inc(x_2581);
x_2582 = lean_ctor_get(x_2572, 2);
lean_inc_ref(x_2582);
x_2583 = lean_ctor_get(x_2572, 3);
lean_inc_ref(x_2583);
x_2584 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_2581, x_2575, x_2571);
lean_dec(x_2581);
x_2585 = lean_ctor_get(x_2584, 0);
lean_inc(x_2585);
x_2586 = lean_ctor_get(x_2584, 1);
lean_inc(x_2586);
lean_dec_ref(x_2584);
lean_inc(x_2585);
lean_inc_ref(x_1);
lean_inc_ref(x_2573);
x_2587 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_2587, 0, x_2573);
lean_closure_set(x_2587, 1, x_1);
lean_closure_set(x_2587, 2, x_2585);
x_2588 = lean_unbox(x_2585);
if (x_2588 == 0)
{
uint8_t x_2589; 
lean_dec(x_2585);
lean_dec_ref(x_2573);
x_2589 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_2589 == 0)
{
lean_dec_ref(x_2583);
lean_dec_ref(x_2582);
x_10 = x_2587;
x_11 = x_2572;
x_12 = x_2574;
x_13 = x_2575;
x_14 = x_2576;
x_15 = x_2577;
x_16 = x_2578;
x_17 = x_2579;
x_18 = x_2580;
x_19 = x_2586;
goto block_29;
}
else
{
uint8_t x_2590; 
x_2590 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_2583, x_2582);
lean_dec_ref(x_2582);
if (x_2590 == 0)
{
x_10 = x_2587;
x_11 = x_2572;
x_12 = x_2574;
x_13 = x_2575;
x_14 = x_2576;
x_15 = x_2577;
x_16 = x_2578;
x_17 = x_2579;
x_18 = x_2580;
x_19 = x_2586;
goto block_29;
}
else
{
lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; 
x_2591 = lean_st_ref_get(x_2575, x_2586);
x_2592 = lean_ctor_get(x_2591, 0);
lean_inc(x_2592);
x_2593 = lean_ctor_get(x_2591, 1);
lean_inc(x_2593);
lean_dec_ref(x_2591);
x_2594 = lean_ctor_get(x_2592, 0);
lean_inc_ref(x_2594);
lean_dec(x_2592);
lean_inc(x_2580);
lean_inc_ref(x_2579);
lean_inc(x_2578);
lean_inc_ref(x_2577);
x_2595 = l_Lean_Compiler_LCNF_normFunDeclImp(x_2568, x_2572, x_2594, x_2577, x_2578, x_2579, x_2580, x_2593);
if (lean_obj_tag(x_2595) == 0)
{
lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; 
x_2596 = lean_ctor_get(x_2595, 0);
lean_inc(x_2596);
x_2597 = lean_ctor_get(x_2595, 1);
lean_inc(x_2597);
lean_dec_ref(x_2595);
lean_inc(x_2580);
lean_inc_ref(x_2579);
lean_inc(x_2578);
lean_inc_ref(x_2577);
x_2598 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_2596, x_2577, x_2578, x_2579, x_2580, x_2597);
if (lean_obj_tag(x_2598) == 0)
{
lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; 
x_2599 = lean_ctor_get(x_2598, 0);
lean_inc(x_2599);
x_2600 = lean_ctor_get(x_2598, 1);
lean_inc(x_2600);
lean_dec_ref(x_2598);
x_2601 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_2575, x_2600);
x_2602 = lean_ctor_get(x_2601, 1);
lean_inc(x_2602);
lean_dec_ref(x_2601);
x_10 = x_2587;
x_11 = x_2599;
x_12 = x_2574;
x_13 = x_2575;
x_14 = x_2576;
x_15 = x_2577;
x_16 = x_2578;
x_17 = x_2579;
x_18 = x_2580;
x_19 = x_2602;
goto block_29;
}
else
{
lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; lean_object* x_2606; 
lean_dec_ref(x_2587);
lean_dec(x_2580);
lean_dec_ref(x_2579);
lean_dec(x_2578);
lean_dec_ref(x_2577);
lean_dec_ref(x_2576);
lean_dec(x_2575);
lean_dec_ref(x_2574);
x_2603 = lean_ctor_get(x_2598, 0);
lean_inc(x_2603);
x_2604 = lean_ctor_get(x_2598, 1);
lean_inc(x_2604);
if (lean_is_exclusive(x_2598)) {
 lean_ctor_release(x_2598, 0);
 lean_ctor_release(x_2598, 1);
 x_2605 = x_2598;
} else {
 lean_dec_ref(x_2598);
 x_2605 = lean_box(0);
}
if (lean_is_scalar(x_2605)) {
 x_2606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2606 = x_2605;
}
lean_ctor_set(x_2606, 0, x_2603);
lean_ctor_set(x_2606, 1, x_2604);
return x_2606;
}
}
else
{
lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; 
lean_dec_ref(x_2587);
lean_dec(x_2580);
lean_dec_ref(x_2579);
lean_dec(x_2578);
lean_dec_ref(x_2577);
lean_dec_ref(x_2576);
lean_dec(x_2575);
lean_dec_ref(x_2574);
x_2607 = lean_ctor_get(x_2595, 0);
lean_inc(x_2607);
x_2608 = lean_ctor_get(x_2595, 1);
lean_inc(x_2608);
if (lean_is_exclusive(x_2595)) {
 lean_ctor_release(x_2595, 0);
 lean_ctor_release(x_2595, 1);
 x_2609 = x_2595;
} else {
 lean_dec_ref(x_2595);
 x_2609 = lean_box(0);
}
if (lean_is_scalar(x_2609)) {
 x_2610 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2610 = x_2609;
}
lean_ctor_set(x_2610, 0, x_2607);
lean_ctor_set(x_2610, 1, x_2608);
return x_2610;
}
}
}
}
else
{
lean_object* x_2611; lean_object* x_2612; lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; 
lean_dec_ref(x_2587);
lean_dec_ref(x_2583);
lean_dec_ref(x_2582);
x_2611 = lean_st_ref_get(x_2575, x_2586);
x_2612 = lean_ctor_get(x_2611, 0);
lean_inc(x_2612);
x_2613 = lean_ctor_get(x_2611, 1);
lean_inc(x_2613);
lean_dec_ref(x_2611);
x_2614 = lean_ctor_get(x_2612, 0);
lean_inc_ref(x_2614);
lean_dec(x_2612);
lean_inc(x_2580);
lean_inc_ref(x_2579);
lean_inc(x_2578);
lean_inc_ref(x_2577);
x_2615 = l_Lean_Compiler_LCNF_normFunDeclImp(x_2568, x_2572, x_2614, x_2577, x_2578, x_2579, x_2580, x_2613);
if (lean_obj_tag(x_2615) == 0)
{
lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; uint8_t x_2619; lean_object* x_2620; 
x_2616 = lean_ctor_get(x_2615, 0);
lean_inc(x_2616);
x_2617 = lean_ctor_get(x_2615, 1);
lean_inc(x_2617);
lean_dec_ref(x_2615);
x_2618 = lean_box(0);
x_2619 = lean_unbox(x_2585);
lean_dec(x_2585);
x_2620 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_2573, x_1, x_2619, x_2616, x_2618, x_2574, x_2575, x_2576, x_2577, x_2578, x_2579, x_2580, x_2617);
lean_dec_ref(x_1);
return x_2620;
}
else
{
lean_object* x_2621; lean_object* x_2622; lean_object* x_2623; lean_object* x_2624; 
lean_dec(x_2585);
lean_dec(x_2580);
lean_dec_ref(x_2579);
lean_dec(x_2578);
lean_dec_ref(x_2577);
lean_dec_ref(x_2576);
lean_dec(x_2575);
lean_dec_ref(x_2574);
lean_dec_ref(x_2573);
lean_dec_ref(x_1);
x_2621 = lean_ctor_get(x_2615, 0);
lean_inc(x_2621);
x_2622 = lean_ctor_get(x_2615, 1);
lean_inc(x_2622);
if (lean_is_exclusive(x_2615)) {
 lean_ctor_release(x_2615, 0);
 lean_ctor_release(x_2615, 1);
 x_2623 = x_2615;
} else {
 lean_dec_ref(x_2615);
 x_2623 = lean_box(0);
}
if (lean_is_scalar(x_2623)) {
 x_2624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2624 = x_2623;
}
lean_ctor_set(x_2624, 0, x_2621);
lean_ctor_set(x_2624, 1, x_2622);
return x_2624;
}
}
}
}
else
{
lean_object* x_3008; 
lean_dec_ref(x_2567);
lean_dec(x_2565);
lean_dec(x_2563);
lean_dec(x_2562);
lean_dec(x_2561);
lean_dec(x_2560);
lean_dec(x_2559);
lean_dec(x_2558);
lean_dec(x_2557);
lean_dec(x_2556);
lean_dec(x_2555);
lean_dec_ref(x_2554);
lean_dec_ref(x_2553);
lean_dec_ref(x_2552);
lean_dec_ref(x_1);
x_3008 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_3008;
}
}
}
else
{
lean_object* x_3009; lean_object* x_3010; lean_object* x_3011; lean_object* x_3012; lean_object* x_3013; lean_object* x_3014; lean_object* x_3015; lean_object* x_3016; lean_object* x_3017; lean_object* x_3018; lean_object* x_3019; lean_object* x_3020; lean_object* x_3021; lean_object* x_3022; lean_object* x_3023; lean_object* x_3024; lean_object* x_3025; lean_object* x_3026; lean_object* x_3027; lean_object* x_3028; lean_object* x_3029; lean_object* x_3030; lean_object* x_3031; lean_object* x_3032; lean_object* x_3033; lean_object* x_3034; lean_object* x_3035; lean_object* x_3036; lean_object* x_3037; lean_object* x_3038; lean_object* x_3039; lean_object* x_3040; lean_object* x_3041; lean_object* x_3042; lean_object* x_3043; lean_object* x_3044; lean_object* x_3045; lean_object* x_3046; lean_object* x_3047; lean_object* x_3048; lean_object* x_3049; lean_object* x_3050; lean_object* x_3051; lean_object* x_3052; lean_object* x_3053; lean_object* x_3054; lean_object* x_3055; lean_object* x_3056; lean_object* x_3057; lean_object* x_3058; lean_object* x_3059; lean_object* x_3060; lean_object* x_3061; lean_object* x_3062; lean_object* x_3063; lean_object* x_3064; lean_object* x_3065; lean_object* x_3066; lean_object* x_3067; lean_object* x_3068; lean_object* x_3069; uint8_t x_3070; lean_object* x_3071; uint8_t x_3072; lean_object* x_3073; uint8_t x_3074; 
x_3009 = lean_ctor_get(x_32, 0);
x_3010 = lean_ctor_get(x_32, 2);
x_3011 = lean_ctor_get(x_32, 3);
x_3012 = lean_ctor_get(x_32, 4);
lean_inc(x_3012);
lean_inc(x_3011);
lean_inc(x_3010);
lean_inc(x_3009);
lean_dec(x_32);
x_3013 = l_Lean_Compiler_LCNF_Simp_simp___closed__2;
x_3014 = l_Lean_Compiler_LCNF_Simp_simp___closed__3;
lean_inc_ref(x_3009);
x_3015 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_3015, 0, x_3009);
x_3016 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3016, 0, x_3009);
x_3017 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3017, 0, x_3015);
lean_ctor_set(x_3017, 1, x_3016);
x_3018 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3018, 0, x_3012);
x_3019 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_3019, 0, x_3011);
x_3020 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_3020, 0, x_3010);
x_3021 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3021, 0, x_3017);
lean_ctor_set(x_3021, 1, x_3013);
lean_ctor_set(x_3021, 2, x_3020);
lean_ctor_set(x_3021, 3, x_3019);
lean_ctor_set(x_3021, 4, x_3018);
lean_ctor_set(x_30, 1, x_3014);
lean_ctor_set(x_30, 0, x_3021);
x_3022 = l_ReaderT_instMonad___redArg(x_30);
x_3023 = lean_ctor_get(x_3022, 0);
lean_inc_ref(x_3023);
if (lean_is_exclusive(x_3022)) {
 lean_ctor_release(x_3022, 0);
 lean_ctor_release(x_3022, 1);
 x_3024 = x_3022;
} else {
 lean_dec_ref(x_3022);
 x_3024 = lean_box(0);
}
x_3025 = lean_ctor_get(x_3023, 0);
lean_inc_ref(x_3025);
x_3026 = lean_ctor_get(x_3023, 2);
lean_inc_ref(x_3026);
x_3027 = lean_ctor_get(x_3023, 3);
lean_inc_ref(x_3027);
x_3028 = lean_ctor_get(x_3023, 4);
lean_inc_ref(x_3028);
if (lean_is_exclusive(x_3023)) {
 lean_ctor_release(x_3023, 0);
 lean_ctor_release(x_3023, 1);
 lean_ctor_release(x_3023, 2);
 lean_ctor_release(x_3023, 3);
 lean_ctor_release(x_3023, 4);
 x_3029 = x_3023;
} else {
 lean_dec_ref(x_3023);
 x_3029 = lean_box(0);
}
x_3030 = l_Lean_Compiler_LCNF_Simp_simp___closed__4;
x_3031 = l_Lean_Compiler_LCNF_Simp_simp___closed__5;
lean_inc_ref(x_3025);
x_3032 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_3032, 0, x_3025);
x_3033 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3033, 0, x_3025);
x_3034 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3034, 0, x_3032);
lean_ctor_set(x_3034, 1, x_3033);
x_3035 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3035, 0, x_3028);
x_3036 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_3036, 0, x_3027);
x_3037 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_3037, 0, x_3026);
if (lean_is_scalar(x_3029)) {
 x_3038 = lean_alloc_ctor(0, 5, 0);
} else {
 x_3038 = x_3029;
}
lean_ctor_set(x_3038, 0, x_3034);
lean_ctor_set(x_3038, 1, x_3030);
lean_ctor_set(x_3038, 2, x_3037);
lean_ctor_set(x_3038, 3, x_3036);
lean_ctor_set(x_3038, 4, x_3035);
if (lean_is_scalar(x_3024)) {
 x_3039 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3039 = x_3024;
}
lean_ctor_set(x_3039, 0, x_3038);
lean_ctor_set(x_3039, 1, x_3031);
x_3040 = l_ReaderT_instMonad___redArg(x_3039);
x_3041 = l_ReaderT_instMonad___redArg(x_3040);
x_3042 = lean_ctor_get(x_3041, 0);
lean_inc_ref(x_3042);
if (lean_is_exclusive(x_3041)) {
 lean_ctor_release(x_3041, 0);
 lean_ctor_release(x_3041, 1);
 x_3043 = x_3041;
} else {
 lean_dec_ref(x_3041);
 x_3043 = lean_box(0);
}
x_3044 = lean_ctor_get(x_3042, 0);
lean_inc_ref(x_3044);
x_3045 = lean_ctor_get(x_3042, 2);
lean_inc_ref(x_3045);
x_3046 = lean_ctor_get(x_3042, 3);
lean_inc_ref(x_3046);
x_3047 = lean_ctor_get(x_3042, 4);
lean_inc_ref(x_3047);
if (lean_is_exclusive(x_3042)) {
 lean_ctor_release(x_3042, 0);
 lean_ctor_release(x_3042, 1);
 lean_ctor_release(x_3042, 2);
 lean_ctor_release(x_3042, 3);
 lean_ctor_release(x_3042, 4);
 x_3048 = x_3042;
} else {
 lean_dec_ref(x_3042);
 x_3048 = lean_box(0);
}
x_3049 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_3050 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_3044);
x_3051 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_3051, 0, x_3044);
x_3052 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3052, 0, x_3044);
x_3053 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3053, 0, x_3051);
lean_ctor_set(x_3053, 1, x_3052);
x_3054 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3054, 0, x_3047);
x_3055 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_3055, 0, x_3046);
x_3056 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_3056, 0, x_3045);
if (lean_is_scalar(x_3048)) {
 x_3057 = lean_alloc_ctor(0, 5, 0);
} else {
 x_3057 = x_3048;
}
lean_ctor_set(x_3057, 0, x_3053);
lean_ctor_set(x_3057, 1, x_3049);
lean_ctor_set(x_3057, 2, x_3056);
lean_ctor_set(x_3057, 3, x_3055);
lean_ctor_set(x_3057, 4, x_3054);
if (lean_is_scalar(x_3043)) {
 x_3058 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3058 = x_3043;
}
lean_ctor_set(x_3058, 0, x_3057);
lean_ctor_set(x_3058, 1, x_3050);
x_3059 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_3059);
x_3060 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_3060);
x_3061 = lean_ctor_get(x_7, 2);
lean_inc(x_3061);
x_3062 = lean_ctor_get(x_7, 3);
lean_inc(x_3062);
x_3063 = lean_ctor_get(x_7, 4);
lean_inc(x_3063);
x_3064 = lean_ctor_get(x_7, 5);
lean_inc(x_3064);
x_3065 = lean_ctor_get(x_7, 6);
lean_inc(x_3065);
x_3066 = lean_ctor_get(x_7, 7);
lean_inc(x_3066);
x_3067 = lean_ctor_get(x_7, 8);
lean_inc(x_3067);
x_3068 = lean_ctor_get(x_7, 9);
lean_inc(x_3068);
x_3069 = lean_ctor_get(x_7, 10);
lean_inc(x_3069);
x_3070 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_3071 = lean_ctor_get(x_7, 11);
lean_inc(x_3071);
x_3072 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_3073 = lean_ctor_get(x_7, 12);
lean_inc_ref(x_3073);
x_3074 = lean_nat_dec_eq(x_3062, x_3063);
if (x_3074 == 0)
{
lean_object* x_3075; lean_object* x_3076; lean_object* x_3077; lean_object* x_3078; lean_object* x_3079; lean_object* x_3080; lean_object* x_3081; lean_object* x_3082; lean_object* x_3083; lean_object* x_3084; lean_object* x_3085; lean_object* x_3086; lean_object* x_3132; lean_object* x_3133; lean_object* x_3134; 
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 lean_ctor_release(x_7, 9);
 lean_ctor_release(x_7, 10);
 lean_ctor_release(x_7, 11);
 lean_ctor_release(x_7, 12);
 x_3075 = x_7;
} else {
 lean_dec_ref(x_7);
 x_3075 = lean_box(0);
}
x_3076 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
x_3077 = lean_ctor_get(x_3076, 1);
lean_inc(x_3077);
lean_dec_ref(x_3076);
x_3132 = lean_unsigned_to_nat(1u);
x_3133 = lean_nat_add(x_3062, x_3132);
lean_dec(x_3062);
if (lean_is_scalar(x_3075)) {
 x_3134 = lean_alloc_ctor(0, 13, 2);
} else {
 x_3134 = x_3075;
}
lean_ctor_set(x_3134, 0, x_3059);
lean_ctor_set(x_3134, 1, x_3060);
lean_ctor_set(x_3134, 2, x_3061);
lean_ctor_set(x_3134, 3, x_3133);
lean_ctor_set(x_3134, 4, x_3063);
lean_ctor_set(x_3134, 5, x_3064);
lean_ctor_set(x_3134, 6, x_3065);
lean_ctor_set(x_3134, 7, x_3066);
lean_ctor_set(x_3134, 8, x_3067);
lean_ctor_set(x_3134, 9, x_3068);
lean_ctor_set(x_3134, 10, x_3069);
lean_ctor_set(x_3134, 11, x_3071);
lean_ctor_set(x_3134, 12, x_3073);
lean_ctor_set_uint8(x_3134, sizeof(void*)*13, x_3070);
lean_ctor_set_uint8(x_3134, sizeof(void*)*13 + 1, x_3072);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3135; lean_object* x_3136; lean_object* x_3137; lean_object* x_3138; lean_object* x_3139; lean_object* x_3140; lean_object* x_3141; lean_object* x_3142; lean_object* x_3143; lean_object* x_3144; uint8_t x_3145; lean_object* x_3146; lean_object* x_3147; lean_object* x_3148; lean_object* x_3149; lean_object* x_3150; lean_object* x_3151; lean_object* x_3152; lean_object* x_3153; lean_object* x_3161; lean_object* x_3162; lean_object* x_3163; lean_object* x_3164; lean_object* x_3165; lean_object* x_3166; lean_object* x_3167; lean_object* x_3168; lean_object* x_3169; uint8_t x_3170; lean_object* x_3316; lean_object* x_3317; lean_object* x_3318; lean_object* x_3319; lean_object* x_3320; lean_object* x_3321; lean_object* x_3322; lean_object* x_3323; lean_object* x_3324; lean_object* x_3325; lean_object* x_3326; lean_object* x_3331; lean_object* x_3332; lean_object* x_3333; lean_object* x_3334; lean_object* x_3335; lean_object* x_3336; lean_object* x_3337; lean_object* x_3338; lean_object* x_3339; lean_object* x_3340; lean_object* x_3341; uint8_t x_3364; 
lean_dec_ref(x_3058);
x_3135 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3135);
x_3136 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3136);
lean_inc_ref(x_3135);
x_3331 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_3074, x_3135, x_3, x_5, x_6, x_3134, x_8, x_3077);
x_3332 = lean_ctor_get(x_3331, 0);
lean_inc(x_3332);
x_3333 = lean_ctor_get(x_3331, 1);
lean_inc(x_3333);
lean_dec_ref(x_3331);
x_3364 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2069_(x_3135, x_3332);
lean_dec_ref(x_3135);
if (x_3364 == 0)
{
goto block_3363;
}
else
{
if (x_3074 == 0)
{
x_3334 = x_2;
x_3335 = x_3;
x_3336 = x_4;
x_3337 = x_5;
x_3338 = x_6;
x_3339 = x_3134;
x_3340 = x_8;
x_3341 = x_3333;
goto block_3360;
}
else
{
goto block_3363;
}
}
block_3160:
{
lean_object* x_3154; lean_object* x_3155; lean_object* x_3156; lean_object* x_3157; lean_object* x_3158; 
x_3154 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_3154, 0, x_3153);
lean_ctor_set(x_3154, 1, x_3142);
lean_ctor_set(x_3154, 2, x_3143);
lean_ctor_set(x_3154, 3, x_3144);
lean_ctor_set(x_3154, 4, x_3146);
lean_ctor_set(x_3154, 5, x_3147);
lean_ctor_set(x_3154, 6, x_3148);
lean_ctor_set_uint8(x_3154, sizeof(void*)*7, x_3145);
x_3155 = lean_st_ref_set(x_3140, x_3154, x_3151);
x_3156 = lean_ctor_get(x_3155, 1);
lean_inc(x_3156);
lean_dec_ref(x_3155);
x_3157 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_3141, x_3140, x_3137, x_3156);
lean_dec_ref(x_3141);
x_3158 = lean_ctor_get(x_3157, 1);
lean_inc(x_3158);
lean_dec_ref(x_3157);
x_1 = x_3136;
x_2 = x_3150;
x_3 = x_3140;
x_4 = x_3152;
x_5 = x_3149;
x_6 = x_3137;
x_7 = x_3139;
x_8 = x_3138;
x_9 = x_3158;
goto _start;
}
block_3315:
{
if (x_3170 == 0)
{
lean_object* x_3171; 
lean_inc(x_3163);
lean_inc_ref(x_3165);
lean_inc(x_3161);
lean_inc_ref(x_3168);
lean_inc_ref(x_3166);
x_3171 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_3166, x_3168, x_3161, x_3165, x_3163, x_3162);
if (lean_obj_tag(x_3171) == 0)
{
lean_object* x_3172; 
x_3172 = lean_ctor_get(x_3171, 0);
lean_inc(x_3172);
if (lean_obj_tag(x_3172) == 0)
{
lean_object* x_3173; lean_object* x_3174; 
x_3173 = lean_ctor_get(x_3171, 1);
lean_inc(x_3173);
lean_dec_ref(x_3171);
lean_inc(x_3163);
lean_inc_ref(x_3165);
lean_inc(x_3161);
lean_inc_ref(x_3168);
lean_inc_ref(x_3166);
x_3174 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_3166, x_3167, x_3164, x_3168, x_3161, x_3165, x_3163, x_3173);
if (lean_obj_tag(x_3174) == 0)
{
lean_object* x_3175; 
x_3175 = lean_ctor_get(x_3174, 0);
lean_inc(x_3175);
if (lean_obj_tag(x_3175) == 0)
{
lean_object* x_3176; lean_object* x_3177; lean_object* x_3178; lean_object* x_3179; lean_object* x_3180; 
x_3176 = lean_ctor_get(x_3174, 1);
lean_inc(x_3176);
lean_dec_ref(x_3174);
x_3177 = lean_ctor_get(x_3166, 0);
lean_inc(x_3177);
x_3178 = lean_ctor_get(x_3166, 3);
lean_inc(x_3178);
lean_inc(x_3178);
x_3179 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_3178, x_3176);
x_3180 = lean_ctor_get(x_3179, 0);
lean_inc(x_3180);
if (lean_obj_tag(x_3180) == 0)
{
lean_object* x_3181; lean_object* x_3182; 
x_3181 = lean_ctor_get(x_3179, 1);
lean_inc(x_3181);
lean_dec_ref(x_3179);
lean_inc(x_3163);
lean_inc_ref(x_3165);
lean_inc(x_3161);
lean_inc_ref(x_3168);
lean_inc_ref(x_3169);
lean_inc(x_3164);
lean_inc_ref(x_3167);
lean_inc_ref(x_3136);
lean_inc_ref(x_3166);
x_3182 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_3166, x_3136, x_3167, x_3164, x_3169, x_3168, x_3161, x_3165, x_3163, x_3181);
if (lean_obj_tag(x_3182) == 0)
{
lean_object* x_3183; 
x_3183 = lean_ctor_get(x_3182, 0);
lean_inc(x_3183);
if (lean_obj_tag(x_3183) == 0)
{
lean_object* x_3184; lean_object* x_3185; 
x_3184 = lean_ctor_get(x_3182, 1);
lean_inc(x_3184);
lean_dec_ref(x_3182);
lean_inc(x_3163);
lean_inc_ref(x_3165);
lean_inc(x_3161);
lean_inc_ref(x_3168);
lean_inc_ref(x_3169);
lean_inc(x_3164);
lean_inc_ref(x_3167);
x_3185 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_3178, x_3167, x_3164, x_3169, x_3168, x_3161, x_3165, x_3163, x_3184);
if (lean_obj_tag(x_3185) == 0)
{
lean_object* x_3186; 
x_3186 = lean_ctor_get(x_3185, 0);
lean_inc(x_3186);
if (lean_obj_tag(x_3186) == 0)
{
lean_object* x_3187; lean_object* x_3188; 
x_3187 = lean_ctor_get(x_3185, 1);
lean_inc(x_3187);
lean_dec_ref(x_3185);
lean_inc(x_3163);
lean_inc_ref(x_3165);
lean_inc(x_3161);
lean_inc_ref(x_3168);
lean_inc_ref(x_3169);
lean_inc(x_3164);
lean_inc_ref(x_3167);
x_3188 = l_Lean_Compiler_LCNF_Simp_simp(x_3136, x_3167, x_3164, x_3169, x_3168, x_3161, x_3165, x_3163, x_3187);
if (lean_obj_tag(x_3188) == 0)
{
lean_object* x_3189; lean_object* x_3190; lean_object* x_3191; lean_object* x_3192; uint8_t x_3193; 
x_3189 = lean_ctor_get(x_3188, 0);
lean_inc(x_3189);
x_3190 = lean_ctor_get(x_3188, 1);
lean_inc(x_3190);
lean_dec_ref(x_3188);
x_3191 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_3177, x_3164, x_3190);
lean_dec(x_3177);
x_3192 = lean_ctor_get(x_3191, 0);
lean_inc(x_3192);
x_3193 = lean_unbox(x_3192);
lean_dec(x_3192);
if (x_3193 == 0)
{
lean_object* x_3194; lean_object* x_3195; lean_object* x_3196; lean_object* x_3197; lean_object* x_3198; 
lean_dec_ref(x_3169);
lean_dec_ref(x_3168);
lean_dec_ref(x_3167);
lean_dec_ref(x_3165);
lean_dec(x_3163);
lean_dec_ref(x_1);
x_3194 = lean_ctor_get(x_3191, 1);
lean_inc(x_3194);
lean_dec_ref(x_3191);
x_3195 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_3166, x_3164, x_3161, x_3194);
lean_dec(x_3161);
lean_dec(x_3164);
lean_dec_ref(x_3166);
x_3196 = lean_ctor_get(x_3195, 1);
lean_inc(x_3196);
if (lean_is_exclusive(x_3195)) {
 lean_ctor_release(x_3195, 0);
 lean_ctor_release(x_3195, 1);
 x_3197 = x_3195;
} else {
 lean_dec_ref(x_3195);
 x_3197 = lean_box(0);
}
if (lean_is_scalar(x_3197)) {
 x_3198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3198 = x_3197;
}
lean_ctor_set(x_3198, 0, x_3189);
lean_ctor_set(x_3198, 1, x_3196);
return x_3198;
}
else
{
lean_object* x_3199; lean_object* x_3200; lean_object* x_3201; lean_object* x_3202; lean_object* x_3203; lean_object* x_3204; 
x_3199 = lean_ctor_get(x_3191, 1);
lean_inc(x_3199);
lean_dec_ref(x_3191);
lean_inc_ref(x_3166);
x_3200 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_3166, x_3167, x_3164, x_3169, x_3168, x_3161, x_3165, x_3163, x_3199);
lean_dec(x_3163);
lean_dec_ref(x_3165);
lean_dec(x_3161);
lean_dec_ref(x_3168);
lean_dec_ref(x_3169);
lean_dec(x_3164);
lean_dec_ref(x_3167);
x_3201 = lean_ctor_get(x_3200, 1);
lean_inc(x_3201);
if (lean_is_exclusive(x_3200)) {
 lean_ctor_release(x_3200, 0);
 lean_ctor_release(x_3200, 1);
 x_3202 = x_3200;
} else {
 lean_dec_ref(x_3200);
 x_3202 = lean_box(0);
}
x_3203 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_3166, x_3189);
lean_dec_ref(x_1);
if (lean_is_scalar(x_3202)) {
 x_3204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3204 = x_3202;
}
lean_ctor_set(x_3204, 0, x_3203);
lean_ctor_set(x_3204, 1, x_3201);
return x_3204;
}
}
else
{
lean_dec(x_3177);
lean_dec_ref(x_3169);
lean_dec_ref(x_3168);
lean_dec_ref(x_3167);
lean_dec_ref(x_3166);
lean_dec_ref(x_3165);
lean_dec(x_3164);
lean_dec(x_3163);
lean_dec(x_3161);
lean_dec_ref(x_1);
return x_3188;
}
}
else
{
lean_object* x_3205; lean_object* x_3206; lean_object* x_3207; lean_object* x_3208; lean_object* x_3209; 
lean_dec_ref(x_1);
x_3205 = lean_ctor_get(x_3186, 0);
lean_inc(x_3205);
lean_dec_ref(x_3186);
x_3206 = lean_ctor_get(x_3185, 1);
lean_inc(x_3206);
lean_dec_ref(x_3185);
x_3207 = lean_ctor_get(x_3205, 0);
lean_inc(x_3207);
x_3208 = lean_ctor_get(x_3205, 1);
lean_inc(x_3208);
lean_dec(x_3205);
x_3209 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3177, x_3208, x_3164, x_3161, x_3165, x_3163, x_3206);
if (lean_obj_tag(x_3209) == 0)
{
lean_object* x_3210; lean_object* x_3211; lean_object* x_3212; lean_object* x_3213; 
x_3210 = lean_ctor_get(x_3209, 1);
lean_inc(x_3210);
lean_dec_ref(x_3209);
x_3211 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_3166, x_3164, x_3161, x_3210);
lean_dec_ref(x_3166);
x_3212 = lean_ctor_get(x_3211, 1);
lean_inc(x_3212);
lean_dec_ref(x_3211);
lean_inc(x_3163);
lean_inc_ref(x_3165);
lean_inc(x_3161);
lean_inc_ref(x_3168);
lean_inc_ref(x_3169);
lean_inc(x_3164);
lean_inc_ref(x_3167);
x_3213 = l_Lean_Compiler_LCNF_Simp_simp(x_3136, x_3167, x_3164, x_3169, x_3168, x_3161, x_3165, x_3163, x_3212);
if (lean_obj_tag(x_3213) == 0)
{
lean_object* x_3214; lean_object* x_3215; lean_object* x_3216; 
x_3214 = lean_ctor_get(x_3213, 0);
lean_inc(x_3214);
x_3215 = lean_ctor_get(x_3213, 1);
lean_inc(x_3215);
lean_dec_ref(x_3213);
x_3216 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_3207, x_3214, x_3167, x_3164, x_3169, x_3168, x_3161, x_3165, x_3163, x_3215);
lean_dec(x_3163);
lean_dec_ref(x_3165);
lean_dec(x_3161);
lean_dec_ref(x_3168);
lean_dec_ref(x_3169);
lean_dec(x_3164);
lean_dec_ref(x_3167);
lean_dec(x_3207);
return x_3216;
}
else
{
lean_dec(x_3207);
lean_dec_ref(x_3169);
lean_dec_ref(x_3168);
lean_dec_ref(x_3167);
lean_dec_ref(x_3165);
lean_dec(x_3164);
lean_dec(x_3163);
lean_dec(x_3161);
return x_3213;
}
}
else
{
lean_object* x_3217; lean_object* x_3218; lean_object* x_3219; lean_object* x_3220; 
lean_dec(x_3207);
lean_dec_ref(x_3169);
lean_dec_ref(x_3168);
lean_dec_ref(x_3167);
lean_dec_ref(x_3166);
lean_dec_ref(x_3165);
lean_dec(x_3164);
lean_dec(x_3163);
lean_dec(x_3161);
lean_dec_ref(x_3136);
x_3217 = lean_ctor_get(x_3209, 0);
lean_inc(x_3217);
x_3218 = lean_ctor_get(x_3209, 1);
lean_inc(x_3218);
if (lean_is_exclusive(x_3209)) {
 lean_ctor_release(x_3209, 0);
 lean_ctor_release(x_3209, 1);
 x_3219 = x_3209;
} else {
 lean_dec_ref(x_3209);
 x_3219 = lean_box(0);
}
if (lean_is_scalar(x_3219)) {
 x_3220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3220 = x_3219;
}
lean_ctor_set(x_3220, 0, x_3217);
lean_ctor_set(x_3220, 1, x_3218);
return x_3220;
}
}
}
else
{
lean_object* x_3221; lean_object* x_3222; lean_object* x_3223; lean_object* x_3224; 
lean_dec(x_3177);
lean_dec_ref(x_3169);
lean_dec_ref(x_3168);
lean_dec_ref(x_3167);
lean_dec_ref(x_3166);
lean_dec_ref(x_3165);
lean_dec(x_3164);
lean_dec(x_3163);
lean_dec(x_3161);
lean_dec_ref(x_3136);
lean_dec_ref(x_1);
x_3221 = lean_ctor_get(x_3185, 0);
lean_inc(x_3221);
x_3222 = lean_ctor_get(x_3185, 1);
lean_inc(x_3222);
if (lean_is_exclusive(x_3185)) {
 lean_ctor_release(x_3185, 0);
 lean_ctor_release(x_3185, 1);
 x_3223 = x_3185;
} else {
 lean_dec_ref(x_3185);
 x_3223 = lean_box(0);
}
if (lean_is_scalar(x_3223)) {
 x_3224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3224 = x_3223;
}
lean_ctor_set(x_3224, 0, x_3221);
lean_ctor_set(x_3224, 1, x_3222);
return x_3224;
}
}
else
{
lean_object* x_3225; lean_object* x_3226; lean_object* x_3227; lean_object* x_3228; lean_object* x_3229; lean_object* x_3230; 
lean_dec(x_3178);
lean_dec(x_3177);
lean_dec_ref(x_3169);
lean_dec_ref(x_3168);
lean_dec_ref(x_3167);
lean_dec_ref(x_3165);
lean_dec(x_3163);
lean_dec_ref(x_3136);
lean_dec_ref(x_1);
x_3225 = lean_ctor_get(x_3182, 1);
lean_inc(x_3225);
lean_dec_ref(x_3182);
x_3226 = lean_ctor_get(x_3183, 0);
lean_inc(x_3226);
lean_dec_ref(x_3183);
x_3227 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_3166, x_3164, x_3161, x_3225);
lean_dec(x_3161);
lean_dec(x_3164);
lean_dec_ref(x_3166);
x_3228 = lean_ctor_get(x_3227, 1);
lean_inc(x_3228);
if (lean_is_exclusive(x_3227)) {
 lean_ctor_release(x_3227, 0);
 lean_ctor_release(x_3227, 1);
 x_3229 = x_3227;
} else {
 lean_dec_ref(x_3227);
 x_3229 = lean_box(0);
}
if (lean_is_scalar(x_3229)) {
 x_3230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3230 = x_3229;
}
lean_ctor_set(x_3230, 0, x_3226);
lean_ctor_set(x_3230, 1, x_3228);
return x_3230;
}
}
else
{
lean_object* x_3231; lean_object* x_3232; lean_object* x_3233; lean_object* x_3234; 
lean_dec(x_3178);
lean_dec(x_3177);
lean_dec_ref(x_3169);
lean_dec_ref(x_3168);
lean_dec_ref(x_3167);
lean_dec_ref(x_3166);
lean_dec_ref(x_3165);
lean_dec(x_3164);
lean_dec(x_3163);
lean_dec(x_3161);
lean_dec_ref(x_3136);
lean_dec_ref(x_1);
x_3231 = lean_ctor_get(x_3182, 0);
lean_inc(x_3231);
x_3232 = lean_ctor_get(x_3182, 1);
lean_inc(x_3232);
if (lean_is_exclusive(x_3182)) {
 lean_ctor_release(x_3182, 0);
 lean_ctor_release(x_3182, 1);
 x_3233 = x_3182;
} else {
 lean_dec_ref(x_3182);
 x_3233 = lean_box(0);
}
if (lean_is_scalar(x_3233)) {
 x_3234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3234 = x_3233;
}
lean_ctor_set(x_3234, 0, x_3231);
lean_ctor_set(x_3234, 1, x_3232);
return x_3234;
}
}
else
{
lean_object* x_3235; lean_object* x_3236; lean_object* x_3237; 
lean_dec(x_3178);
lean_dec_ref(x_1);
x_3235 = lean_ctor_get(x_3179, 1);
lean_inc(x_3235);
lean_dec_ref(x_3179);
x_3236 = lean_ctor_get(x_3180, 0);
lean_inc(x_3236);
lean_dec_ref(x_3180);
x_3237 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3177, x_3236, x_3164, x_3161, x_3165, x_3163, x_3235);
if (lean_obj_tag(x_3237) == 0)
{
lean_object* x_3238; lean_object* x_3239; lean_object* x_3240; 
x_3238 = lean_ctor_get(x_3237, 1);
lean_inc(x_3238);
lean_dec_ref(x_3237);
x_3239 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_3166, x_3164, x_3161, x_3238);
lean_dec_ref(x_3166);
x_3240 = lean_ctor_get(x_3239, 1);
lean_inc(x_3240);
lean_dec_ref(x_3239);
x_1 = x_3136;
x_2 = x_3167;
x_3 = x_3164;
x_4 = x_3169;
x_5 = x_3168;
x_6 = x_3161;
x_7 = x_3165;
x_8 = x_3163;
x_9 = x_3240;
goto _start;
}
else
{
lean_object* x_3242; lean_object* x_3243; lean_object* x_3244; lean_object* x_3245; 
lean_dec_ref(x_3169);
lean_dec_ref(x_3168);
lean_dec_ref(x_3167);
lean_dec_ref(x_3166);
lean_dec_ref(x_3165);
lean_dec(x_3164);
lean_dec(x_3163);
lean_dec(x_3161);
lean_dec_ref(x_3136);
x_3242 = lean_ctor_get(x_3237, 0);
lean_inc(x_3242);
x_3243 = lean_ctor_get(x_3237, 1);
lean_inc(x_3243);
if (lean_is_exclusive(x_3237)) {
 lean_ctor_release(x_3237, 0);
 lean_ctor_release(x_3237, 1);
 x_3244 = x_3237;
} else {
 lean_dec_ref(x_3237);
 x_3244 = lean_box(0);
}
if (lean_is_scalar(x_3244)) {
 x_3245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3245 = x_3244;
}
lean_ctor_set(x_3245, 0, x_3242);
lean_ctor_set(x_3245, 1, x_3243);
return x_3245;
}
}
}
else
{
lean_object* x_3246; lean_object* x_3247; lean_object* x_3248; lean_object* x_3249; 
lean_dec_ref(x_3166);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_3246 = x_1;
} else {
 lean_dec_ref(x_1);
 x_3246 = lean_box(0);
}
x_3247 = lean_ctor_get(x_3174, 1);
lean_inc(x_3247);
lean_dec_ref(x_3174);
x_3248 = lean_ctor_get(x_3175, 0);
lean_inc(x_3248);
lean_dec_ref(x_3175);
if (lean_is_scalar(x_3246)) {
 x_3249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3249 = x_3246;
 lean_ctor_set_tag(x_3249, 1);
}
lean_ctor_set(x_3249, 0, x_3248);
lean_ctor_set(x_3249, 1, x_3136);
x_1 = x_3249;
x_2 = x_3167;
x_3 = x_3164;
x_4 = x_3169;
x_5 = x_3168;
x_6 = x_3161;
x_7 = x_3165;
x_8 = x_3163;
x_9 = x_3247;
goto _start;
}
}
else
{
lean_object* x_3251; lean_object* x_3252; lean_object* x_3253; lean_object* x_3254; 
lean_dec_ref(x_3169);
lean_dec_ref(x_3168);
lean_dec_ref(x_3167);
lean_dec_ref(x_3166);
lean_dec_ref(x_3165);
lean_dec(x_3164);
lean_dec(x_3163);
lean_dec(x_3161);
lean_dec_ref(x_3136);
lean_dec_ref(x_1);
x_3251 = lean_ctor_get(x_3174, 0);
lean_inc(x_3251);
x_3252 = lean_ctor_get(x_3174, 1);
lean_inc(x_3252);
if (lean_is_exclusive(x_3174)) {
 lean_ctor_release(x_3174, 0);
 lean_ctor_release(x_3174, 1);
 x_3253 = x_3174;
} else {
 lean_dec_ref(x_3174);
 x_3253 = lean_box(0);
}
if (lean_is_scalar(x_3253)) {
 x_3254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3254 = x_3253;
}
lean_ctor_set(x_3254, 0, x_3251);
lean_ctor_set(x_3254, 1, x_3252);
return x_3254;
}
}
else
{
lean_object* x_3255; lean_object* x_3256; lean_object* x_3257; lean_object* x_3258; lean_object* x_3259; 
lean_dec_ref(x_3166);
lean_dec_ref(x_1);
x_3255 = lean_ctor_get(x_3171, 1);
lean_inc(x_3255);
lean_dec_ref(x_3171);
x_3256 = lean_ctor_get(x_3172, 0);
lean_inc(x_3256);
lean_dec_ref(x_3172);
x_3257 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3164, x_3255);
x_3258 = lean_ctor_get(x_3257, 1);
lean_inc(x_3258);
lean_dec_ref(x_3257);
lean_inc(x_3163);
lean_inc_ref(x_3165);
lean_inc(x_3161);
lean_inc_ref(x_3168);
lean_inc_ref(x_3169);
lean_inc(x_3164);
lean_inc_ref(x_3167);
x_3259 = l_Lean_Compiler_LCNF_Simp_simp(x_3136, x_3167, x_3164, x_3169, x_3168, x_3161, x_3165, x_3163, x_3258);
if (lean_obj_tag(x_3259) == 0)
{
lean_object* x_3260; lean_object* x_3261; lean_object* x_3262; 
x_3260 = lean_ctor_get(x_3259, 0);
lean_inc(x_3260);
x_3261 = lean_ctor_get(x_3259, 1);
lean_inc(x_3261);
lean_dec_ref(x_3259);
x_3262 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_3256, x_3260, x_3167, x_3164, x_3169, x_3168, x_3161, x_3165, x_3163, x_3261);
lean_dec(x_3163);
lean_dec_ref(x_3165);
lean_dec(x_3161);
lean_dec_ref(x_3168);
lean_dec_ref(x_3169);
lean_dec(x_3164);
lean_dec_ref(x_3167);
lean_dec(x_3256);
return x_3262;
}
else
{
lean_dec(x_3256);
lean_dec_ref(x_3169);
lean_dec_ref(x_3168);
lean_dec_ref(x_3167);
lean_dec_ref(x_3165);
lean_dec(x_3164);
lean_dec(x_3163);
lean_dec(x_3161);
return x_3259;
}
}
}
else
{
lean_object* x_3263; lean_object* x_3264; lean_object* x_3265; lean_object* x_3266; 
lean_dec_ref(x_3169);
lean_dec_ref(x_3168);
lean_dec_ref(x_3167);
lean_dec_ref(x_3166);
lean_dec_ref(x_3165);
lean_dec(x_3164);
lean_dec(x_3163);
lean_dec(x_3161);
lean_dec_ref(x_3136);
lean_dec_ref(x_1);
x_3263 = lean_ctor_get(x_3171, 0);
lean_inc(x_3263);
x_3264 = lean_ctor_get(x_3171, 1);
lean_inc(x_3264);
if (lean_is_exclusive(x_3171)) {
 lean_ctor_release(x_3171, 0);
 lean_ctor_release(x_3171, 1);
 x_3265 = x_3171;
} else {
 lean_dec_ref(x_3171);
 x_3265 = lean_box(0);
}
if (lean_is_scalar(x_3265)) {
 x_3266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3266 = x_3265;
}
lean_ctor_set(x_3266, 0, x_3263);
lean_ctor_set(x_3266, 1, x_3264);
return x_3266;
}
}
else
{
lean_object* x_3267; lean_object* x_3268; lean_object* x_3269; lean_object* x_3270; lean_object* x_3271; lean_object* x_3272; lean_object* x_3273; uint8_t x_3274; lean_object* x_3275; lean_object* x_3276; lean_object* x_3277; lean_object* x_3278; lean_object* x_3279; lean_object* x_3280; lean_object* x_3281; lean_object* x_3282; lean_object* x_3283; uint64_t x_3284; uint64_t x_3285; uint64_t x_3286; uint64_t x_3287; uint64_t x_3288; uint64_t x_3289; uint64_t x_3290; size_t x_3291; size_t x_3292; size_t x_3293; size_t x_3294; size_t x_3295; lean_object* x_3296; uint8_t x_3297; 
lean_dec_ref(x_1);
x_3267 = lean_st_ref_take(x_3164, x_3162);
x_3268 = lean_ctor_get(x_3267, 0);
lean_inc(x_3268);
x_3269 = lean_ctor_get(x_3268, 0);
lean_inc_ref(x_3269);
x_3270 = lean_ctor_get(x_3267, 1);
lean_inc(x_3270);
lean_dec_ref(x_3267);
x_3271 = lean_ctor_get(x_3268, 1);
lean_inc_ref(x_3271);
x_3272 = lean_ctor_get(x_3268, 2);
lean_inc(x_3272);
x_3273 = lean_ctor_get(x_3268, 3);
lean_inc_ref(x_3273);
x_3274 = lean_ctor_get_uint8(x_3268, sizeof(void*)*7);
x_3275 = lean_ctor_get(x_3268, 4);
lean_inc(x_3275);
x_3276 = lean_ctor_get(x_3268, 5);
lean_inc(x_3276);
x_3277 = lean_ctor_get(x_3268, 6);
lean_inc(x_3277);
lean_dec(x_3268);
x_3278 = lean_ctor_get(x_3269, 0);
lean_inc(x_3278);
x_3279 = lean_ctor_get(x_3269, 1);
lean_inc_ref(x_3279);
if (lean_is_exclusive(x_3269)) {
 lean_ctor_release(x_3269, 0);
 lean_ctor_release(x_3269, 1);
 x_3280 = x_3269;
} else {
 lean_dec_ref(x_3269);
 x_3280 = lean_box(0);
}
x_3281 = lean_ctor_get(x_3166, 0);
lean_inc(x_3281);
x_3282 = lean_box(0);
x_3283 = lean_array_get_size(x_3279);
x_3284 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_3281);
x_3285 = 32;
x_3286 = lean_uint64_shift_right(x_3284, x_3285);
x_3287 = lean_uint64_xor(x_3284, x_3286);
x_3288 = 16;
x_3289 = lean_uint64_shift_right(x_3287, x_3288);
x_3290 = lean_uint64_xor(x_3287, x_3289);
x_3291 = lean_uint64_to_usize(x_3290);
x_3292 = lean_usize_of_nat(x_3283);
lean_dec(x_3283);
x_3293 = 1;
x_3294 = lean_usize_sub(x_3292, x_3293);
x_3295 = lean_usize_land(x_3291, x_3294);
x_3296 = lean_array_uget(x_3279, x_3295);
x_3297 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_3281, x_3296);
if (x_3297 == 0)
{
lean_object* x_3298; lean_object* x_3299; lean_object* x_3300; lean_object* x_3301; lean_object* x_3302; lean_object* x_3303; lean_object* x_3304; lean_object* x_3305; uint8_t x_3306; 
x_3298 = lean_nat_add(x_3278, x_3132);
lean_dec(x_3278);
x_3299 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3299, 0, x_3281);
lean_ctor_set(x_3299, 1, x_3282);
lean_ctor_set(x_3299, 2, x_3296);
x_3300 = lean_array_uset(x_3279, x_3295, x_3299);
x_3301 = lean_unsigned_to_nat(4u);
x_3302 = lean_nat_mul(x_3298, x_3301);
x_3303 = lean_unsigned_to_nat(3u);
x_3304 = lean_nat_div(x_3302, x_3303);
lean_dec(x_3302);
x_3305 = lean_array_get_size(x_3300);
x_3306 = lean_nat_dec_le(x_3304, x_3305);
lean_dec(x_3305);
lean_dec(x_3304);
if (x_3306 == 0)
{
lean_object* x_3307; lean_object* x_3308; 
x_3307 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_3300);
if (lean_is_scalar(x_3280)) {
 x_3308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3308 = x_3280;
}
lean_ctor_set(x_3308, 0, x_3298);
lean_ctor_set(x_3308, 1, x_3307);
x_3137 = x_3161;
x_3138 = x_3163;
x_3139 = x_3165;
x_3140 = x_3164;
x_3141 = x_3166;
x_3142 = x_3271;
x_3143 = x_3272;
x_3144 = x_3273;
x_3145 = x_3274;
x_3146 = x_3275;
x_3147 = x_3276;
x_3148 = x_3277;
x_3149 = x_3168;
x_3150 = x_3167;
x_3151 = x_3270;
x_3152 = x_3169;
x_3153 = x_3308;
goto block_3160;
}
else
{
lean_object* x_3309; 
if (lean_is_scalar(x_3280)) {
 x_3309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3309 = x_3280;
}
lean_ctor_set(x_3309, 0, x_3298);
lean_ctor_set(x_3309, 1, x_3300);
x_3137 = x_3161;
x_3138 = x_3163;
x_3139 = x_3165;
x_3140 = x_3164;
x_3141 = x_3166;
x_3142 = x_3271;
x_3143 = x_3272;
x_3144 = x_3273;
x_3145 = x_3274;
x_3146 = x_3275;
x_3147 = x_3276;
x_3148 = x_3277;
x_3149 = x_3168;
x_3150 = x_3167;
x_3151 = x_3270;
x_3152 = x_3169;
x_3153 = x_3309;
goto block_3160;
}
}
else
{
lean_object* x_3310; lean_object* x_3311; lean_object* x_3312; lean_object* x_3313; lean_object* x_3314; 
x_3310 = lean_box(0);
x_3311 = lean_array_uset(x_3279, x_3295, x_3310);
x_3312 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_3281, x_3282, x_3296);
x_3313 = lean_array_uset(x_3311, x_3295, x_3312);
if (lean_is_scalar(x_3280)) {
 x_3314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3314 = x_3280;
}
lean_ctor_set(x_3314, 0, x_3278);
lean_ctor_set(x_3314, 1, x_3313);
x_3137 = x_3161;
x_3138 = x_3163;
x_3139 = x_3165;
x_3140 = x_3164;
x_3141 = x_3166;
x_3142 = x_3271;
x_3143 = x_3272;
x_3144 = x_3273;
x_3145 = x_3274;
x_3146 = x_3275;
x_3147 = x_3276;
x_3148 = x_3277;
x_3149 = x_3168;
x_3150 = x_3167;
x_3151 = x_3270;
x_3152 = x_3169;
x_3153 = x_3314;
goto block_3160;
}
}
}
block_3330:
{
uint8_t x_3327; 
x_3327 = l_Lean_Expr_isErased(x_3317);
lean_dec_ref(x_3317);
if (x_3327 == 0)
{
lean_dec(x_3318);
x_3161 = x_3323;
x_3162 = x_3326;
x_3163 = x_3325;
x_3164 = x_3320;
x_3165 = x_3324;
x_3166 = x_3316;
x_3167 = x_3319;
x_3168 = x_3322;
x_3169 = x_3321;
x_3170 = x_3074;
goto block_3315;
}
else
{
lean_object* x_3328; uint8_t x_3329; 
x_3328 = lean_box(1);
x_3329 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1209_(x_3318, x_3328);
lean_dec(x_3318);
if (x_3329 == 0)
{
x_3161 = x_3323;
x_3162 = x_3326;
x_3163 = x_3325;
x_3164 = x_3320;
x_3165 = x_3324;
x_3166 = x_3316;
x_3167 = x_3319;
x_3168 = x_3322;
x_3169 = x_3321;
x_3170 = x_3327;
goto block_3315;
}
else
{
x_3161 = x_3323;
x_3162 = x_3326;
x_3163 = x_3325;
x_3164 = x_3320;
x_3165 = x_3324;
x_3166 = x_3316;
x_3167 = x_3319;
x_3168 = x_3322;
x_3169 = x_3321;
x_3170 = x_3074;
goto block_3315;
}
}
}
block_3360:
{
lean_object* x_3342; lean_object* x_3343; lean_object* x_3344; 
x_3342 = lean_ctor_get(x_3332, 2);
lean_inc_ref(x_3342);
x_3343 = lean_ctor_get(x_3332, 3);
lean_inc(x_3343);
lean_inc(x_3340);
lean_inc_ref(x_3339);
lean_inc(x_3338);
lean_inc_ref(x_3337);
lean_inc_ref(x_3336);
lean_inc(x_3343);
x_3344 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_3343, x_3334, x_3336, x_3337, x_3338, x_3339, x_3340, x_3341);
if (lean_obj_tag(x_3344) == 0)
{
lean_object* x_3345; 
x_3345 = lean_ctor_get(x_3344, 0);
lean_inc(x_3345);
if (lean_obj_tag(x_3345) == 0)
{
lean_object* x_3346; 
x_3346 = lean_ctor_get(x_3344, 1);
lean_inc(x_3346);
lean_dec_ref(x_3344);
x_3316 = x_3332;
x_3317 = x_3342;
x_3318 = x_3343;
x_3319 = x_3334;
x_3320 = x_3335;
x_3321 = x_3336;
x_3322 = x_3337;
x_3323 = x_3338;
x_3324 = x_3339;
x_3325 = x_3340;
x_3326 = x_3346;
goto block_3330;
}
else
{
lean_object* x_3347; lean_object* x_3348; lean_object* x_3349; lean_object* x_3350; lean_object* x_3351; lean_object* x_3352; lean_object* x_3353; lean_object* x_3354; lean_object* x_3355; 
lean_dec(x_3343);
lean_dec_ref(x_3342);
x_3347 = lean_ctor_get(x_3344, 1);
lean_inc(x_3347);
lean_dec_ref(x_3344);
x_3348 = lean_ctor_get(x_3345, 0);
lean_inc(x_3348);
lean_dec_ref(x_3345);
x_3349 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3335, x_3347);
x_3350 = lean_ctor_get(x_3349, 1);
lean_inc(x_3350);
lean_dec_ref(x_3349);
x_3351 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_3332, x_3348, x_3338, x_3350);
x_3352 = lean_ctor_get(x_3351, 0);
lean_inc(x_3352);
x_3353 = lean_ctor_get(x_3351, 1);
lean_inc(x_3353);
lean_dec_ref(x_3351);
x_3354 = lean_ctor_get(x_3352, 2);
lean_inc_ref(x_3354);
x_3355 = lean_ctor_get(x_3352, 3);
lean_inc(x_3355);
x_3316 = x_3352;
x_3317 = x_3354;
x_3318 = x_3355;
x_3319 = x_3334;
x_3320 = x_3335;
x_3321 = x_3336;
x_3322 = x_3337;
x_3323 = x_3338;
x_3324 = x_3339;
x_3325 = x_3340;
x_3326 = x_3353;
goto block_3330;
}
}
else
{
lean_object* x_3356; lean_object* x_3357; lean_object* x_3358; lean_object* x_3359; 
lean_dec(x_3343);
lean_dec_ref(x_3342);
lean_dec(x_3340);
lean_dec_ref(x_3339);
lean_dec(x_3338);
lean_dec_ref(x_3337);
lean_dec_ref(x_3336);
lean_dec(x_3335);
lean_dec_ref(x_3334);
lean_dec(x_3332);
lean_dec_ref(x_3136);
lean_dec_ref(x_1);
x_3356 = lean_ctor_get(x_3344, 0);
lean_inc(x_3356);
x_3357 = lean_ctor_get(x_3344, 1);
lean_inc(x_3357);
if (lean_is_exclusive(x_3344)) {
 lean_ctor_release(x_3344, 0);
 lean_ctor_release(x_3344, 1);
 x_3358 = x_3344;
} else {
 lean_dec_ref(x_3344);
 x_3358 = lean_box(0);
}
if (lean_is_scalar(x_3358)) {
 x_3359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3359 = x_3358;
}
lean_ctor_set(x_3359, 0, x_3356);
lean_ctor_set(x_3359, 1, x_3357);
return x_3359;
}
}
block_3363:
{
lean_object* x_3361; lean_object* x_3362; 
x_3361 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_3333);
x_3362 = lean_ctor_get(x_3361, 1);
lean_inc(x_3362);
lean_dec_ref(x_3361);
x_3334 = x_2;
x_3335 = x_3;
x_3336 = x_4;
x_3337 = x_5;
x_3338 = x_6;
x_3339 = x_3134;
x_3340 = x_8;
x_3341 = x_3362;
goto block_3360;
}
}
case 3:
{
lean_object* x_3365; lean_object* x_3366; lean_object* x_3367; lean_object* x_3368; lean_object* x_3369; lean_object* x_3370; lean_object* x_3371; 
lean_dec_ref(x_3058);
x_3365 = lean_ctor_get(x_1, 0);
lean_inc(x_3365);
x_3366 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3366);
x_3367 = lean_st_ref_get(x_3, x_3077);
x_3368 = lean_ctor_get(x_3367, 0);
lean_inc(x_3368);
x_3369 = lean_ctor_get(x_3367, 1);
lean_inc(x_3369);
lean_dec_ref(x_3367);
x_3370 = lean_ctor_get(x_3368, 0);
lean_inc_ref(x_3370);
lean_dec(x_3368);
x_3371 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_3370, x_3365, x_3074);
lean_dec_ref(x_3370);
if (lean_obj_tag(x_3371) == 0)
{
lean_object* x_3372; lean_object* x_3373; lean_object* x_3374; lean_object* x_3375; lean_object* x_3376; lean_object* x_3377; lean_object* x_3381; 
x_3372 = lean_ctor_get(x_3371, 0);
lean_inc(x_3372);
lean_dec_ref(x_3371);
x_3373 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_3074, x_3366, x_3, x_3369);
x_3374 = lean_ctor_get(x_3373, 0);
lean_inc(x_3374);
x_3375 = lean_ctor_get(x_3373, 1);
lean_inc(x_3375);
if (lean_is_exclusive(x_3373)) {
 lean_ctor_release(x_3373, 0);
 lean_ctor_release(x_3373, 1);
 x_3376 = x_3373;
} else {
 lean_dec_ref(x_3373);
 x_3376 = lean_box(0);
}
lean_inc(x_3374);
x_3381 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_3372, x_3374, x_2, x_3, x_4, x_5, x_6, x_3134, x_8, x_3375);
if (lean_obj_tag(x_3381) == 0)
{
lean_object* x_3382; 
x_3382 = lean_ctor_get(x_3381, 0);
lean_inc(x_3382);
if (lean_obj_tag(x_3382) == 0)
{
lean_object* x_3383; lean_object* x_3384; lean_object* x_3385; lean_object* x_3386; lean_object* x_3387; uint8_t x_3388; 
lean_dec_ref(x_3134);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_3383 = lean_ctor_get(x_3381, 1);
lean_inc(x_3383);
lean_dec_ref(x_3381);
lean_inc(x_3372);
x_3384 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_3372, x_3, x_3383);
x_3385 = lean_ctor_get(x_3384, 1);
lean_inc(x_3385);
lean_dec_ref(x_3384);
x_3386 = lean_unsigned_to_nat(0u);
x_3387 = lean_array_get_size(x_3374);
x_3388 = lean_nat_dec_lt(x_3386, x_3387);
if (x_3388 == 0)
{
lean_dec(x_3387);
lean_dec(x_3);
x_3377 = x_3385;
goto block_3380;
}
else
{
uint8_t x_3389; 
x_3389 = lean_nat_dec_le(x_3387, x_3387);
if (x_3389 == 0)
{
lean_dec(x_3387);
lean_dec(x_3);
x_3377 = x_3385;
goto block_3380;
}
else
{
lean_object* x_3390; size_t x_3391; size_t x_3392; lean_object* x_3393; lean_object* x_3394; 
x_3390 = lean_box(0);
x_3391 = 0;
x_3392 = lean_usize_of_nat(x_3387);
lean_dec(x_3387);
x_3393 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_3374, x_3391, x_3392, x_3390, x_3, x_3385);
lean_dec(x_3);
x_3394 = lean_ctor_get(x_3393, 1);
lean_inc(x_3394);
lean_dec_ref(x_3393);
x_3377 = x_3394;
goto block_3380;
}
}
}
else
{
lean_object* x_3395; lean_object* x_3396; 
lean_dec(x_3376);
lean_dec(x_3374);
lean_dec(x_3372);
lean_dec_ref(x_1);
x_3395 = lean_ctor_get(x_3381, 1);
lean_inc(x_3395);
lean_dec_ref(x_3381);
x_3396 = lean_ctor_get(x_3382, 0);
lean_inc(x_3396);
lean_dec_ref(x_3382);
x_1 = x_3396;
x_7 = x_3134;
x_9 = x_3395;
goto _start;
}
}
else
{
lean_object* x_3398; lean_object* x_3399; lean_object* x_3400; lean_object* x_3401; 
lean_dec(x_3376);
lean_dec(x_3374);
lean_dec(x_3372);
lean_dec_ref(x_3134);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3398 = lean_ctor_get(x_3381, 0);
lean_inc(x_3398);
x_3399 = lean_ctor_get(x_3381, 1);
lean_inc(x_3399);
if (lean_is_exclusive(x_3381)) {
 lean_ctor_release(x_3381, 0);
 lean_ctor_release(x_3381, 1);
 x_3400 = x_3381;
} else {
 lean_dec_ref(x_3381);
 x_3400 = lean_box(0);
}
if (lean_is_scalar(x_3400)) {
 x_3401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3401 = x_3400;
}
lean_ctor_set(x_3401, 0, x_3398);
lean_ctor_set(x_3401, 1, x_3399);
return x_3401;
}
block_3380:
{
lean_object* x_3378; lean_object* x_3379; 
x_3378 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_1, x_3372, x_3374);
lean_dec_ref(x_1);
if (lean_is_scalar(x_3376)) {
 x_3379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3379 = x_3376;
}
lean_ctor_set(x_3379, 0, x_3378);
lean_ctor_set(x_3379, 1, x_3377);
return x_3379;
}
}
else
{
lean_object* x_3402; 
lean_dec_ref(x_3366);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3402 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_3134, x_8, x_3369);
lean_dec(x_8);
lean_dec_ref(x_3134);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_3402;
}
}
case 4:
{
lean_object* x_3403; lean_object* x_3404; 
x_3403 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3403);
lean_inc(x_8);
lean_inc_ref(x_3134);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_3403);
x_3404 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_3403, x_2, x_3, x_4, x_5, x_6, x_3134, x_8, x_3077);
if (lean_obj_tag(x_3404) == 0)
{
lean_object* x_3405; 
x_3405 = lean_ctor_get(x_3404, 0);
lean_inc(x_3405);
if (lean_obj_tag(x_3405) == 0)
{
lean_object* x_3406; lean_object* x_3407; lean_object* x_3408; lean_object* x_3409; lean_object* x_3410; lean_object* x_3411; lean_object* x_3412; lean_object* x_3413; lean_object* x_3414; 
x_3406 = lean_ctor_get(x_3404, 1);
lean_inc(x_3406);
lean_dec_ref(x_3404);
x_3407 = lean_st_ref_get(x_3, x_3406);
x_3408 = lean_ctor_get(x_3407, 0);
lean_inc(x_3408);
x_3409 = lean_ctor_get(x_3407, 1);
lean_inc(x_3409);
lean_dec_ref(x_3407);
x_3410 = lean_ctor_get(x_3403, 1);
lean_inc_ref(x_3410);
x_3411 = lean_ctor_get(x_3403, 2);
lean_inc(x_3411);
x_3412 = lean_ctor_get(x_3403, 3);
lean_inc_ref(x_3412);
lean_dec_ref(x_3403);
x_3413 = lean_ctor_get(x_3408, 0);
lean_inc_ref(x_3413);
lean_dec(x_3408);
x_3414 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_3413, x_3411, x_3074);
lean_dec_ref(x_3413);
if (lean_obj_tag(x_3414) == 0)
{
lean_object* x_3415; lean_object* x_3416; lean_object* x_3417; lean_object* x_3418; lean_object* x_3419; lean_object* x_3420; lean_object* x_3421; lean_object* x_3422; 
x_3415 = lean_ctor_get(x_3414, 0);
lean_inc(x_3415);
lean_dec_ref(x_3414);
x_3416 = lean_st_ref_get(x_3, x_3409);
x_3417 = lean_ctor_get(x_3416, 0);
lean_inc(x_3417);
x_3418 = lean_ctor_get(x_3416, 1);
lean_inc(x_3418);
lean_dec_ref(x_3416);
x_3419 = lean_box(x_3074);
lean_inc(x_3415);
x_3420 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__1___boxed), 11, 2);
lean_closure_set(x_3420, 0, x_3415);
lean_closure_set(x_3420, 1, x_3419);
x_3421 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_3058, x_3412, x_3420);
lean_inc(x_8);
lean_inc_ref(x_3134);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_3422 = lean_apply_8(x_3421, x_2, x_3, x_4, x_5, x_6, x_3134, x_8, x_3418);
if (lean_obj_tag(x_3422) == 0)
{
lean_object* x_3423; lean_object* x_3424; lean_object* x_3425; 
x_3423 = lean_ctor_get(x_3422, 0);
lean_inc(x_3423);
x_3424 = lean_ctor_get(x_3422, 1);
lean_inc(x_3424);
lean_dec_ref(x_3422);
lean_inc(x_6);
lean_inc(x_3);
x_3425 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_3423, x_2, x_3, x_4, x_5, x_6, x_3134, x_8, x_3424);
if (lean_obj_tag(x_3425) == 0)
{
lean_object* x_3426; lean_object* x_3427; lean_object* x_3428; lean_object* x_3429; lean_object* x_3430; lean_object* x_3431; lean_object* x_3432; lean_object* x_3439; uint8_t x_3440; 
x_3426 = lean_ctor_get(x_3425, 0);
lean_inc(x_3426);
x_3427 = lean_ctor_get(x_3425, 1);
lean_inc(x_3427);
if (lean_is_exclusive(x_3425)) {
 lean_ctor_release(x_3425, 0);
 lean_ctor_release(x_3425, 1);
 x_3428 = x_3425;
} else {
 lean_dec_ref(x_3425);
 x_3428 = lean_box(0);
}
x_3429 = lean_ctor_get(x_3417, 0);
lean_inc_ref(x_3429);
lean_dec(x_3417);
x_3430 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_3429, x_3074, x_3410);
lean_dec_ref(x_3429);
x_3439 = lean_array_get_size(x_3426);
x_3440 = lean_nat_dec_eq(x_3439, x_3132);
lean_dec(x_3439);
if (x_3440 == 0)
{
lean_dec(x_3428);
lean_dec(x_6);
x_3431 = x_3;
x_3432 = x_3427;
goto block_3438;
}
else
{
lean_object* x_3441; lean_object* x_3442; 
x_3441 = lean_unsigned_to_nat(0u);
x_3442 = lean_array_fget(x_3426, x_3441);
if (lean_obj_tag(x_3442) == 0)
{
lean_object* x_3443; lean_object* x_3444; lean_object* x_3445; lean_object* x_3451; lean_object* x_3452; uint8_t x_3461; lean_object* x_3462; uint8_t x_3464; 
lean_dec(x_3428);
x_3443 = lean_ctor_get(x_3442, 1);
lean_inc_ref(x_3443);
x_3444 = lean_ctor_get(x_3442, 2);
lean_inc_ref(x_3444);
lean_dec_ref(x_3442);
x_3451 = lean_array_get_size(x_3443);
x_3464 = lean_nat_dec_lt(x_3441, x_3451);
if (x_3464 == 0)
{
x_3461 = x_3074;
x_3462 = x_3427;
goto block_3463;
}
else
{
if (x_3464 == 0)
{
x_3461 = x_3074;
x_3462 = x_3427;
goto block_3463;
}
else
{
size_t x_3465; size_t x_3466; lean_object* x_3467; lean_object* x_3468; lean_object* x_3469; uint8_t x_3470; 
x_3465 = 0;
x_3466 = lean_usize_of_nat(x_3451);
x_3467 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_3443, x_3465, x_3466, x_3, x_3427);
x_3468 = lean_ctor_get(x_3467, 0);
lean_inc(x_3468);
x_3469 = lean_ctor_get(x_3467, 1);
lean_inc(x_3469);
lean_dec_ref(x_3467);
x_3470 = lean_unbox(x_3468);
lean_dec(x_3468);
x_3461 = x_3470;
x_3462 = x_3469;
goto block_3463;
}
}
block_3450:
{
lean_object* x_3446; lean_object* x_3447; lean_object* x_3448; lean_object* x_3449; 
x_3446 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_3445);
lean_dec(x_3);
x_3447 = lean_ctor_get(x_3446, 1);
lean_inc(x_3447);
if (lean_is_exclusive(x_3446)) {
 lean_ctor_release(x_3446, 0);
 lean_ctor_release(x_3446, 1);
 x_3448 = x_3446;
} else {
 lean_dec_ref(x_3446);
 x_3448 = lean_box(0);
}
if (lean_is_scalar(x_3448)) {
 x_3449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3449 = x_3448;
}
lean_ctor_set(x_3449, 0, x_3444);
lean_ctor_set(x_3449, 1, x_3447);
return x_3449;
}
block_3460:
{
uint8_t x_3453; 
x_3453 = lean_nat_dec_lt(x_3441, x_3451);
if (x_3453 == 0)
{
lean_dec(x_3451);
lean_dec_ref(x_3443);
lean_dec(x_6);
x_3445 = x_3452;
goto block_3450;
}
else
{
uint8_t x_3454; 
x_3454 = lean_nat_dec_le(x_3451, x_3451);
if (x_3454 == 0)
{
lean_dec(x_3451);
lean_dec_ref(x_3443);
lean_dec(x_6);
x_3445 = x_3452;
goto block_3450;
}
else
{
lean_object* x_3455; size_t x_3456; size_t x_3457; lean_object* x_3458; lean_object* x_3459; 
x_3455 = lean_box(0);
x_3456 = 0;
x_3457 = lean_usize_of_nat(x_3451);
lean_dec(x_3451);
x_3458 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_3443, x_3456, x_3457, x_3455, x_6, x_3452);
lean_dec(x_6);
lean_dec_ref(x_3443);
x_3459 = lean_ctor_get(x_3458, 1);
lean_inc(x_3459);
lean_dec_ref(x_3458);
x_3445 = x_3459;
goto block_3450;
}
}
}
block_3463:
{
if (x_3461 == 0)
{
lean_dec_ref(x_3430);
lean_dec(x_3426);
lean_dec(x_3415);
lean_dec_ref(x_1);
x_3452 = x_3462;
goto block_3460;
}
else
{
if (x_3074 == 0)
{
lean_dec(x_3451);
lean_dec_ref(x_3444);
lean_dec_ref(x_3443);
lean_dec(x_6);
x_3431 = x_3;
x_3432 = x_3462;
goto block_3438;
}
else
{
lean_dec_ref(x_3430);
lean_dec(x_3426);
lean_dec(x_3415);
lean_dec_ref(x_1);
x_3452 = x_3462;
goto block_3460;
}
}
}
}
else
{
lean_object* x_3471; lean_object* x_3472; 
lean_dec_ref(x_3430);
lean_dec(x_3426);
lean_dec(x_3415);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_3471 = lean_ctor_get(x_3442, 0);
lean_inc_ref(x_3471);
lean_dec_ref(x_3442);
if (lean_is_scalar(x_3428)) {
 x_3472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3472 = x_3428;
}
lean_ctor_set(x_3472, 0, x_3471);
lean_ctor_set(x_3472, 1, x_3427);
return x_3472;
}
}
block_3438:
{
lean_object* x_3433; lean_object* x_3434; lean_object* x_3435; lean_object* x_3436; lean_object* x_3437; 
lean_inc(x_3415);
x_3433 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_3415, x_3431, x_3432);
lean_dec(x_3431);
x_3434 = lean_ctor_get(x_3433, 1);
lean_inc(x_3434);
if (lean_is_exclusive(x_3433)) {
 lean_ctor_release(x_3433, 0);
 lean_ctor_release(x_3433, 1);
 x_3435 = x_3433;
} else {
 lean_dec_ref(x_3433);
 x_3435 = lean_box(0);
}
x_3436 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_1, x_3430, x_3415, x_3426);
if (lean_is_scalar(x_3435)) {
 x_3437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3437 = x_3435;
}
lean_ctor_set(x_3437, 0, x_3436);
lean_ctor_set(x_3437, 1, x_3434);
return x_3437;
}
}
else
{
lean_object* x_3473; lean_object* x_3474; lean_object* x_3475; lean_object* x_3476; 
lean_dec(x_3417);
lean_dec(x_3415);
lean_dec_ref(x_3410);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_3473 = lean_ctor_get(x_3425, 0);
lean_inc(x_3473);
x_3474 = lean_ctor_get(x_3425, 1);
lean_inc(x_3474);
if (lean_is_exclusive(x_3425)) {
 lean_ctor_release(x_3425, 0);
 lean_ctor_release(x_3425, 1);
 x_3475 = x_3425;
} else {
 lean_dec_ref(x_3425);
 x_3475 = lean_box(0);
}
if (lean_is_scalar(x_3475)) {
 x_3476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3476 = x_3475;
}
lean_ctor_set(x_3476, 0, x_3473);
lean_ctor_set(x_3476, 1, x_3474);
return x_3476;
}
}
else
{
lean_object* x_3477; lean_object* x_3478; lean_object* x_3479; lean_object* x_3480; 
lean_dec(x_3417);
lean_dec(x_3415);
lean_dec_ref(x_3410);
lean_dec_ref(x_3134);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3477 = lean_ctor_get(x_3422, 0);
lean_inc(x_3477);
x_3478 = lean_ctor_get(x_3422, 1);
lean_inc(x_3478);
if (lean_is_exclusive(x_3422)) {
 lean_ctor_release(x_3422, 0);
 lean_ctor_release(x_3422, 1);
 x_3479 = x_3422;
} else {
 lean_dec_ref(x_3422);
 x_3479 = lean_box(0);
}
if (lean_is_scalar(x_3479)) {
 x_3480 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3480 = x_3479;
}
lean_ctor_set(x_3480, 0, x_3477);
lean_ctor_set(x_3480, 1, x_3478);
return x_3480;
}
}
else
{
lean_object* x_3481; 
lean_dec_ref(x_3412);
lean_dec_ref(x_3410);
lean_dec_ref(x_3058);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3481 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_3134, x_8, x_3409);
lean_dec(x_8);
lean_dec_ref(x_3134);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_3481;
}
}
else
{
lean_object* x_3482; lean_object* x_3483; lean_object* x_3484; lean_object* x_3485; 
lean_dec_ref(x_3403);
lean_dec_ref(x_3134);
lean_dec_ref(x_3058);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3482 = lean_ctor_get(x_3404, 1);
lean_inc(x_3482);
if (lean_is_exclusive(x_3404)) {
 lean_ctor_release(x_3404, 0);
 lean_ctor_release(x_3404, 1);
 x_3483 = x_3404;
} else {
 lean_dec_ref(x_3404);
 x_3483 = lean_box(0);
}
x_3484 = lean_ctor_get(x_3405, 0);
lean_inc(x_3484);
lean_dec_ref(x_3405);
if (lean_is_scalar(x_3483)) {
 x_3485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3485 = x_3483;
}
lean_ctor_set(x_3485, 0, x_3484);
lean_ctor_set(x_3485, 1, x_3482);
return x_3485;
}
}
else
{
lean_object* x_3486; lean_object* x_3487; lean_object* x_3488; lean_object* x_3489; 
lean_dec_ref(x_3403);
lean_dec_ref(x_3134);
lean_dec_ref(x_3058);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3486 = lean_ctor_get(x_3404, 0);
lean_inc(x_3486);
x_3487 = lean_ctor_get(x_3404, 1);
lean_inc(x_3487);
if (lean_is_exclusive(x_3404)) {
 lean_ctor_release(x_3404, 0);
 lean_ctor_release(x_3404, 1);
 x_3488 = x_3404;
} else {
 lean_dec_ref(x_3404);
 x_3488 = lean_box(0);
}
if (lean_is_scalar(x_3488)) {
 x_3489 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3489 = x_3488;
}
lean_ctor_set(x_3489, 0, x_3486);
lean_ctor_set(x_3489, 1, x_3487);
return x_3489;
}
}
case 5:
{
lean_object* x_3490; lean_object* x_3491; lean_object* x_3492; lean_object* x_3493; lean_object* x_3494; lean_object* x_3495; 
lean_dec_ref(x_3058);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_3490 = lean_ctor_get(x_1, 0);
lean_inc(x_3490);
x_3491 = lean_st_ref_get(x_3, x_3077);
x_3492 = lean_ctor_get(x_3491, 0);
lean_inc(x_3492);
x_3493 = lean_ctor_get(x_3491, 1);
lean_inc(x_3493);
lean_dec_ref(x_3491);
x_3494 = lean_ctor_get(x_3492, 0);
lean_inc_ref(x_3494);
lean_dec(x_3492);
x_3495 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_3494, x_3490, x_3074);
lean_dec_ref(x_3494);
if (lean_obj_tag(x_3495) == 0)
{
lean_object* x_3496; lean_object* x_3497; lean_object* x_3498; lean_object* x_3499; lean_object* x_3500; lean_object* x_3501; 
lean_dec_ref(x_3134);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_3496 = lean_ctor_get(x_3495, 0);
lean_inc(x_3496);
lean_dec_ref(x_3495);
lean_inc(x_3496);
x_3497 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_3496, x_3, x_3493);
lean_dec(x_3);
x_3498 = lean_ctor_get(x_3497, 1);
lean_inc(x_3498);
if (lean_is_exclusive(x_3497)) {
 lean_ctor_release(x_3497, 0);
 lean_ctor_release(x_3497, 1);
 x_3499 = x_3497;
} else {
 lean_dec_ref(x_3497);
 x_3499 = lean_box(0);
}
x_3500 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_1, x_3496);
if (lean_is_scalar(x_3499)) {
 x_3501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3501 = x_3499;
}
lean_ctor_set(x_3501, 0, x_3500);
lean_ctor_set(x_3501, 1, x_3498);
return x_3501;
}
else
{
lean_object* x_3502; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_3502 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_3134, x_8, x_3493);
lean_dec(x_8);
lean_dec_ref(x_3134);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_3502;
}
}
case 6:
{
lean_object* x_3503; lean_object* x_3504; lean_object* x_3505; lean_object* x_3506; lean_object* x_3507; lean_object* x_3508; lean_object* x_3509; lean_object* x_3510; lean_object* x_3511; 
lean_dec_ref(x_3134);
lean_dec_ref(x_3058);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_3503 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3503);
x_3504 = lean_st_ref_get(x_3, x_3077);
lean_dec(x_3);
x_3505 = lean_ctor_get(x_3504, 0);
lean_inc(x_3505);
x_3506 = lean_ctor_get(x_3504, 1);
lean_inc(x_3506);
if (lean_is_exclusive(x_3504)) {
 lean_ctor_release(x_3504, 0);
 lean_ctor_release(x_3504, 1);
 x_3507 = x_3504;
} else {
 lean_dec_ref(x_3504);
 x_3507 = lean_box(0);
}
x_3508 = lean_ctor_get(x_3505, 0);
lean_inc_ref(x_3508);
lean_dec(x_3505);
x_3509 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_3508, x_3074, x_3503);
lean_dec_ref(x_3508);
x_3510 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(x_1, x_3509);
if (lean_is_scalar(x_3507)) {
 x_3511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3511 = x_3507;
}
lean_ctor_set(x_3511, 0, x_3510);
lean_ctor_set(x_3511, 1, x_3506);
return x_3511;
}
default: 
{
lean_object* x_3512; lean_object* x_3513; 
lean_dec_ref(x_3058);
x_3512 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3512);
x_3513 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3513);
x_3078 = x_3512;
x_3079 = x_3513;
x_3080 = x_2;
x_3081 = x_3;
x_3082 = x_4;
x_3083 = x_5;
x_3084 = x_6;
x_3085 = x_3134;
x_3086 = x_8;
goto block_3131;
}
}
block_3131:
{
lean_object* x_3087; lean_object* x_3088; lean_object* x_3089; lean_object* x_3090; lean_object* x_3091; lean_object* x_3092; lean_object* x_3093; uint8_t x_3094; 
x_3087 = lean_ctor_get(x_3078, 0);
lean_inc(x_3087);
x_3088 = lean_ctor_get(x_3078, 2);
lean_inc_ref(x_3088);
x_3089 = lean_ctor_get(x_3078, 3);
lean_inc_ref(x_3089);
x_3090 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_3087, x_3081, x_3077);
lean_dec(x_3087);
x_3091 = lean_ctor_get(x_3090, 0);
lean_inc(x_3091);
x_3092 = lean_ctor_get(x_3090, 1);
lean_inc(x_3092);
lean_dec_ref(x_3090);
lean_inc(x_3091);
lean_inc_ref(x_1);
lean_inc_ref(x_3079);
x_3093 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_3093, 0, x_3079);
lean_closure_set(x_3093, 1, x_1);
lean_closure_set(x_3093, 2, x_3091);
x_3094 = lean_unbox(x_3091);
if (x_3094 == 0)
{
uint8_t x_3095; 
lean_dec(x_3091);
lean_dec_ref(x_3079);
x_3095 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_3095 == 0)
{
lean_dec_ref(x_3089);
lean_dec_ref(x_3088);
x_10 = x_3093;
x_11 = x_3078;
x_12 = x_3080;
x_13 = x_3081;
x_14 = x_3082;
x_15 = x_3083;
x_16 = x_3084;
x_17 = x_3085;
x_18 = x_3086;
x_19 = x_3092;
goto block_29;
}
else
{
uint8_t x_3096; 
x_3096 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_3089, x_3088);
lean_dec_ref(x_3088);
if (x_3096 == 0)
{
x_10 = x_3093;
x_11 = x_3078;
x_12 = x_3080;
x_13 = x_3081;
x_14 = x_3082;
x_15 = x_3083;
x_16 = x_3084;
x_17 = x_3085;
x_18 = x_3086;
x_19 = x_3092;
goto block_29;
}
else
{
lean_object* x_3097; lean_object* x_3098; lean_object* x_3099; lean_object* x_3100; lean_object* x_3101; 
x_3097 = lean_st_ref_get(x_3081, x_3092);
x_3098 = lean_ctor_get(x_3097, 0);
lean_inc(x_3098);
x_3099 = lean_ctor_get(x_3097, 1);
lean_inc(x_3099);
lean_dec_ref(x_3097);
x_3100 = lean_ctor_get(x_3098, 0);
lean_inc_ref(x_3100);
lean_dec(x_3098);
lean_inc(x_3086);
lean_inc_ref(x_3085);
lean_inc(x_3084);
lean_inc_ref(x_3083);
x_3101 = l_Lean_Compiler_LCNF_normFunDeclImp(x_3074, x_3078, x_3100, x_3083, x_3084, x_3085, x_3086, x_3099);
if (lean_obj_tag(x_3101) == 0)
{
lean_object* x_3102; lean_object* x_3103; lean_object* x_3104; 
x_3102 = lean_ctor_get(x_3101, 0);
lean_inc(x_3102);
x_3103 = lean_ctor_get(x_3101, 1);
lean_inc(x_3103);
lean_dec_ref(x_3101);
lean_inc(x_3086);
lean_inc_ref(x_3085);
lean_inc(x_3084);
lean_inc_ref(x_3083);
x_3104 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_3102, x_3083, x_3084, x_3085, x_3086, x_3103);
if (lean_obj_tag(x_3104) == 0)
{
lean_object* x_3105; lean_object* x_3106; lean_object* x_3107; lean_object* x_3108; 
x_3105 = lean_ctor_get(x_3104, 0);
lean_inc(x_3105);
x_3106 = lean_ctor_get(x_3104, 1);
lean_inc(x_3106);
lean_dec_ref(x_3104);
x_3107 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3081, x_3106);
x_3108 = lean_ctor_get(x_3107, 1);
lean_inc(x_3108);
lean_dec_ref(x_3107);
x_10 = x_3093;
x_11 = x_3105;
x_12 = x_3080;
x_13 = x_3081;
x_14 = x_3082;
x_15 = x_3083;
x_16 = x_3084;
x_17 = x_3085;
x_18 = x_3086;
x_19 = x_3108;
goto block_29;
}
else
{
lean_object* x_3109; lean_object* x_3110; lean_object* x_3111; lean_object* x_3112; 
lean_dec_ref(x_3093);
lean_dec(x_3086);
lean_dec_ref(x_3085);
lean_dec(x_3084);
lean_dec_ref(x_3083);
lean_dec_ref(x_3082);
lean_dec(x_3081);
lean_dec_ref(x_3080);
x_3109 = lean_ctor_get(x_3104, 0);
lean_inc(x_3109);
x_3110 = lean_ctor_get(x_3104, 1);
lean_inc(x_3110);
if (lean_is_exclusive(x_3104)) {
 lean_ctor_release(x_3104, 0);
 lean_ctor_release(x_3104, 1);
 x_3111 = x_3104;
} else {
 lean_dec_ref(x_3104);
 x_3111 = lean_box(0);
}
if (lean_is_scalar(x_3111)) {
 x_3112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3112 = x_3111;
}
lean_ctor_set(x_3112, 0, x_3109);
lean_ctor_set(x_3112, 1, x_3110);
return x_3112;
}
}
else
{
lean_object* x_3113; lean_object* x_3114; lean_object* x_3115; lean_object* x_3116; 
lean_dec_ref(x_3093);
lean_dec(x_3086);
lean_dec_ref(x_3085);
lean_dec(x_3084);
lean_dec_ref(x_3083);
lean_dec_ref(x_3082);
lean_dec(x_3081);
lean_dec_ref(x_3080);
x_3113 = lean_ctor_get(x_3101, 0);
lean_inc(x_3113);
x_3114 = lean_ctor_get(x_3101, 1);
lean_inc(x_3114);
if (lean_is_exclusive(x_3101)) {
 lean_ctor_release(x_3101, 0);
 lean_ctor_release(x_3101, 1);
 x_3115 = x_3101;
} else {
 lean_dec_ref(x_3101);
 x_3115 = lean_box(0);
}
if (lean_is_scalar(x_3115)) {
 x_3116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3116 = x_3115;
}
lean_ctor_set(x_3116, 0, x_3113);
lean_ctor_set(x_3116, 1, x_3114);
return x_3116;
}
}
}
}
else
{
lean_object* x_3117; lean_object* x_3118; lean_object* x_3119; lean_object* x_3120; lean_object* x_3121; 
lean_dec_ref(x_3093);
lean_dec_ref(x_3089);
lean_dec_ref(x_3088);
x_3117 = lean_st_ref_get(x_3081, x_3092);
x_3118 = lean_ctor_get(x_3117, 0);
lean_inc(x_3118);
x_3119 = lean_ctor_get(x_3117, 1);
lean_inc(x_3119);
lean_dec_ref(x_3117);
x_3120 = lean_ctor_get(x_3118, 0);
lean_inc_ref(x_3120);
lean_dec(x_3118);
lean_inc(x_3086);
lean_inc_ref(x_3085);
lean_inc(x_3084);
lean_inc_ref(x_3083);
x_3121 = l_Lean_Compiler_LCNF_normFunDeclImp(x_3074, x_3078, x_3120, x_3083, x_3084, x_3085, x_3086, x_3119);
if (lean_obj_tag(x_3121) == 0)
{
lean_object* x_3122; lean_object* x_3123; lean_object* x_3124; uint8_t x_3125; lean_object* x_3126; 
x_3122 = lean_ctor_get(x_3121, 0);
lean_inc(x_3122);
x_3123 = lean_ctor_get(x_3121, 1);
lean_inc(x_3123);
lean_dec_ref(x_3121);
x_3124 = lean_box(0);
x_3125 = lean_unbox(x_3091);
lean_dec(x_3091);
x_3126 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_3079, x_1, x_3125, x_3122, x_3124, x_3080, x_3081, x_3082, x_3083, x_3084, x_3085, x_3086, x_3123);
lean_dec_ref(x_1);
return x_3126;
}
else
{
lean_object* x_3127; lean_object* x_3128; lean_object* x_3129; lean_object* x_3130; 
lean_dec(x_3091);
lean_dec(x_3086);
lean_dec_ref(x_3085);
lean_dec(x_3084);
lean_dec_ref(x_3083);
lean_dec_ref(x_3082);
lean_dec(x_3081);
lean_dec_ref(x_3080);
lean_dec_ref(x_3079);
lean_dec_ref(x_1);
x_3127 = lean_ctor_get(x_3121, 0);
lean_inc(x_3127);
x_3128 = lean_ctor_get(x_3121, 1);
lean_inc(x_3128);
if (lean_is_exclusive(x_3121)) {
 lean_ctor_release(x_3121, 0);
 lean_ctor_release(x_3121, 1);
 x_3129 = x_3121;
} else {
 lean_dec_ref(x_3121);
 x_3129 = lean_box(0);
}
if (lean_is_scalar(x_3129)) {
 x_3130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3130 = x_3129;
}
lean_ctor_set(x_3130, 0, x_3127);
lean_ctor_set(x_3130, 1, x_3128);
return x_3130;
}
}
}
}
else
{
lean_object* x_3514; 
lean_dec_ref(x_3073);
lean_dec(x_3071);
lean_dec(x_3069);
lean_dec(x_3068);
lean_dec(x_3067);
lean_dec(x_3066);
lean_dec(x_3065);
lean_dec(x_3064);
lean_dec(x_3063);
lean_dec(x_3062);
lean_dec(x_3061);
lean_dec_ref(x_3060);
lean_dec_ref(x_3059);
lean_dec_ref(x_3058);
lean_dec_ref(x_1);
x_3514 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_3514;
}
}
}
else
{
lean_object* x_3515; lean_object* x_3516; lean_object* x_3517; lean_object* x_3518; lean_object* x_3519; lean_object* x_3520; lean_object* x_3521; lean_object* x_3522; lean_object* x_3523; lean_object* x_3524; lean_object* x_3525; lean_object* x_3526; lean_object* x_3527; lean_object* x_3528; lean_object* x_3529; lean_object* x_3530; lean_object* x_3531; lean_object* x_3532; lean_object* x_3533; lean_object* x_3534; lean_object* x_3535; lean_object* x_3536; lean_object* x_3537; lean_object* x_3538; lean_object* x_3539; lean_object* x_3540; lean_object* x_3541; lean_object* x_3542; lean_object* x_3543; lean_object* x_3544; lean_object* x_3545; lean_object* x_3546; lean_object* x_3547; lean_object* x_3548; lean_object* x_3549; lean_object* x_3550; lean_object* x_3551; lean_object* x_3552; lean_object* x_3553; lean_object* x_3554; lean_object* x_3555; lean_object* x_3556; lean_object* x_3557; lean_object* x_3558; lean_object* x_3559; lean_object* x_3560; lean_object* x_3561; lean_object* x_3562; lean_object* x_3563; lean_object* x_3564; lean_object* x_3565; lean_object* x_3566; lean_object* x_3567; lean_object* x_3568; lean_object* x_3569; lean_object* x_3570; lean_object* x_3571; lean_object* x_3572; lean_object* x_3573; lean_object* x_3574; lean_object* x_3575; lean_object* x_3576; lean_object* x_3577; lean_object* x_3578; uint8_t x_3579; lean_object* x_3580; uint8_t x_3581; lean_object* x_3582; uint8_t x_3583; 
x_3515 = lean_ctor_get(x_30, 0);
lean_inc(x_3515);
lean_dec(x_30);
x_3516 = lean_ctor_get(x_3515, 0);
lean_inc_ref(x_3516);
x_3517 = lean_ctor_get(x_3515, 2);
lean_inc_ref(x_3517);
x_3518 = lean_ctor_get(x_3515, 3);
lean_inc_ref(x_3518);
x_3519 = lean_ctor_get(x_3515, 4);
lean_inc_ref(x_3519);
if (lean_is_exclusive(x_3515)) {
 lean_ctor_release(x_3515, 0);
 lean_ctor_release(x_3515, 1);
 lean_ctor_release(x_3515, 2);
 lean_ctor_release(x_3515, 3);
 lean_ctor_release(x_3515, 4);
 x_3520 = x_3515;
} else {
 lean_dec_ref(x_3515);
 x_3520 = lean_box(0);
}
x_3521 = l_Lean_Compiler_LCNF_Simp_simp___closed__2;
x_3522 = l_Lean_Compiler_LCNF_Simp_simp___closed__3;
lean_inc_ref(x_3516);
x_3523 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_3523, 0, x_3516);
x_3524 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3524, 0, x_3516);
x_3525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3525, 0, x_3523);
lean_ctor_set(x_3525, 1, x_3524);
x_3526 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3526, 0, x_3519);
x_3527 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_3527, 0, x_3518);
x_3528 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_3528, 0, x_3517);
if (lean_is_scalar(x_3520)) {
 x_3529 = lean_alloc_ctor(0, 5, 0);
} else {
 x_3529 = x_3520;
}
lean_ctor_set(x_3529, 0, x_3525);
lean_ctor_set(x_3529, 1, x_3521);
lean_ctor_set(x_3529, 2, x_3528);
lean_ctor_set(x_3529, 3, x_3527);
lean_ctor_set(x_3529, 4, x_3526);
x_3530 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3530, 0, x_3529);
lean_ctor_set(x_3530, 1, x_3522);
x_3531 = l_ReaderT_instMonad___redArg(x_3530);
x_3532 = lean_ctor_get(x_3531, 0);
lean_inc_ref(x_3532);
if (lean_is_exclusive(x_3531)) {
 lean_ctor_release(x_3531, 0);
 lean_ctor_release(x_3531, 1);
 x_3533 = x_3531;
} else {
 lean_dec_ref(x_3531);
 x_3533 = lean_box(0);
}
x_3534 = lean_ctor_get(x_3532, 0);
lean_inc_ref(x_3534);
x_3535 = lean_ctor_get(x_3532, 2);
lean_inc_ref(x_3535);
x_3536 = lean_ctor_get(x_3532, 3);
lean_inc_ref(x_3536);
x_3537 = lean_ctor_get(x_3532, 4);
lean_inc_ref(x_3537);
if (lean_is_exclusive(x_3532)) {
 lean_ctor_release(x_3532, 0);
 lean_ctor_release(x_3532, 1);
 lean_ctor_release(x_3532, 2);
 lean_ctor_release(x_3532, 3);
 lean_ctor_release(x_3532, 4);
 x_3538 = x_3532;
} else {
 lean_dec_ref(x_3532);
 x_3538 = lean_box(0);
}
x_3539 = l_Lean_Compiler_LCNF_Simp_simp___closed__4;
x_3540 = l_Lean_Compiler_LCNF_Simp_simp___closed__5;
lean_inc_ref(x_3534);
x_3541 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_3541, 0, x_3534);
x_3542 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3542, 0, x_3534);
x_3543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3543, 0, x_3541);
lean_ctor_set(x_3543, 1, x_3542);
x_3544 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3544, 0, x_3537);
x_3545 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_3545, 0, x_3536);
x_3546 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_3546, 0, x_3535);
if (lean_is_scalar(x_3538)) {
 x_3547 = lean_alloc_ctor(0, 5, 0);
} else {
 x_3547 = x_3538;
}
lean_ctor_set(x_3547, 0, x_3543);
lean_ctor_set(x_3547, 1, x_3539);
lean_ctor_set(x_3547, 2, x_3546);
lean_ctor_set(x_3547, 3, x_3545);
lean_ctor_set(x_3547, 4, x_3544);
if (lean_is_scalar(x_3533)) {
 x_3548 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3548 = x_3533;
}
lean_ctor_set(x_3548, 0, x_3547);
lean_ctor_set(x_3548, 1, x_3540);
x_3549 = l_ReaderT_instMonad___redArg(x_3548);
x_3550 = l_ReaderT_instMonad___redArg(x_3549);
x_3551 = lean_ctor_get(x_3550, 0);
lean_inc_ref(x_3551);
if (lean_is_exclusive(x_3550)) {
 lean_ctor_release(x_3550, 0);
 lean_ctor_release(x_3550, 1);
 x_3552 = x_3550;
} else {
 lean_dec_ref(x_3550);
 x_3552 = lean_box(0);
}
x_3553 = lean_ctor_get(x_3551, 0);
lean_inc_ref(x_3553);
x_3554 = lean_ctor_get(x_3551, 2);
lean_inc_ref(x_3554);
x_3555 = lean_ctor_get(x_3551, 3);
lean_inc_ref(x_3555);
x_3556 = lean_ctor_get(x_3551, 4);
lean_inc_ref(x_3556);
if (lean_is_exclusive(x_3551)) {
 lean_ctor_release(x_3551, 0);
 lean_ctor_release(x_3551, 1);
 lean_ctor_release(x_3551, 2);
 lean_ctor_release(x_3551, 3);
 lean_ctor_release(x_3551, 4);
 x_3557 = x_3551;
} else {
 lean_dec_ref(x_3551);
 x_3557 = lean_box(0);
}
x_3558 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_3559 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_3553);
x_3560 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_3560, 0, x_3553);
x_3561 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3561, 0, x_3553);
x_3562 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3562, 0, x_3560);
lean_ctor_set(x_3562, 1, x_3561);
x_3563 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_3563, 0, x_3556);
x_3564 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_3564, 0, x_3555);
x_3565 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_3565, 0, x_3554);
if (lean_is_scalar(x_3557)) {
 x_3566 = lean_alloc_ctor(0, 5, 0);
} else {
 x_3566 = x_3557;
}
lean_ctor_set(x_3566, 0, x_3562);
lean_ctor_set(x_3566, 1, x_3558);
lean_ctor_set(x_3566, 2, x_3565);
lean_ctor_set(x_3566, 3, x_3564);
lean_ctor_set(x_3566, 4, x_3563);
if (lean_is_scalar(x_3552)) {
 x_3567 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3567 = x_3552;
}
lean_ctor_set(x_3567, 0, x_3566);
lean_ctor_set(x_3567, 1, x_3559);
x_3568 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_3568);
x_3569 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_3569);
x_3570 = lean_ctor_get(x_7, 2);
lean_inc(x_3570);
x_3571 = lean_ctor_get(x_7, 3);
lean_inc(x_3571);
x_3572 = lean_ctor_get(x_7, 4);
lean_inc(x_3572);
x_3573 = lean_ctor_get(x_7, 5);
lean_inc(x_3573);
x_3574 = lean_ctor_get(x_7, 6);
lean_inc(x_3574);
x_3575 = lean_ctor_get(x_7, 7);
lean_inc(x_3575);
x_3576 = lean_ctor_get(x_7, 8);
lean_inc(x_3576);
x_3577 = lean_ctor_get(x_7, 9);
lean_inc(x_3577);
x_3578 = lean_ctor_get(x_7, 10);
lean_inc(x_3578);
x_3579 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_3580 = lean_ctor_get(x_7, 11);
lean_inc(x_3580);
x_3581 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_3582 = lean_ctor_get(x_7, 12);
lean_inc_ref(x_3582);
x_3583 = lean_nat_dec_eq(x_3571, x_3572);
if (x_3583 == 0)
{
lean_object* x_3584; lean_object* x_3585; lean_object* x_3586; lean_object* x_3587; lean_object* x_3588; lean_object* x_3589; lean_object* x_3590; lean_object* x_3591; lean_object* x_3592; lean_object* x_3593; lean_object* x_3594; lean_object* x_3595; lean_object* x_3641; lean_object* x_3642; lean_object* x_3643; 
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 lean_ctor_release(x_7, 9);
 lean_ctor_release(x_7, 10);
 lean_ctor_release(x_7, 11);
 lean_ctor_release(x_7, 12);
 x_3584 = x_7;
} else {
 lean_dec_ref(x_7);
 x_3584 = lean_box(0);
}
x_3585 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
x_3586 = lean_ctor_get(x_3585, 1);
lean_inc(x_3586);
lean_dec_ref(x_3585);
x_3641 = lean_unsigned_to_nat(1u);
x_3642 = lean_nat_add(x_3571, x_3641);
lean_dec(x_3571);
if (lean_is_scalar(x_3584)) {
 x_3643 = lean_alloc_ctor(0, 13, 2);
} else {
 x_3643 = x_3584;
}
lean_ctor_set(x_3643, 0, x_3568);
lean_ctor_set(x_3643, 1, x_3569);
lean_ctor_set(x_3643, 2, x_3570);
lean_ctor_set(x_3643, 3, x_3642);
lean_ctor_set(x_3643, 4, x_3572);
lean_ctor_set(x_3643, 5, x_3573);
lean_ctor_set(x_3643, 6, x_3574);
lean_ctor_set(x_3643, 7, x_3575);
lean_ctor_set(x_3643, 8, x_3576);
lean_ctor_set(x_3643, 9, x_3577);
lean_ctor_set(x_3643, 10, x_3578);
lean_ctor_set(x_3643, 11, x_3580);
lean_ctor_set(x_3643, 12, x_3582);
lean_ctor_set_uint8(x_3643, sizeof(void*)*13, x_3579);
lean_ctor_set_uint8(x_3643, sizeof(void*)*13 + 1, x_3581);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3644; lean_object* x_3645; lean_object* x_3646; lean_object* x_3647; lean_object* x_3648; lean_object* x_3649; lean_object* x_3650; lean_object* x_3651; lean_object* x_3652; lean_object* x_3653; uint8_t x_3654; lean_object* x_3655; lean_object* x_3656; lean_object* x_3657; lean_object* x_3658; lean_object* x_3659; lean_object* x_3660; lean_object* x_3661; lean_object* x_3662; lean_object* x_3670; lean_object* x_3671; lean_object* x_3672; lean_object* x_3673; lean_object* x_3674; lean_object* x_3675; lean_object* x_3676; lean_object* x_3677; lean_object* x_3678; uint8_t x_3679; lean_object* x_3825; lean_object* x_3826; lean_object* x_3827; lean_object* x_3828; lean_object* x_3829; lean_object* x_3830; lean_object* x_3831; lean_object* x_3832; lean_object* x_3833; lean_object* x_3834; lean_object* x_3835; lean_object* x_3840; lean_object* x_3841; lean_object* x_3842; lean_object* x_3843; lean_object* x_3844; lean_object* x_3845; lean_object* x_3846; lean_object* x_3847; lean_object* x_3848; lean_object* x_3849; lean_object* x_3850; uint8_t x_3873; 
lean_dec_ref(x_3567);
x_3644 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3644);
x_3645 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3645);
lean_inc_ref(x_3644);
x_3840 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_3583, x_3644, x_3, x_5, x_6, x_3643, x_8, x_3586);
x_3841 = lean_ctor_get(x_3840, 0);
lean_inc(x_3841);
x_3842 = lean_ctor_get(x_3840, 1);
lean_inc(x_3842);
lean_dec_ref(x_3840);
x_3873 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2069_(x_3644, x_3841);
lean_dec_ref(x_3644);
if (x_3873 == 0)
{
goto block_3872;
}
else
{
if (x_3583 == 0)
{
x_3843 = x_2;
x_3844 = x_3;
x_3845 = x_4;
x_3846 = x_5;
x_3847 = x_6;
x_3848 = x_3643;
x_3849 = x_8;
x_3850 = x_3842;
goto block_3869;
}
else
{
goto block_3872;
}
}
block_3669:
{
lean_object* x_3663; lean_object* x_3664; lean_object* x_3665; lean_object* x_3666; lean_object* x_3667; 
x_3663 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_3663, 0, x_3662);
lean_ctor_set(x_3663, 1, x_3651);
lean_ctor_set(x_3663, 2, x_3652);
lean_ctor_set(x_3663, 3, x_3653);
lean_ctor_set(x_3663, 4, x_3655);
lean_ctor_set(x_3663, 5, x_3656);
lean_ctor_set(x_3663, 6, x_3657);
lean_ctor_set_uint8(x_3663, sizeof(void*)*7, x_3654);
x_3664 = lean_st_ref_set(x_3649, x_3663, x_3660);
x_3665 = lean_ctor_get(x_3664, 1);
lean_inc(x_3665);
lean_dec_ref(x_3664);
x_3666 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_3650, x_3649, x_3646, x_3665);
lean_dec_ref(x_3650);
x_3667 = lean_ctor_get(x_3666, 1);
lean_inc(x_3667);
lean_dec_ref(x_3666);
x_1 = x_3645;
x_2 = x_3659;
x_3 = x_3649;
x_4 = x_3661;
x_5 = x_3658;
x_6 = x_3646;
x_7 = x_3648;
x_8 = x_3647;
x_9 = x_3667;
goto _start;
}
block_3824:
{
if (x_3679 == 0)
{
lean_object* x_3680; 
lean_inc(x_3672);
lean_inc_ref(x_3674);
lean_inc(x_3670);
lean_inc_ref(x_3677);
lean_inc_ref(x_3675);
x_3680 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_3675, x_3677, x_3670, x_3674, x_3672, x_3671);
if (lean_obj_tag(x_3680) == 0)
{
lean_object* x_3681; 
x_3681 = lean_ctor_get(x_3680, 0);
lean_inc(x_3681);
if (lean_obj_tag(x_3681) == 0)
{
lean_object* x_3682; lean_object* x_3683; 
x_3682 = lean_ctor_get(x_3680, 1);
lean_inc(x_3682);
lean_dec_ref(x_3680);
lean_inc(x_3672);
lean_inc_ref(x_3674);
lean_inc(x_3670);
lean_inc_ref(x_3677);
lean_inc_ref(x_3675);
x_3683 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_3675, x_3676, x_3673, x_3677, x_3670, x_3674, x_3672, x_3682);
if (lean_obj_tag(x_3683) == 0)
{
lean_object* x_3684; 
x_3684 = lean_ctor_get(x_3683, 0);
lean_inc(x_3684);
if (lean_obj_tag(x_3684) == 0)
{
lean_object* x_3685; lean_object* x_3686; lean_object* x_3687; lean_object* x_3688; lean_object* x_3689; 
x_3685 = lean_ctor_get(x_3683, 1);
lean_inc(x_3685);
lean_dec_ref(x_3683);
x_3686 = lean_ctor_get(x_3675, 0);
lean_inc(x_3686);
x_3687 = lean_ctor_get(x_3675, 3);
lean_inc(x_3687);
lean_inc(x_3687);
x_3688 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_3687, x_3685);
x_3689 = lean_ctor_get(x_3688, 0);
lean_inc(x_3689);
if (lean_obj_tag(x_3689) == 0)
{
lean_object* x_3690; lean_object* x_3691; 
x_3690 = lean_ctor_get(x_3688, 1);
lean_inc(x_3690);
lean_dec_ref(x_3688);
lean_inc(x_3672);
lean_inc_ref(x_3674);
lean_inc(x_3670);
lean_inc_ref(x_3677);
lean_inc_ref(x_3678);
lean_inc(x_3673);
lean_inc_ref(x_3676);
lean_inc_ref(x_3645);
lean_inc_ref(x_3675);
x_3691 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_3675, x_3645, x_3676, x_3673, x_3678, x_3677, x_3670, x_3674, x_3672, x_3690);
if (lean_obj_tag(x_3691) == 0)
{
lean_object* x_3692; 
x_3692 = lean_ctor_get(x_3691, 0);
lean_inc(x_3692);
if (lean_obj_tag(x_3692) == 0)
{
lean_object* x_3693; lean_object* x_3694; 
x_3693 = lean_ctor_get(x_3691, 1);
lean_inc(x_3693);
lean_dec_ref(x_3691);
lean_inc(x_3672);
lean_inc_ref(x_3674);
lean_inc(x_3670);
lean_inc_ref(x_3677);
lean_inc_ref(x_3678);
lean_inc(x_3673);
lean_inc_ref(x_3676);
x_3694 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_3687, x_3676, x_3673, x_3678, x_3677, x_3670, x_3674, x_3672, x_3693);
if (lean_obj_tag(x_3694) == 0)
{
lean_object* x_3695; 
x_3695 = lean_ctor_get(x_3694, 0);
lean_inc(x_3695);
if (lean_obj_tag(x_3695) == 0)
{
lean_object* x_3696; lean_object* x_3697; 
x_3696 = lean_ctor_get(x_3694, 1);
lean_inc(x_3696);
lean_dec_ref(x_3694);
lean_inc(x_3672);
lean_inc_ref(x_3674);
lean_inc(x_3670);
lean_inc_ref(x_3677);
lean_inc_ref(x_3678);
lean_inc(x_3673);
lean_inc_ref(x_3676);
x_3697 = l_Lean_Compiler_LCNF_Simp_simp(x_3645, x_3676, x_3673, x_3678, x_3677, x_3670, x_3674, x_3672, x_3696);
if (lean_obj_tag(x_3697) == 0)
{
lean_object* x_3698; lean_object* x_3699; lean_object* x_3700; lean_object* x_3701; uint8_t x_3702; 
x_3698 = lean_ctor_get(x_3697, 0);
lean_inc(x_3698);
x_3699 = lean_ctor_get(x_3697, 1);
lean_inc(x_3699);
lean_dec_ref(x_3697);
x_3700 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_3686, x_3673, x_3699);
lean_dec(x_3686);
x_3701 = lean_ctor_get(x_3700, 0);
lean_inc(x_3701);
x_3702 = lean_unbox(x_3701);
lean_dec(x_3701);
if (x_3702 == 0)
{
lean_object* x_3703; lean_object* x_3704; lean_object* x_3705; lean_object* x_3706; lean_object* x_3707; 
lean_dec_ref(x_3678);
lean_dec_ref(x_3677);
lean_dec_ref(x_3676);
lean_dec_ref(x_3674);
lean_dec(x_3672);
lean_dec_ref(x_1);
x_3703 = lean_ctor_get(x_3700, 1);
lean_inc(x_3703);
lean_dec_ref(x_3700);
x_3704 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_3675, x_3673, x_3670, x_3703);
lean_dec(x_3670);
lean_dec(x_3673);
lean_dec_ref(x_3675);
x_3705 = lean_ctor_get(x_3704, 1);
lean_inc(x_3705);
if (lean_is_exclusive(x_3704)) {
 lean_ctor_release(x_3704, 0);
 lean_ctor_release(x_3704, 1);
 x_3706 = x_3704;
} else {
 lean_dec_ref(x_3704);
 x_3706 = lean_box(0);
}
if (lean_is_scalar(x_3706)) {
 x_3707 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3707 = x_3706;
}
lean_ctor_set(x_3707, 0, x_3698);
lean_ctor_set(x_3707, 1, x_3705);
return x_3707;
}
else
{
lean_object* x_3708; lean_object* x_3709; lean_object* x_3710; lean_object* x_3711; lean_object* x_3712; lean_object* x_3713; 
x_3708 = lean_ctor_get(x_3700, 1);
lean_inc(x_3708);
lean_dec_ref(x_3700);
lean_inc_ref(x_3675);
x_3709 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_3675, x_3676, x_3673, x_3678, x_3677, x_3670, x_3674, x_3672, x_3708);
lean_dec(x_3672);
lean_dec_ref(x_3674);
lean_dec(x_3670);
lean_dec_ref(x_3677);
lean_dec_ref(x_3678);
lean_dec(x_3673);
lean_dec_ref(x_3676);
x_3710 = lean_ctor_get(x_3709, 1);
lean_inc(x_3710);
if (lean_is_exclusive(x_3709)) {
 lean_ctor_release(x_3709, 0);
 lean_ctor_release(x_3709, 1);
 x_3711 = x_3709;
} else {
 lean_dec_ref(x_3709);
 x_3711 = lean_box(0);
}
x_3712 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_1, x_3675, x_3698);
lean_dec_ref(x_1);
if (lean_is_scalar(x_3711)) {
 x_3713 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3713 = x_3711;
}
lean_ctor_set(x_3713, 0, x_3712);
lean_ctor_set(x_3713, 1, x_3710);
return x_3713;
}
}
else
{
lean_dec(x_3686);
lean_dec_ref(x_3678);
lean_dec_ref(x_3677);
lean_dec_ref(x_3676);
lean_dec_ref(x_3675);
lean_dec_ref(x_3674);
lean_dec(x_3673);
lean_dec(x_3672);
lean_dec(x_3670);
lean_dec_ref(x_1);
return x_3697;
}
}
else
{
lean_object* x_3714; lean_object* x_3715; lean_object* x_3716; lean_object* x_3717; lean_object* x_3718; 
lean_dec_ref(x_1);
x_3714 = lean_ctor_get(x_3695, 0);
lean_inc(x_3714);
lean_dec_ref(x_3695);
x_3715 = lean_ctor_get(x_3694, 1);
lean_inc(x_3715);
lean_dec_ref(x_3694);
x_3716 = lean_ctor_get(x_3714, 0);
lean_inc(x_3716);
x_3717 = lean_ctor_get(x_3714, 1);
lean_inc(x_3717);
lean_dec(x_3714);
x_3718 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3686, x_3717, x_3673, x_3670, x_3674, x_3672, x_3715);
if (lean_obj_tag(x_3718) == 0)
{
lean_object* x_3719; lean_object* x_3720; lean_object* x_3721; lean_object* x_3722; 
x_3719 = lean_ctor_get(x_3718, 1);
lean_inc(x_3719);
lean_dec_ref(x_3718);
x_3720 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_3675, x_3673, x_3670, x_3719);
lean_dec_ref(x_3675);
x_3721 = lean_ctor_get(x_3720, 1);
lean_inc(x_3721);
lean_dec_ref(x_3720);
lean_inc(x_3672);
lean_inc_ref(x_3674);
lean_inc(x_3670);
lean_inc_ref(x_3677);
lean_inc_ref(x_3678);
lean_inc(x_3673);
lean_inc_ref(x_3676);
x_3722 = l_Lean_Compiler_LCNF_Simp_simp(x_3645, x_3676, x_3673, x_3678, x_3677, x_3670, x_3674, x_3672, x_3721);
if (lean_obj_tag(x_3722) == 0)
{
lean_object* x_3723; lean_object* x_3724; lean_object* x_3725; 
x_3723 = lean_ctor_get(x_3722, 0);
lean_inc(x_3723);
x_3724 = lean_ctor_get(x_3722, 1);
lean_inc(x_3724);
lean_dec_ref(x_3722);
x_3725 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_3716, x_3723, x_3676, x_3673, x_3678, x_3677, x_3670, x_3674, x_3672, x_3724);
lean_dec(x_3672);
lean_dec_ref(x_3674);
lean_dec(x_3670);
lean_dec_ref(x_3677);
lean_dec_ref(x_3678);
lean_dec(x_3673);
lean_dec_ref(x_3676);
lean_dec(x_3716);
return x_3725;
}
else
{
lean_dec(x_3716);
lean_dec_ref(x_3678);
lean_dec_ref(x_3677);
lean_dec_ref(x_3676);
lean_dec_ref(x_3674);
lean_dec(x_3673);
lean_dec(x_3672);
lean_dec(x_3670);
return x_3722;
}
}
else
{
lean_object* x_3726; lean_object* x_3727; lean_object* x_3728; lean_object* x_3729; 
lean_dec(x_3716);
lean_dec_ref(x_3678);
lean_dec_ref(x_3677);
lean_dec_ref(x_3676);
lean_dec_ref(x_3675);
lean_dec_ref(x_3674);
lean_dec(x_3673);
lean_dec(x_3672);
lean_dec(x_3670);
lean_dec_ref(x_3645);
x_3726 = lean_ctor_get(x_3718, 0);
lean_inc(x_3726);
x_3727 = lean_ctor_get(x_3718, 1);
lean_inc(x_3727);
if (lean_is_exclusive(x_3718)) {
 lean_ctor_release(x_3718, 0);
 lean_ctor_release(x_3718, 1);
 x_3728 = x_3718;
} else {
 lean_dec_ref(x_3718);
 x_3728 = lean_box(0);
}
if (lean_is_scalar(x_3728)) {
 x_3729 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3729 = x_3728;
}
lean_ctor_set(x_3729, 0, x_3726);
lean_ctor_set(x_3729, 1, x_3727);
return x_3729;
}
}
}
else
{
lean_object* x_3730; lean_object* x_3731; lean_object* x_3732; lean_object* x_3733; 
lean_dec(x_3686);
lean_dec_ref(x_3678);
lean_dec_ref(x_3677);
lean_dec_ref(x_3676);
lean_dec_ref(x_3675);
lean_dec_ref(x_3674);
lean_dec(x_3673);
lean_dec(x_3672);
lean_dec(x_3670);
lean_dec_ref(x_3645);
lean_dec_ref(x_1);
x_3730 = lean_ctor_get(x_3694, 0);
lean_inc(x_3730);
x_3731 = lean_ctor_get(x_3694, 1);
lean_inc(x_3731);
if (lean_is_exclusive(x_3694)) {
 lean_ctor_release(x_3694, 0);
 lean_ctor_release(x_3694, 1);
 x_3732 = x_3694;
} else {
 lean_dec_ref(x_3694);
 x_3732 = lean_box(0);
}
if (lean_is_scalar(x_3732)) {
 x_3733 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3733 = x_3732;
}
lean_ctor_set(x_3733, 0, x_3730);
lean_ctor_set(x_3733, 1, x_3731);
return x_3733;
}
}
else
{
lean_object* x_3734; lean_object* x_3735; lean_object* x_3736; lean_object* x_3737; lean_object* x_3738; lean_object* x_3739; 
lean_dec(x_3687);
lean_dec(x_3686);
lean_dec_ref(x_3678);
lean_dec_ref(x_3677);
lean_dec_ref(x_3676);
lean_dec_ref(x_3674);
lean_dec(x_3672);
lean_dec_ref(x_3645);
lean_dec_ref(x_1);
x_3734 = lean_ctor_get(x_3691, 1);
lean_inc(x_3734);
lean_dec_ref(x_3691);
x_3735 = lean_ctor_get(x_3692, 0);
lean_inc(x_3735);
lean_dec_ref(x_3692);
x_3736 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_3675, x_3673, x_3670, x_3734);
lean_dec(x_3670);
lean_dec(x_3673);
lean_dec_ref(x_3675);
x_3737 = lean_ctor_get(x_3736, 1);
lean_inc(x_3737);
if (lean_is_exclusive(x_3736)) {
 lean_ctor_release(x_3736, 0);
 lean_ctor_release(x_3736, 1);
 x_3738 = x_3736;
} else {
 lean_dec_ref(x_3736);
 x_3738 = lean_box(0);
}
if (lean_is_scalar(x_3738)) {
 x_3739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3739 = x_3738;
}
lean_ctor_set(x_3739, 0, x_3735);
lean_ctor_set(x_3739, 1, x_3737);
return x_3739;
}
}
else
{
lean_object* x_3740; lean_object* x_3741; lean_object* x_3742; lean_object* x_3743; 
lean_dec(x_3687);
lean_dec(x_3686);
lean_dec_ref(x_3678);
lean_dec_ref(x_3677);
lean_dec_ref(x_3676);
lean_dec_ref(x_3675);
lean_dec_ref(x_3674);
lean_dec(x_3673);
lean_dec(x_3672);
lean_dec(x_3670);
lean_dec_ref(x_3645);
lean_dec_ref(x_1);
x_3740 = lean_ctor_get(x_3691, 0);
lean_inc(x_3740);
x_3741 = lean_ctor_get(x_3691, 1);
lean_inc(x_3741);
if (lean_is_exclusive(x_3691)) {
 lean_ctor_release(x_3691, 0);
 lean_ctor_release(x_3691, 1);
 x_3742 = x_3691;
} else {
 lean_dec_ref(x_3691);
 x_3742 = lean_box(0);
}
if (lean_is_scalar(x_3742)) {
 x_3743 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3743 = x_3742;
}
lean_ctor_set(x_3743, 0, x_3740);
lean_ctor_set(x_3743, 1, x_3741);
return x_3743;
}
}
else
{
lean_object* x_3744; lean_object* x_3745; lean_object* x_3746; 
lean_dec(x_3687);
lean_dec_ref(x_1);
x_3744 = lean_ctor_get(x_3688, 1);
lean_inc(x_3744);
lean_dec_ref(x_3688);
x_3745 = lean_ctor_get(x_3689, 0);
lean_inc(x_3745);
lean_dec_ref(x_3689);
x_3746 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3686, x_3745, x_3673, x_3670, x_3674, x_3672, x_3744);
if (lean_obj_tag(x_3746) == 0)
{
lean_object* x_3747; lean_object* x_3748; lean_object* x_3749; 
x_3747 = lean_ctor_get(x_3746, 1);
lean_inc(x_3747);
lean_dec_ref(x_3746);
x_3748 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_3675, x_3673, x_3670, x_3747);
lean_dec_ref(x_3675);
x_3749 = lean_ctor_get(x_3748, 1);
lean_inc(x_3749);
lean_dec_ref(x_3748);
x_1 = x_3645;
x_2 = x_3676;
x_3 = x_3673;
x_4 = x_3678;
x_5 = x_3677;
x_6 = x_3670;
x_7 = x_3674;
x_8 = x_3672;
x_9 = x_3749;
goto _start;
}
else
{
lean_object* x_3751; lean_object* x_3752; lean_object* x_3753; lean_object* x_3754; 
lean_dec_ref(x_3678);
lean_dec_ref(x_3677);
lean_dec_ref(x_3676);
lean_dec_ref(x_3675);
lean_dec_ref(x_3674);
lean_dec(x_3673);
lean_dec(x_3672);
lean_dec(x_3670);
lean_dec_ref(x_3645);
x_3751 = lean_ctor_get(x_3746, 0);
lean_inc(x_3751);
x_3752 = lean_ctor_get(x_3746, 1);
lean_inc(x_3752);
if (lean_is_exclusive(x_3746)) {
 lean_ctor_release(x_3746, 0);
 lean_ctor_release(x_3746, 1);
 x_3753 = x_3746;
} else {
 lean_dec_ref(x_3746);
 x_3753 = lean_box(0);
}
if (lean_is_scalar(x_3753)) {
 x_3754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3754 = x_3753;
}
lean_ctor_set(x_3754, 0, x_3751);
lean_ctor_set(x_3754, 1, x_3752);
return x_3754;
}
}
}
else
{
lean_object* x_3755; lean_object* x_3756; lean_object* x_3757; lean_object* x_3758; 
lean_dec_ref(x_3675);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_3755 = x_1;
} else {
 lean_dec_ref(x_1);
 x_3755 = lean_box(0);
}
x_3756 = lean_ctor_get(x_3683, 1);
lean_inc(x_3756);
lean_dec_ref(x_3683);
x_3757 = lean_ctor_get(x_3684, 0);
lean_inc(x_3757);
lean_dec_ref(x_3684);
if (lean_is_scalar(x_3755)) {
 x_3758 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3758 = x_3755;
 lean_ctor_set_tag(x_3758, 1);
}
lean_ctor_set(x_3758, 0, x_3757);
lean_ctor_set(x_3758, 1, x_3645);
x_1 = x_3758;
x_2 = x_3676;
x_3 = x_3673;
x_4 = x_3678;
x_5 = x_3677;
x_6 = x_3670;
x_7 = x_3674;
x_8 = x_3672;
x_9 = x_3756;
goto _start;
}
}
else
{
lean_object* x_3760; lean_object* x_3761; lean_object* x_3762; lean_object* x_3763; 
lean_dec_ref(x_3678);
lean_dec_ref(x_3677);
lean_dec_ref(x_3676);
lean_dec_ref(x_3675);
lean_dec_ref(x_3674);
lean_dec(x_3673);
lean_dec(x_3672);
lean_dec(x_3670);
lean_dec_ref(x_3645);
lean_dec_ref(x_1);
x_3760 = lean_ctor_get(x_3683, 0);
lean_inc(x_3760);
x_3761 = lean_ctor_get(x_3683, 1);
lean_inc(x_3761);
if (lean_is_exclusive(x_3683)) {
 lean_ctor_release(x_3683, 0);
 lean_ctor_release(x_3683, 1);
 x_3762 = x_3683;
} else {
 lean_dec_ref(x_3683);
 x_3762 = lean_box(0);
}
if (lean_is_scalar(x_3762)) {
 x_3763 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3763 = x_3762;
}
lean_ctor_set(x_3763, 0, x_3760);
lean_ctor_set(x_3763, 1, x_3761);
return x_3763;
}
}
else
{
lean_object* x_3764; lean_object* x_3765; lean_object* x_3766; lean_object* x_3767; lean_object* x_3768; 
lean_dec_ref(x_3675);
lean_dec_ref(x_1);
x_3764 = lean_ctor_get(x_3680, 1);
lean_inc(x_3764);
lean_dec_ref(x_3680);
x_3765 = lean_ctor_get(x_3681, 0);
lean_inc(x_3765);
lean_dec_ref(x_3681);
x_3766 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3673, x_3764);
x_3767 = lean_ctor_get(x_3766, 1);
lean_inc(x_3767);
lean_dec_ref(x_3766);
lean_inc(x_3672);
lean_inc_ref(x_3674);
lean_inc(x_3670);
lean_inc_ref(x_3677);
lean_inc_ref(x_3678);
lean_inc(x_3673);
lean_inc_ref(x_3676);
x_3768 = l_Lean_Compiler_LCNF_Simp_simp(x_3645, x_3676, x_3673, x_3678, x_3677, x_3670, x_3674, x_3672, x_3767);
if (lean_obj_tag(x_3768) == 0)
{
lean_object* x_3769; lean_object* x_3770; lean_object* x_3771; 
x_3769 = lean_ctor_get(x_3768, 0);
lean_inc(x_3769);
x_3770 = lean_ctor_get(x_3768, 1);
lean_inc(x_3770);
lean_dec_ref(x_3768);
x_3771 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_3765, x_3769, x_3676, x_3673, x_3678, x_3677, x_3670, x_3674, x_3672, x_3770);
lean_dec(x_3672);
lean_dec_ref(x_3674);
lean_dec(x_3670);
lean_dec_ref(x_3677);
lean_dec_ref(x_3678);
lean_dec(x_3673);
lean_dec_ref(x_3676);
lean_dec(x_3765);
return x_3771;
}
else
{
lean_dec(x_3765);
lean_dec_ref(x_3678);
lean_dec_ref(x_3677);
lean_dec_ref(x_3676);
lean_dec_ref(x_3674);
lean_dec(x_3673);
lean_dec(x_3672);
lean_dec(x_3670);
return x_3768;
}
}
}
else
{
lean_object* x_3772; lean_object* x_3773; lean_object* x_3774; lean_object* x_3775; 
lean_dec_ref(x_3678);
lean_dec_ref(x_3677);
lean_dec_ref(x_3676);
lean_dec_ref(x_3675);
lean_dec_ref(x_3674);
lean_dec(x_3673);
lean_dec(x_3672);
lean_dec(x_3670);
lean_dec_ref(x_3645);
lean_dec_ref(x_1);
x_3772 = lean_ctor_get(x_3680, 0);
lean_inc(x_3772);
x_3773 = lean_ctor_get(x_3680, 1);
lean_inc(x_3773);
if (lean_is_exclusive(x_3680)) {
 lean_ctor_release(x_3680, 0);
 lean_ctor_release(x_3680, 1);
 x_3774 = x_3680;
} else {
 lean_dec_ref(x_3680);
 x_3774 = lean_box(0);
}
if (lean_is_scalar(x_3774)) {
 x_3775 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3775 = x_3774;
}
lean_ctor_set(x_3775, 0, x_3772);
lean_ctor_set(x_3775, 1, x_3773);
return x_3775;
}
}
else
{
lean_object* x_3776; lean_object* x_3777; lean_object* x_3778; lean_object* x_3779; lean_object* x_3780; lean_object* x_3781; lean_object* x_3782; uint8_t x_3783; lean_object* x_3784; lean_object* x_3785; lean_object* x_3786; lean_object* x_3787; lean_object* x_3788; lean_object* x_3789; lean_object* x_3790; lean_object* x_3791; lean_object* x_3792; uint64_t x_3793; uint64_t x_3794; uint64_t x_3795; uint64_t x_3796; uint64_t x_3797; uint64_t x_3798; uint64_t x_3799; size_t x_3800; size_t x_3801; size_t x_3802; size_t x_3803; size_t x_3804; lean_object* x_3805; uint8_t x_3806; 
lean_dec_ref(x_1);
x_3776 = lean_st_ref_take(x_3673, x_3671);
x_3777 = lean_ctor_get(x_3776, 0);
lean_inc(x_3777);
x_3778 = lean_ctor_get(x_3777, 0);
lean_inc_ref(x_3778);
x_3779 = lean_ctor_get(x_3776, 1);
lean_inc(x_3779);
lean_dec_ref(x_3776);
x_3780 = lean_ctor_get(x_3777, 1);
lean_inc_ref(x_3780);
x_3781 = lean_ctor_get(x_3777, 2);
lean_inc(x_3781);
x_3782 = lean_ctor_get(x_3777, 3);
lean_inc_ref(x_3782);
x_3783 = lean_ctor_get_uint8(x_3777, sizeof(void*)*7);
x_3784 = lean_ctor_get(x_3777, 4);
lean_inc(x_3784);
x_3785 = lean_ctor_get(x_3777, 5);
lean_inc(x_3785);
x_3786 = lean_ctor_get(x_3777, 6);
lean_inc(x_3786);
lean_dec(x_3777);
x_3787 = lean_ctor_get(x_3778, 0);
lean_inc(x_3787);
x_3788 = lean_ctor_get(x_3778, 1);
lean_inc_ref(x_3788);
if (lean_is_exclusive(x_3778)) {
 lean_ctor_release(x_3778, 0);
 lean_ctor_release(x_3778, 1);
 x_3789 = x_3778;
} else {
 lean_dec_ref(x_3778);
 x_3789 = lean_box(0);
}
x_3790 = lean_ctor_get(x_3675, 0);
lean_inc(x_3790);
x_3791 = lean_box(0);
x_3792 = lean_array_get_size(x_3788);
x_3793 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_3790);
x_3794 = 32;
x_3795 = lean_uint64_shift_right(x_3793, x_3794);
x_3796 = lean_uint64_xor(x_3793, x_3795);
x_3797 = 16;
x_3798 = lean_uint64_shift_right(x_3796, x_3797);
x_3799 = lean_uint64_xor(x_3796, x_3798);
x_3800 = lean_uint64_to_usize(x_3799);
x_3801 = lean_usize_of_nat(x_3792);
lean_dec(x_3792);
x_3802 = 1;
x_3803 = lean_usize_sub(x_3801, x_3802);
x_3804 = lean_usize_land(x_3800, x_3803);
x_3805 = lean_array_uget(x_3788, x_3804);
x_3806 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_3790, x_3805);
if (x_3806 == 0)
{
lean_object* x_3807; lean_object* x_3808; lean_object* x_3809; lean_object* x_3810; lean_object* x_3811; lean_object* x_3812; lean_object* x_3813; lean_object* x_3814; uint8_t x_3815; 
x_3807 = lean_nat_add(x_3787, x_3641);
lean_dec(x_3787);
x_3808 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3808, 0, x_3790);
lean_ctor_set(x_3808, 1, x_3791);
lean_ctor_set(x_3808, 2, x_3805);
x_3809 = lean_array_uset(x_3788, x_3804, x_3808);
x_3810 = lean_unsigned_to_nat(4u);
x_3811 = lean_nat_mul(x_3807, x_3810);
x_3812 = lean_unsigned_to_nat(3u);
x_3813 = lean_nat_div(x_3811, x_3812);
lean_dec(x_3811);
x_3814 = lean_array_get_size(x_3809);
x_3815 = lean_nat_dec_le(x_3813, x_3814);
lean_dec(x_3814);
lean_dec(x_3813);
if (x_3815 == 0)
{
lean_object* x_3816; lean_object* x_3817; 
x_3816 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_3809);
if (lean_is_scalar(x_3789)) {
 x_3817 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3817 = x_3789;
}
lean_ctor_set(x_3817, 0, x_3807);
lean_ctor_set(x_3817, 1, x_3816);
x_3646 = x_3670;
x_3647 = x_3672;
x_3648 = x_3674;
x_3649 = x_3673;
x_3650 = x_3675;
x_3651 = x_3780;
x_3652 = x_3781;
x_3653 = x_3782;
x_3654 = x_3783;
x_3655 = x_3784;
x_3656 = x_3785;
x_3657 = x_3786;
x_3658 = x_3677;
x_3659 = x_3676;
x_3660 = x_3779;
x_3661 = x_3678;
x_3662 = x_3817;
goto block_3669;
}
else
{
lean_object* x_3818; 
if (lean_is_scalar(x_3789)) {
 x_3818 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3818 = x_3789;
}
lean_ctor_set(x_3818, 0, x_3807);
lean_ctor_set(x_3818, 1, x_3809);
x_3646 = x_3670;
x_3647 = x_3672;
x_3648 = x_3674;
x_3649 = x_3673;
x_3650 = x_3675;
x_3651 = x_3780;
x_3652 = x_3781;
x_3653 = x_3782;
x_3654 = x_3783;
x_3655 = x_3784;
x_3656 = x_3785;
x_3657 = x_3786;
x_3658 = x_3677;
x_3659 = x_3676;
x_3660 = x_3779;
x_3661 = x_3678;
x_3662 = x_3818;
goto block_3669;
}
}
else
{
lean_object* x_3819; lean_object* x_3820; lean_object* x_3821; lean_object* x_3822; lean_object* x_3823; 
x_3819 = lean_box(0);
x_3820 = lean_array_uset(x_3788, x_3804, x_3819);
x_3821 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_3790, x_3791, x_3805);
x_3822 = lean_array_uset(x_3820, x_3804, x_3821);
if (lean_is_scalar(x_3789)) {
 x_3823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3823 = x_3789;
}
lean_ctor_set(x_3823, 0, x_3787);
lean_ctor_set(x_3823, 1, x_3822);
x_3646 = x_3670;
x_3647 = x_3672;
x_3648 = x_3674;
x_3649 = x_3673;
x_3650 = x_3675;
x_3651 = x_3780;
x_3652 = x_3781;
x_3653 = x_3782;
x_3654 = x_3783;
x_3655 = x_3784;
x_3656 = x_3785;
x_3657 = x_3786;
x_3658 = x_3677;
x_3659 = x_3676;
x_3660 = x_3779;
x_3661 = x_3678;
x_3662 = x_3823;
goto block_3669;
}
}
}
block_3839:
{
uint8_t x_3836; 
x_3836 = l_Lean_Expr_isErased(x_3826);
lean_dec_ref(x_3826);
if (x_3836 == 0)
{
lean_dec(x_3827);
x_3670 = x_3832;
x_3671 = x_3835;
x_3672 = x_3834;
x_3673 = x_3829;
x_3674 = x_3833;
x_3675 = x_3825;
x_3676 = x_3828;
x_3677 = x_3831;
x_3678 = x_3830;
x_3679 = x_3583;
goto block_3824;
}
else
{
lean_object* x_3837; uint8_t x_3838; 
x_3837 = lean_box(1);
x_3838 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1209_(x_3827, x_3837);
lean_dec(x_3827);
if (x_3838 == 0)
{
x_3670 = x_3832;
x_3671 = x_3835;
x_3672 = x_3834;
x_3673 = x_3829;
x_3674 = x_3833;
x_3675 = x_3825;
x_3676 = x_3828;
x_3677 = x_3831;
x_3678 = x_3830;
x_3679 = x_3836;
goto block_3824;
}
else
{
x_3670 = x_3832;
x_3671 = x_3835;
x_3672 = x_3834;
x_3673 = x_3829;
x_3674 = x_3833;
x_3675 = x_3825;
x_3676 = x_3828;
x_3677 = x_3831;
x_3678 = x_3830;
x_3679 = x_3583;
goto block_3824;
}
}
}
block_3869:
{
lean_object* x_3851; lean_object* x_3852; lean_object* x_3853; 
x_3851 = lean_ctor_get(x_3841, 2);
lean_inc_ref(x_3851);
x_3852 = lean_ctor_get(x_3841, 3);
lean_inc(x_3852);
lean_inc(x_3849);
lean_inc_ref(x_3848);
lean_inc(x_3847);
lean_inc_ref(x_3846);
lean_inc_ref(x_3845);
lean_inc(x_3852);
x_3853 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_3852, x_3843, x_3845, x_3846, x_3847, x_3848, x_3849, x_3850);
if (lean_obj_tag(x_3853) == 0)
{
lean_object* x_3854; 
x_3854 = lean_ctor_get(x_3853, 0);
lean_inc(x_3854);
if (lean_obj_tag(x_3854) == 0)
{
lean_object* x_3855; 
x_3855 = lean_ctor_get(x_3853, 1);
lean_inc(x_3855);
lean_dec_ref(x_3853);
x_3825 = x_3841;
x_3826 = x_3851;
x_3827 = x_3852;
x_3828 = x_3843;
x_3829 = x_3844;
x_3830 = x_3845;
x_3831 = x_3846;
x_3832 = x_3847;
x_3833 = x_3848;
x_3834 = x_3849;
x_3835 = x_3855;
goto block_3839;
}
else
{
lean_object* x_3856; lean_object* x_3857; lean_object* x_3858; lean_object* x_3859; lean_object* x_3860; lean_object* x_3861; lean_object* x_3862; lean_object* x_3863; lean_object* x_3864; 
lean_dec(x_3852);
lean_dec_ref(x_3851);
x_3856 = lean_ctor_get(x_3853, 1);
lean_inc(x_3856);
lean_dec_ref(x_3853);
x_3857 = lean_ctor_get(x_3854, 0);
lean_inc(x_3857);
lean_dec_ref(x_3854);
x_3858 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3844, x_3856);
x_3859 = lean_ctor_get(x_3858, 1);
lean_inc(x_3859);
lean_dec_ref(x_3858);
x_3860 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_3841, x_3857, x_3847, x_3859);
x_3861 = lean_ctor_get(x_3860, 0);
lean_inc(x_3861);
x_3862 = lean_ctor_get(x_3860, 1);
lean_inc(x_3862);
lean_dec_ref(x_3860);
x_3863 = lean_ctor_get(x_3861, 2);
lean_inc_ref(x_3863);
x_3864 = lean_ctor_get(x_3861, 3);
lean_inc(x_3864);
x_3825 = x_3861;
x_3826 = x_3863;
x_3827 = x_3864;
x_3828 = x_3843;
x_3829 = x_3844;
x_3830 = x_3845;
x_3831 = x_3846;
x_3832 = x_3847;
x_3833 = x_3848;
x_3834 = x_3849;
x_3835 = x_3862;
goto block_3839;
}
}
else
{
lean_object* x_3865; lean_object* x_3866; lean_object* x_3867; lean_object* x_3868; 
lean_dec(x_3852);
lean_dec_ref(x_3851);
lean_dec(x_3849);
lean_dec_ref(x_3848);
lean_dec(x_3847);
lean_dec_ref(x_3846);
lean_dec_ref(x_3845);
lean_dec(x_3844);
lean_dec_ref(x_3843);
lean_dec(x_3841);
lean_dec_ref(x_3645);
lean_dec_ref(x_1);
x_3865 = lean_ctor_get(x_3853, 0);
lean_inc(x_3865);
x_3866 = lean_ctor_get(x_3853, 1);
lean_inc(x_3866);
if (lean_is_exclusive(x_3853)) {
 lean_ctor_release(x_3853, 0);
 lean_ctor_release(x_3853, 1);
 x_3867 = x_3853;
} else {
 lean_dec_ref(x_3853);
 x_3867 = lean_box(0);
}
if (lean_is_scalar(x_3867)) {
 x_3868 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3868 = x_3867;
}
lean_ctor_set(x_3868, 0, x_3865);
lean_ctor_set(x_3868, 1, x_3866);
return x_3868;
}
}
block_3872:
{
lean_object* x_3870; lean_object* x_3871; 
x_3870 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_3842);
x_3871 = lean_ctor_get(x_3870, 1);
lean_inc(x_3871);
lean_dec_ref(x_3870);
x_3843 = x_2;
x_3844 = x_3;
x_3845 = x_4;
x_3846 = x_5;
x_3847 = x_6;
x_3848 = x_3643;
x_3849 = x_8;
x_3850 = x_3871;
goto block_3869;
}
}
case 3:
{
lean_object* x_3874; lean_object* x_3875; lean_object* x_3876; lean_object* x_3877; lean_object* x_3878; lean_object* x_3879; lean_object* x_3880; 
lean_dec_ref(x_3567);
x_3874 = lean_ctor_get(x_1, 0);
lean_inc(x_3874);
x_3875 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3875);
x_3876 = lean_st_ref_get(x_3, x_3586);
x_3877 = lean_ctor_get(x_3876, 0);
lean_inc(x_3877);
x_3878 = lean_ctor_get(x_3876, 1);
lean_inc(x_3878);
lean_dec_ref(x_3876);
x_3879 = lean_ctor_get(x_3877, 0);
lean_inc_ref(x_3879);
lean_dec(x_3877);
x_3880 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_3879, x_3874, x_3583);
lean_dec_ref(x_3879);
if (lean_obj_tag(x_3880) == 0)
{
lean_object* x_3881; lean_object* x_3882; lean_object* x_3883; lean_object* x_3884; lean_object* x_3885; lean_object* x_3886; lean_object* x_3890; 
x_3881 = lean_ctor_get(x_3880, 0);
lean_inc(x_3881);
lean_dec_ref(x_3880);
x_3882 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_3583, x_3875, x_3, x_3878);
x_3883 = lean_ctor_get(x_3882, 0);
lean_inc(x_3883);
x_3884 = lean_ctor_get(x_3882, 1);
lean_inc(x_3884);
if (lean_is_exclusive(x_3882)) {
 lean_ctor_release(x_3882, 0);
 lean_ctor_release(x_3882, 1);
 x_3885 = x_3882;
} else {
 lean_dec_ref(x_3882);
 x_3885 = lean_box(0);
}
lean_inc(x_3883);
x_3890 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_3881, x_3883, x_2, x_3, x_4, x_5, x_6, x_3643, x_8, x_3884);
if (lean_obj_tag(x_3890) == 0)
{
lean_object* x_3891; 
x_3891 = lean_ctor_get(x_3890, 0);
lean_inc(x_3891);
if (lean_obj_tag(x_3891) == 0)
{
lean_object* x_3892; lean_object* x_3893; lean_object* x_3894; lean_object* x_3895; lean_object* x_3896; uint8_t x_3897; 
lean_dec_ref(x_3643);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_3892 = lean_ctor_get(x_3890, 1);
lean_inc(x_3892);
lean_dec_ref(x_3890);
lean_inc(x_3881);
x_3893 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_3881, x_3, x_3892);
x_3894 = lean_ctor_get(x_3893, 1);
lean_inc(x_3894);
lean_dec_ref(x_3893);
x_3895 = lean_unsigned_to_nat(0u);
x_3896 = lean_array_get_size(x_3883);
x_3897 = lean_nat_dec_lt(x_3895, x_3896);
if (x_3897 == 0)
{
lean_dec(x_3896);
lean_dec(x_3);
x_3886 = x_3894;
goto block_3889;
}
else
{
uint8_t x_3898; 
x_3898 = lean_nat_dec_le(x_3896, x_3896);
if (x_3898 == 0)
{
lean_dec(x_3896);
lean_dec(x_3);
x_3886 = x_3894;
goto block_3889;
}
else
{
lean_object* x_3899; size_t x_3900; size_t x_3901; lean_object* x_3902; lean_object* x_3903; 
x_3899 = lean_box(0);
x_3900 = 0;
x_3901 = lean_usize_of_nat(x_3896);
lean_dec(x_3896);
x_3902 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_3883, x_3900, x_3901, x_3899, x_3, x_3894);
lean_dec(x_3);
x_3903 = lean_ctor_get(x_3902, 1);
lean_inc(x_3903);
lean_dec_ref(x_3902);
x_3886 = x_3903;
goto block_3889;
}
}
}
else
{
lean_object* x_3904; lean_object* x_3905; 
lean_dec(x_3885);
lean_dec(x_3883);
lean_dec(x_3881);
lean_dec_ref(x_1);
x_3904 = lean_ctor_get(x_3890, 1);
lean_inc(x_3904);
lean_dec_ref(x_3890);
x_3905 = lean_ctor_get(x_3891, 0);
lean_inc(x_3905);
lean_dec_ref(x_3891);
x_1 = x_3905;
x_7 = x_3643;
x_9 = x_3904;
goto _start;
}
}
else
{
lean_object* x_3907; lean_object* x_3908; lean_object* x_3909; lean_object* x_3910; 
lean_dec(x_3885);
lean_dec(x_3883);
lean_dec(x_3881);
lean_dec_ref(x_3643);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3907 = lean_ctor_get(x_3890, 0);
lean_inc(x_3907);
x_3908 = lean_ctor_get(x_3890, 1);
lean_inc(x_3908);
if (lean_is_exclusive(x_3890)) {
 lean_ctor_release(x_3890, 0);
 lean_ctor_release(x_3890, 1);
 x_3909 = x_3890;
} else {
 lean_dec_ref(x_3890);
 x_3909 = lean_box(0);
}
if (lean_is_scalar(x_3909)) {
 x_3910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3910 = x_3909;
}
lean_ctor_set(x_3910, 0, x_3907);
lean_ctor_set(x_3910, 1, x_3908);
return x_3910;
}
block_3889:
{
lean_object* x_3887; lean_object* x_3888; 
x_3887 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_1, x_3881, x_3883);
lean_dec_ref(x_1);
if (lean_is_scalar(x_3885)) {
 x_3888 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3888 = x_3885;
}
lean_ctor_set(x_3888, 0, x_3887);
lean_ctor_set(x_3888, 1, x_3886);
return x_3888;
}
}
else
{
lean_object* x_3911; 
lean_dec_ref(x_3875);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3911 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_3643, x_8, x_3878);
lean_dec(x_8);
lean_dec_ref(x_3643);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_3911;
}
}
case 4:
{
lean_object* x_3912; lean_object* x_3913; 
x_3912 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3912);
lean_inc(x_8);
lean_inc_ref(x_3643);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_3912);
x_3913 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_3912, x_2, x_3, x_4, x_5, x_6, x_3643, x_8, x_3586);
if (lean_obj_tag(x_3913) == 0)
{
lean_object* x_3914; 
x_3914 = lean_ctor_get(x_3913, 0);
lean_inc(x_3914);
if (lean_obj_tag(x_3914) == 0)
{
lean_object* x_3915; lean_object* x_3916; lean_object* x_3917; lean_object* x_3918; lean_object* x_3919; lean_object* x_3920; lean_object* x_3921; lean_object* x_3922; lean_object* x_3923; 
x_3915 = lean_ctor_get(x_3913, 1);
lean_inc(x_3915);
lean_dec_ref(x_3913);
x_3916 = lean_st_ref_get(x_3, x_3915);
x_3917 = lean_ctor_get(x_3916, 0);
lean_inc(x_3917);
x_3918 = lean_ctor_get(x_3916, 1);
lean_inc(x_3918);
lean_dec_ref(x_3916);
x_3919 = lean_ctor_get(x_3912, 1);
lean_inc_ref(x_3919);
x_3920 = lean_ctor_get(x_3912, 2);
lean_inc(x_3920);
x_3921 = lean_ctor_get(x_3912, 3);
lean_inc_ref(x_3921);
lean_dec_ref(x_3912);
x_3922 = lean_ctor_get(x_3917, 0);
lean_inc_ref(x_3922);
lean_dec(x_3917);
x_3923 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_3922, x_3920, x_3583);
lean_dec_ref(x_3922);
if (lean_obj_tag(x_3923) == 0)
{
lean_object* x_3924; lean_object* x_3925; lean_object* x_3926; lean_object* x_3927; lean_object* x_3928; lean_object* x_3929; lean_object* x_3930; lean_object* x_3931; 
x_3924 = lean_ctor_get(x_3923, 0);
lean_inc(x_3924);
lean_dec_ref(x_3923);
x_3925 = lean_st_ref_get(x_3, x_3918);
x_3926 = lean_ctor_get(x_3925, 0);
lean_inc(x_3926);
x_3927 = lean_ctor_get(x_3925, 1);
lean_inc(x_3927);
lean_dec_ref(x_3925);
x_3928 = lean_box(x_3583);
lean_inc(x_3924);
x_3929 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__1___boxed), 11, 2);
lean_closure_set(x_3929, 0, x_3924);
lean_closure_set(x_3929, 1, x_3928);
x_3930 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_3567, x_3921, x_3929);
lean_inc(x_8);
lean_inc_ref(x_3643);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_3931 = lean_apply_8(x_3930, x_2, x_3, x_4, x_5, x_6, x_3643, x_8, x_3927);
if (lean_obj_tag(x_3931) == 0)
{
lean_object* x_3932; lean_object* x_3933; lean_object* x_3934; 
x_3932 = lean_ctor_get(x_3931, 0);
lean_inc(x_3932);
x_3933 = lean_ctor_get(x_3931, 1);
lean_inc(x_3933);
lean_dec_ref(x_3931);
lean_inc(x_6);
lean_inc(x_3);
x_3934 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_3932, x_2, x_3, x_4, x_5, x_6, x_3643, x_8, x_3933);
if (lean_obj_tag(x_3934) == 0)
{
lean_object* x_3935; lean_object* x_3936; lean_object* x_3937; lean_object* x_3938; lean_object* x_3939; lean_object* x_3940; lean_object* x_3941; lean_object* x_3948; uint8_t x_3949; 
x_3935 = lean_ctor_get(x_3934, 0);
lean_inc(x_3935);
x_3936 = lean_ctor_get(x_3934, 1);
lean_inc(x_3936);
if (lean_is_exclusive(x_3934)) {
 lean_ctor_release(x_3934, 0);
 lean_ctor_release(x_3934, 1);
 x_3937 = x_3934;
} else {
 lean_dec_ref(x_3934);
 x_3937 = lean_box(0);
}
x_3938 = lean_ctor_get(x_3926, 0);
lean_inc_ref(x_3938);
lean_dec(x_3926);
x_3939 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_3938, x_3583, x_3919);
lean_dec_ref(x_3938);
x_3948 = lean_array_get_size(x_3935);
x_3949 = lean_nat_dec_eq(x_3948, x_3641);
lean_dec(x_3948);
if (x_3949 == 0)
{
lean_dec(x_3937);
lean_dec(x_6);
x_3940 = x_3;
x_3941 = x_3936;
goto block_3947;
}
else
{
lean_object* x_3950; lean_object* x_3951; 
x_3950 = lean_unsigned_to_nat(0u);
x_3951 = lean_array_fget(x_3935, x_3950);
if (lean_obj_tag(x_3951) == 0)
{
lean_object* x_3952; lean_object* x_3953; lean_object* x_3954; lean_object* x_3960; lean_object* x_3961; uint8_t x_3970; lean_object* x_3971; uint8_t x_3973; 
lean_dec(x_3937);
x_3952 = lean_ctor_get(x_3951, 1);
lean_inc_ref(x_3952);
x_3953 = lean_ctor_get(x_3951, 2);
lean_inc_ref(x_3953);
lean_dec_ref(x_3951);
x_3960 = lean_array_get_size(x_3952);
x_3973 = lean_nat_dec_lt(x_3950, x_3960);
if (x_3973 == 0)
{
x_3970 = x_3583;
x_3971 = x_3936;
goto block_3972;
}
else
{
if (x_3973 == 0)
{
x_3970 = x_3583;
x_3971 = x_3936;
goto block_3972;
}
else
{
size_t x_3974; size_t x_3975; lean_object* x_3976; lean_object* x_3977; lean_object* x_3978; uint8_t x_3979; 
x_3974 = 0;
x_3975 = lean_usize_of_nat(x_3960);
x_3976 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_3952, x_3974, x_3975, x_3, x_3936);
x_3977 = lean_ctor_get(x_3976, 0);
lean_inc(x_3977);
x_3978 = lean_ctor_get(x_3976, 1);
lean_inc(x_3978);
lean_dec_ref(x_3976);
x_3979 = lean_unbox(x_3977);
lean_dec(x_3977);
x_3970 = x_3979;
x_3971 = x_3978;
goto block_3972;
}
}
block_3959:
{
lean_object* x_3955; lean_object* x_3956; lean_object* x_3957; lean_object* x_3958; 
x_3955 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_3954);
lean_dec(x_3);
x_3956 = lean_ctor_get(x_3955, 1);
lean_inc(x_3956);
if (lean_is_exclusive(x_3955)) {
 lean_ctor_release(x_3955, 0);
 lean_ctor_release(x_3955, 1);
 x_3957 = x_3955;
} else {
 lean_dec_ref(x_3955);
 x_3957 = lean_box(0);
}
if (lean_is_scalar(x_3957)) {
 x_3958 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3958 = x_3957;
}
lean_ctor_set(x_3958, 0, x_3953);
lean_ctor_set(x_3958, 1, x_3956);
return x_3958;
}
block_3969:
{
uint8_t x_3962; 
x_3962 = lean_nat_dec_lt(x_3950, x_3960);
if (x_3962 == 0)
{
lean_dec(x_3960);
lean_dec_ref(x_3952);
lean_dec(x_6);
x_3954 = x_3961;
goto block_3959;
}
else
{
uint8_t x_3963; 
x_3963 = lean_nat_dec_le(x_3960, x_3960);
if (x_3963 == 0)
{
lean_dec(x_3960);
lean_dec_ref(x_3952);
lean_dec(x_6);
x_3954 = x_3961;
goto block_3959;
}
else
{
lean_object* x_3964; size_t x_3965; size_t x_3966; lean_object* x_3967; lean_object* x_3968; 
x_3964 = lean_box(0);
x_3965 = 0;
x_3966 = lean_usize_of_nat(x_3960);
lean_dec(x_3960);
x_3967 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_3952, x_3965, x_3966, x_3964, x_6, x_3961);
lean_dec(x_6);
lean_dec_ref(x_3952);
x_3968 = lean_ctor_get(x_3967, 1);
lean_inc(x_3968);
lean_dec_ref(x_3967);
x_3954 = x_3968;
goto block_3959;
}
}
}
block_3972:
{
if (x_3970 == 0)
{
lean_dec_ref(x_3939);
lean_dec(x_3935);
lean_dec(x_3924);
lean_dec_ref(x_1);
x_3961 = x_3971;
goto block_3969;
}
else
{
if (x_3583 == 0)
{
lean_dec(x_3960);
lean_dec_ref(x_3953);
lean_dec_ref(x_3952);
lean_dec(x_6);
x_3940 = x_3;
x_3941 = x_3971;
goto block_3947;
}
else
{
lean_dec_ref(x_3939);
lean_dec(x_3935);
lean_dec(x_3924);
lean_dec_ref(x_1);
x_3961 = x_3971;
goto block_3969;
}
}
}
}
else
{
lean_object* x_3980; lean_object* x_3981; 
lean_dec_ref(x_3939);
lean_dec(x_3935);
lean_dec(x_3924);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_3980 = lean_ctor_get(x_3951, 0);
lean_inc_ref(x_3980);
lean_dec_ref(x_3951);
if (lean_is_scalar(x_3937)) {
 x_3981 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3981 = x_3937;
}
lean_ctor_set(x_3981, 0, x_3980);
lean_ctor_set(x_3981, 1, x_3936);
return x_3981;
}
}
block_3947:
{
lean_object* x_3942; lean_object* x_3943; lean_object* x_3944; lean_object* x_3945; lean_object* x_3946; 
lean_inc(x_3924);
x_3942 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_3924, x_3940, x_3941);
lean_dec(x_3940);
x_3943 = lean_ctor_get(x_3942, 1);
lean_inc(x_3943);
if (lean_is_exclusive(x_3942)) {
 lean_ctor_release(x_3942, 0);
 lean_ctor_release(x_3942, 1);
 x_3944 = x_3942;
} else {
 lean_dec_ref(x_3942);
 x_3944 = lean_box(0);
}
x_3945 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_1, x_3939, x_3924, x_3935);
if (lean_is_scalar(x_3944)) {
 x_3946 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3946 = x_3944;
}
lean_ctor_set(x_3946, 0, x_3945);
lean_ctor_set(x_3946, 1, x_3943);
return x_3946;
}
}
else
{
lean_object* x_3982; lean_object* x_3983; lean_object* x_3984; lean_object* x_3985; 
lean_dec(x_3926);
lean_dec(x_3924);
lean_dec_ref(x_3919);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_3982 = lean_ctor_get(x_3934, 0);
lean_inc(x_3982);
x_3983 = lean_ctor_get(x_3934, 1);
lean_inc(x_3983);
if (lean_is_exclusive(x_3934)) {
 lean_ctor_release(x_3934, 0);
 lean_ctor_release(x_3934, 1);
 x_3984 = x_3934;
} else {
 lean_dec_ref(x_3934);
 x_3984 = lean_box(0);
}
if (lean_is_scalar(x_3984)) {
 x_3985 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3985 = x_3984;
}
lean_ctor_set(x_3985, 0, x_3982);
lean_ctor_set(x_3985, 1, x_3983);
return x_3985;
}
}
else
{
lean_object* x_3986; lean_object* x_3987; lean_object* x_3988; lean_object* x_3989; 
lean_dec(x_3926);
lean_dec(x_3924);
lean_dec_ref(x_3919);
lean_dec_ref(x_3643);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3986 = lean_ctor_get(x_3931, 0);
lean_inc(x_3986);
x_3987 = lean_ctor_get(x_3931, 1);
lean_inc(x_3987);
if (lean_is_exclusive(x_3931)) {
 lean_ctor_release(x_3931, 0);
 lean_ctor_release(x_3931, 1);
 x_3988 = x_3931;
} else {
 lean_dec_ref(x_3931);
 x_3988 = lean_box(0);
}
if (lean_is_scalar(x_3988)) {
 x_3989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3989 = x_3988;
}
lean_ctor_set(x_3989, 0, x_3986);
lean_ctor_set(x_3989, 1, x_3987);
return x_3989;
}
}
else
{
lean_object* x_3990; 
lean_dec_ref(x_3921);
lean_dec_ref(x_3919);
lean_dec_ref(x_3567);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3990 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_3643, x_8, x_3918);
lean_dec(x_8);
lean_dec_ref(x_3643);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_3990;
}
}
else
{
lean_object* x_3991; lean_object* x_3992; lean_object* x_3993; lean_object* x_3994; 
lean_dec_ref(x_3912);
lean_dec_ref(x_3643);
lean_dec_ref(x_3567);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3991 = lean_ctor_get(x_3913, 1);
lean_inc(x_3991);
if (lean_is_exclusive(x_3913)) {
 lean_ctor_release(x_3913, 0);
 lean_ctor_release(x_3913, 1);
 x_3992 = x_3913;
} else {
 lean_dec_ref(x_3913);
 x_3992 = lean_box(0);
}
x_3993 = lean_ctor_get(x_3914, 0);
lean_inc(x_3993);
lean_dec_ref(x_3914);
if (lean_is_scalar(x_3992)) {
 x_3994 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3994 = x_3992;
}
lean_ctor_set(x_3994, 0, x_3993);
lean_ctor_set(x_3994, 1, x_3991);
return x_3994;
}
}
else
{
lean_object* x_3995; lean_object* x_3996; lean_object* x_3997; lean_object* x_3998; 
lean_dec_ref(x_3912);
lean_dec_ref(x_3643);
lean_dec_ref(x_3567);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_3995 = lean_ctor_get(x_3913, 0);
lean_inc(x_3995);
x_3996 = lean_ctor_get(x_3913, 1);
lean_inc(x_3996);
if (lean_is_exclusive(x_3913)) {
 lean_ctor_release(x_3913, 0);
 lean_ctor_release(x_3913, 1);
 x_3997 = x_3913;
} else {
 lean_dec_ref(x_3913);
 x_3997 = lean_box(0);
}
if (lean_is_scalar(x_3997)) {
 x_3998 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3998 = x_3997;
}
lean_ctor_set(x_3998, 0, x_3995);
lean_ctor_set(x_3998, 1, x_3996);
return x_3998;
}
}
case 5:
{
lean_object* x_3999; lean_object* x_4000; lean_object* x_4001; lean_object* x_4002; lean_object* x_4003; lean_object* x_4004; 
lean_dec_ref(x_3567);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_3999 = lean_ctor_get(x_1, 0);
lean_inc(x_3999);
x_4000 = lean_st_ref_get(x_3, x_3586);
x_4001 = lean_ctor_get(x_4000, 0);
lean_inc(x_4001);
x_4002 = lean_ctor_get(x_4000, 1);
lean_inc(x_4002);
lean_dec_ref(x_4000);
x_4003 = lean_ctor_get(x_4001, 0);
lean_inc_ref(x_4003);
lean_dec(x_4001);
x_4004 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_4003, x_3999, x_3583);
lean_dec_ref(x_4003);
if (lean_obj_tag(x_4004) == 0)
{
lean_object* x_4005; lean_object* x_4006; lean_object* x_4007; lean_object* x_4008; lean_object* x_4009; lean_object* x_4010; 
lean_dec_ref(x_3643);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_4005 = lean_ctor_get(x_4004, 0);
lean_inc(x_4005);
lean_dec_ref(x_4004);
lean_inc(x_4005);
x_4006 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_4005, x_3, x_4002);
lean_dec(x_3);
x_4007 = lean_ctor_get(x_4006, 1);
lean_inc(x_4007);
if (lean_is_exclusive(x_4006)) {
 lean_ctor_release(x_4006, 0);
 lean_ctor_release(x_4006, 1);
 x_4008 = x_4006;
} else {
 lean_dec_ref(x_4006);
 x_4008 = lean_box(0);
}
x_4009 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_1, x_4005);
if (lean_is_scalar(x_4008)) {
 x_4010 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4010 = x_4008;
}
lean_ctor_set(x_4010, 0, x_4009);
lean_ctor_set(x_4010, 1, x_4007);
return x_4010;
}
else
{
lean_object* x_4011; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_4011 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_3643, x_8, x_4002);
lean_dec(x_8);
lean_dec_ref(x_3643);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_4011;
}
}
case 6:
{
lean_object* x_4012; lean_object* x_4013; lean_object* x_4014; lean_object* x_4015; lean_object* x_4016; lean_object* x_4017; lean_object* x_4018; lean_object* x_4019; lean_object* x_4020; 
lean_dec_ref(x_3643);
lean_dec_ref(x_3567);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_4012 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4012);
x_4013 = lean_st_ref_get(x_3, x_3586);
lean_dec(x_3);
x_4014 = lean_ctor_get(x_4013, 0);
lean_inc(x_4014);
x_4015 = lean_ctor_get(x_4013, 1);
lean_inc(x_4015);
if (lean_is_exclusive(x_4013)) {
 lean_ctor_release(x_4013, 0);
 lean_ctor_release(x_4013, 1);
 x_4016 = x_4013;
} else {
 lean_dec_ref(x_4013);
 x_4016 = lean_box(0);
}
x_4017 = lean_ctor_get(x_4014, 0);
lean_inc_ref(x_4017);
lean_dec(x_4014);
x_4018 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_4017, x_3583, x_4012);
lean_dec_ref(x_4017);
x_4019 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(x_1, x_4018);
if (lean_is_scalar(x_4016)) {
 x_4020 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4020 = x_4016;
}
lean_ctor_set(x_4020, 0, x_4019);
lean_ctor_set(x_4020, 1, x_4015);
return x_4020;
}
default: 
{
lean_object* x_4021; lean_object* x_4022; 
lean_dec_ref(x_3567);
x_4021 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4021);
x_4022 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4022);
x_3587 = x_4021;
x_3588 = x_4022;
x_3589 = x_2;
x_3590 = x_3;
x_3591 = x_4;
x_3592 = x_5;
x_3593 = x_6;
x_3594 = x_3643;
x_3595 = x_8;
goto block_3640;
}
}
block_3640:
{
lean_object* x_3596; lean_object* x_3597; lean_object* x_3598; lean_object* x_3599; lean_object* x_3600; lean_object* x_3601; lean_object* x_3602; uint8_t x_3603; 
x_3596 = lean_ctor_get(x_3587, 0);
lean_inc(x_3596);
x_3597 = lean_ctor_get(x_3587, 2);
lean_inc_ref(x_3597);
x_3598 = lean_ctor_get(x_3587, 3);
lean_inc_ref(x_3598);
x_3599 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_3596, x_3590, x_3586);
lean_dec(x_3596);
x_3600 = lean_ctor_get(x_3599, 0);
lean_inc(x_3600);
x_3601 = lean_ctor_get(x_3599, 1);
lean_inc(x_3601);
lean_dec_ref(x_3599);
lean_inc(x_3600);
lean_inc_ref(x_1);
lean_inc_ref(x_3588);
x_3602 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_3602, 0, x_3588);
lean_closure_set(x_3602, 1, x_1);
lean_closure_set(x_3602, 2, x_3600);
x_3603 = lean_unbox(x_3600);
if (x_3603 == 0)
{
uint8_t x_3604; 
lean_dec(x_3600);
lean_dec_ref(x_3588);
x_3604 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec_ref(x_1);
if (x_3604 == 0)
{
lean_dec_ref(x_3598);
lean_dec_ref(x_3597);
x_10 = x_3602;
x_11 = x_3587;
x_12 = x_3589;
x_13 = x_3590;
x_14 = x_3591;
x_15 = x_3592;
x_16 = x_3593;
x_17 = x_3594;
x_18 = x_3595;
x_19 = x_3601;
goto block_29;
}
else
{
uint8_t x_3605; 
x_3605 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_3598, x_3597);
lean_dec_ref(x_3597);
if (x_3605 == 0)
{
x_10 = x_3602;
x_11 = x_3587;
x_12 = x_3589;
x_13 = x_3590;
x_14 = x_3591;
x_15 = x_3592;
x_16 = x_3593;
x_17 = x_3594;
x_18 = x_3595;
x_19 = x_3601;
goto block_29;
}
else
{
lean_object* x_3606; lean_object* x_3607; lean_object* x_3608; lean_object* x_3609; lean_object* x_3610; 
x_3606 = lean_st_ref_get(x_3590, x_3601);
x_3607 = lean_ctor_get(x_3606, 0);
lean_inc(x_3607);
x_3608 = lean_ctor_get(x_3606, 1);
lean_inc(x_3608);
lean_dec_ref(x_3606);
x_3609 = lean_ctor_get(x_3607, 0);
lean_inc_ref(x_3609);
lean_dec(x_3607);
lean_inc(x_3595);
lean_inc_ref(x_3594);
lean_inc(x_3593);
lean_inc_ref(x_3592);
x_3610 = l_Lean_Compiler_LCNF_normFunDeclImp(x_3583, x_3587, x_3609, x_3592, x_3593, x_3594, x_3595, x_3608);
if (lean_obj_tag(x_3610) == 0)
{
lean_object* x_3611; lean_object* x_3612; lean_object* x_3613; 
x_3611 = lean_ctor_get(x_3610, 0);
lean_inc(x_3611);
x_3612 = lean_ctor_get(x_3610, 1);
lean_inc(x_3612);
lean_dec_ref(x_3610);
lean_inc(x_3595);
lean_inc_ref(x_3594);
lean_inc(x_3593);
lean_inc_ref(x_3592);
x_3613 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_3611, x_3592, x_3593, x_3594, x_3595, x_3612);
if (lean_obj_tag(x_3613) == 0)
{
lean_object* x_3614; lean_object* x_3615; lean_object* x_3616; lean_object* x_3617; 
x_3614 = lean_ctor_get(x_3613, 0);
lean_inc(x_3614);
x_3615 = lean_ctor_get(x_3613, 1);
lean_inc(x_3615);
lean_dec_ref(x_3613);
x_3616 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3590, x_3615);
x_3617 = lean_ctor_get(x_3616, 1);
lean_inc(x_3617);
lean_dec_ref(x_3616);
x_10 = x_3602;
x_11 = x_3614;
x_12 = x_3589;
x_13 = x_3590;
x_14 = x_3591;
x_15 = x_3592;
x_16 = x_3593;
x_17 = x_3594;
x_18 = x_3595;
x_19 = x_3617;
goto block_29;
}
else
{
lean_object* x_3618; lean_object* x_3619; lean_object* x_3620; lean_object* x_3621; 
lean_dec_ref(x_3602);
lean_dec(x_3595);
lean_dec_ref(x_3594);
lean_dec(x_3593);
lean_dec_ref(x_3592);
lean_dec_ref(x_3591);
lean_dec(x_3590);
lean_dec_ref(x_3589);
x_3618 = lean_ctor_get(x_3613, 0);
lean_inc(x_3618);
x_3619 = lean_ctor_get(x_3613, 1);
lean_inc(x_3619);
if (lean_is_exclusive(x_3613)) {
 lean_ctor_release(x_3613, 0);
 lean_ctor_release(x_3613, 1);
 x_3620 = x_3613;
} else {
 lean_dec_ref(x_3613);
 x_3620 = lean_box(0);
}
if (lean_is_scalar(x_3620)) {
 x_3621 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3621 = x_3620;
}
lean_ctor_set(x_3621, 0, x_3618);
lean_ctor_set(x_3621, 1, x_3619);
return x_3621;
}
}
else
{
lean_object* x_3622; lean_object* x_3623; lean_object* x_3624; lean_object* x_3625; 
lean_dec_ref(x_3602);
lean_dec(x_3595);
lean_dec_ref(x_3594);
lean_dec(x_3593);
lean_dec_ref(x_3592);
lean_dec_ref(x_3591);
lean_dec(x_3590);
lean_dec_ref(x_3589);
x_3622 = lean_ctor_get(x_3610, 0);
lean_inc(x_3622);
x_3623 = lean_ctor_get(x_3610, 1);
lean_inc(x_3623);
if (lean_is_exclusive(x_3610)) {
 lean_ctor_release(x_3610, 0);
 lean_ctor_release(x_3610, 1);
 x_3624 = x_3610;
} else {
 lean_dec_ref(x_3610);
 x_3624 = lean_box(0);
}
if (lean_is_scalar(x_3624)) {
 x_3625 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3625 = x_3624;
}
lean_ctor_set(x_3625, 0, x_3622);
lean_ctor_set(x_3625, 1, x_3623);
return x_3625;
}
}
}
}
else
{
lean_object* x_3626; lean_object* x_3627; lean_object* x_3628; lean_object* x_3629; lean_object* x_3630; 
lean_dec_ref(x_3602);
lean_dec_ref(x_3598);
lean_dec_ref(x_3597);
x_3626 = lean_st_ref_get(x_3590, x_3601);
x_3627 = lean_ctor_get(x_3626, 0);
lean_inc(x_3627);
x_3628 = lean_ctor_get(x_3626, 1);
lean_inc(x_3628);
lean_dec_ref(x_3626);
x_3629 = lean_ctor_get(x_3627, 0);
lean_inc_ref(x_3629);
lean_dec(x_3627);
lean_inc(x_3595);
lean_inc_ref(x_3594);
lean_inc(x_3593);
lean_inc_ref(x_3592);
x_3630 = l_Lean_Compiler_LCNF_normFunDeclImp(x_3583, x_3587, x_3629, x_3592, x_3593, x_3594, x_3595, x_3628);
if (lean_obj_tag(x_3630) == 0)
{
lean_object* x_3631; lean_object* x_3632; lean_object* x_3633; uint8_t x_3634; lean_object* x_3635; 
x_3631 = lean_ctor_get(x_3630, 0);
lean_inc(x_3631);
x_3632 = lean_ctor_get(x_3630, 1);
lean_inc(x_3632);
lean_dec_ref(x_3630);
x_3633 = lean_box(0);
x_3634 = lean_unbox(x_3600);
lean_dec(x_3600);
x_3635 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_3588, x_1, x_3634, x_3631, x_3633, x_3589, x_3590, x_3591, x_3592, x_3593, x_3594, x_3595, x_3632);
lean_dec_ref(x_1);
return x_3635;
}
else
{
lean_object* x_3636; lean_object* x_3637; lean_object* x_3638; lean_object* x_3639; 
lean_dec(x_3600);
lean_dec(x_3595);
lean_dec_ref(x_3594);
lean_dec(x_3593);
lean_dec_ref(x_3592);
lean_dec_ref(x_3591);
lean_dec(x_3590);
lean_dec_ref(x_3589);
lean_dec_ref(x_3588);
lean_dec_ref(x_1);
x_3636 = lean_ctor_get(x_3630, 0);
lean_inc(x_3636);
x_3637 = lean_ctor_get(x_3630, 1);
lean_inc(x_3637);
if (lean_is_exclusive(x_3630)) {
 lean_ctor_release(x_3630, 0);
 lean_ctor_release(x_3630, 1);
 x_3638 = x_3630;
} else {
 lean_dec_ref(x_3630);
 x_3638 = lean_box(0);
}
if (lean_is_scalar(x_3638)) {
 x_3639 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3639 = x_3638;
}
lean_ctor_set(x_3639, 0, x_3636);
lean_ctor_set(x_3639, 1, x_3637);
return x_3639;
}
}
}
}
else
{
lean_object* x_4023; 
lean_dec_ref(x_3582);
lean_dec(x_3580);
lean_dec(x_3578);
lean_dec(x_3577);
lean_dec(x_3576);
lean_dec(x_3575);
lean_dec(x_3574);
lean_dec(x_3573);
lean_dec(x_3572);
lean_dec(x_3571);
lean_dec(x_3570);
lean_dec_ref(x_3569);
lean_dec_ref(x_3568);
lean_dec_ref(x_3567);
lean_dec_ref(x_1);
x_4023 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_4023;
}
}
block_29:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_20 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_box(0);
x_24 = lean_apply_10(x_10, x_21, x_23, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_15 = lean_ctor_get(x_4, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = lean_st_ref_take(x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 3);
lean_inc_ref(x_24);
x_25 = lean_ctor_get_uint8(x_19, sizeof(void*)*7);
x_26 = lean_ctor_get(x_19, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_19, 5);
lean_inc(x_27);
x_28 = lean_ctor_get(x_19, 6);
lean_inc(x_28);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 x_29 = x_19;
} else {
 lean_dec_ref(x_19);
 x_29 = lean_box(0);
}
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; uint8_t x_60; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
x_33 = lean_array_uget(x_1, x_3);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_array_fget(x_9, x_10);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_10, x_36);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_37);
x_46 = lean_array_get_size(x_32);
x_47 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_34);
x_48 = 32;
x_49 = lean_uint64_shift_right(x_47, x_48);
x_50 = lean_uint64_xor(x_47, x_49);
x_51 = 16;
x_52 = lean_uint64_shift_right(x_50, x_51);
x_53 = lean_uint64_xor(x_50, x_52);
x_54 = lean_uint64_to_usize(x_53);
x_55 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_56 = 1;
x_57 = lean_usize_sub(x_55, x_56);
x_58 = lean_usize_land(x_54, x_57);
x_59 = lean_array_uget(x_32, x_58);
x_60 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_34, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_61 = lean_nat_add(x_31, x_36);
lean_dec(x_31);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_34);
lean_ctor_set(x_62, 1, x_35);
lean_ctor_set(x_62, 2, x_59);
x_63 = lean_array_uset(x_32, x_58, x_62);
x_64 = lean_unsigned_to_nat(4u);
x_65 = lean_nat_mul(x_61, x_64);
x_66 = lean_unsigned_to_nat(3u);
x_67 = lean_nat_div(x_65, x_66);
lean_dec(x_65);
x_68 = lean_array_get_size(x_63);
x_69 = lean_nat_dec_le(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_63);
lean_ctor_set(x_20, 1, x_70);
lean_ctor_set(x_20, 0, x_61);
x_38 = x_20;
goto block_45;
}
else
{
lean_ctor_set(x_20, 1, x_63);
lean_ctor_set(x_20, 0, x_61);
x_38 = x_20;
goto block_45;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_box(0);
x_72 = lean_array_uset(x_32, x_58, x_71);
x_73 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_34, x_35, x_59);
x_74 = lean_array_uset(x_72, x_58, x_73);
lean_ctor_set(x_20, 1, x_74);
x_38 = x_20;
goto block_45;
}
block_45:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
if (lean_is_scalar(x_29)) {
 x_39 = lean_alloc_ctor(0, 7, 1);
} else {
 x_39 = x_29;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_22);
lean_ctor_set(x_39, 2, x_23);
lean_ctor_set(x_39, 3, x_24);
lean_ctor_set(x_39, 4, x_26);
lean_ctor_set(x_39, 5, x_27);
lean_ctor_set(x_39, 6, x_28);
lean_ctor_set_uint8(x_39, sizeof(void*)*7, x_25);
x_40 = lean_st_ref_set(x_5, x_39, x_21);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = 1;
x_43 = lean_usize_add(x_3, x_42);
x_3 = x_43;
x_6 = x_41;
goto _start;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; size_t x_98; size_t x_99; size_t x_100; size_t x_101; size_t x_102; lean_object* x_103; uint8_t x_104; 
x_75 = lean_ctor_get(x_20, 0);
x_76 = lean_ctor_get(x_20, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_20);
x_77 = lean_array_uget(x_1, x_3);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_array_fget(x_9, x_10);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_10, x_80);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_81);
x_90 = lean_array_get_size(x_76);
x_91 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_78);
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
x_103 = lean_array_uget(x_76, x_102);
x_104 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_78, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_105 = lean_nat_add(x_75, x_80);
lean_dec(x_75);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_78);
lean_ctor_set(x_106, 1, x_79);
lean_ctor_set(x_106, 2, x_103);
x_107 = lean_array_uset(x_76, x_102, x_106);
x_108 = lean_unsigned_to_nat(4u);
x_109 = lean_nat_mul(x_105, x_108);
x_110 = lean_unsigned_to_nat(3u);
x_111 = lean_nat_div(x_109, x_110);
lean_dec(x_109);
x_112 = lean_array_get_size(x_107);
x_113 = lean_nat_dec_le(x_111, x_112);
lean_dec(x_112);
lean_dec(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_107);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_105);
lean_ctor_set(x_115, 1, x_114);
x_82 = x_115;
goto block_89;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_105);
lean_ctor_set(x_116, 1, x_107);
x_82 = x_116;
goto block_89;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_box(0);
x_118 = lean_array_uset(x_76, x_102, x_117);
x_119 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_78, x_79, x_103);
x_120 = lean_array_uset(x_118, x_102, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_75);
lean_ctor_set(x_121, 1, x_120);
x_82 = x_121;
goto block_89;
}
block_89:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; 
if (lean_is_scalar(x_29)) {
 x_83 = lean_alloc_ctor(0, 7, 1);
} else {
 x_83 = x_29;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_22);
lean_ctor_set(x_83, 2, x_23);
lean_ctor_set(x_83, 3, x_24);
lean_ctor_set(x_83, 4, x_26);
lean_ctor_set(x_83, 5, x_27);
lean_ctor_set(x_83, 6, x_28);
lean_ctor_set_uint8(x_83, sizeof(void*)*7, x_25);
x_84 = lean_st_ref_set(x_5, x_83, x_21);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = 1;
x_87 = lean_usize_add(x_3, x_86);
x_3 = x_87;
x_6 = x_85;
goto _start;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_151; uint64_t x_152; uint64_t x_153; uint64_t x_154; uint64_t x_155; uint64_t x_156; uint64_t x_157; uint64_t x_158; size_t x_159; size_t x_160; size_t x_161; size_t x_162; size_t x_163; lean_object* x_164; uint8_t x_165; 
lean_dec(x_4);
x_122 = lean_st_ref_take(x_5, x_6);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 0);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec_ref(x_122);
x_126 = lean_ctor_get(x_123, 1);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_123, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 3);
lean_inc_ref(x_128);
x_129 = lean_ctor_get_uint8(x_123, sizeof(void*)*7);
x_130 = lean_ctor_get(x_123, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_123, 5);
lean_inc(x_131);
x_132 = lean_ctor_get(x_123, 6);
lean_inc(x_132);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 lean_ctor_release(x_123, 6);
 x_133 = x_123;
} else {
 lean_dec_ref(x_123);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_124, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_124, 1);
lean_inc_ref(x_135);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_136 = x_124;
} else {
 lean_dec_ref(x_124);
 x_136 = lean_box(0);
}
x_137 = lean_array_uget(x_1, x_3);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = lean_array_fget(x_9, x_10);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_add(x_10, x_140);
lean_dec(x_10);
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_9);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_11);
x_151 = lean_array_get_size(x_135);
x_152 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1562_(x_138);
x_153 = 32;
x_154 = lean_uint64_shift_right(x_152, x_153);
x_155 = lean_uint64_xor(x_152, x_154);
x_156 = 16;
x_157 = lean_uint64_shift_right(x_155, x_156);
x_158 = lean_uint64_xor(x_155, x_157);
x_159 = lean_uint64_to_usize(x_158);
x_160 = lean_usize_of_nat(x_151);
lean_dec(x_151);
x_161 = 1;
x_162 = lean_usize_sub(x_160, x_161);
x_163 = lean_usize_land(x_159, x_162);
x_164 = lean_array_uget(x_135, x_163);
x_165 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_138, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_166 = lean_nat_add(x_134, x_140);
lean_dec(x_134);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_138);
lean_ctor_set(x_167, 1, x_139);
lean_ctor_set(x_167, 2, x_164);
x_168 = lean_array_uset(x_135, x_163, x_167);
x_169 = lean_unsigned_to_nat(4u);
x_170 = lean_nat_mul(x_166, x_169);
x_171 = lean_unsigned_to_nat(3u);
x_172 = lean_nat_div(x_170, x_171);
lean_dec(x_170);
x_173 = lean_array_get_size(x_168);
x_174 = lean_nat_dec_le(x_172, x_173);
lean_dec(x_173);
lean_dec(x_172);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_168);
if (lean_is_scalar(x_136)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_136;
}
lean_ctor_set(x_176, 0, x_166);
lean_ctor_set(x_176, 1, x_175);
x_143 = x_176;
goto block_150;
}
else
{
lean_object* x_177; 
if (lean_is_scalar(x_136)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_136;
}
lean_ctor_set(x_177, 0, x_166);
lean_ctor_set(x_177, 1, x_168);
x_143 = x_177;
goto block_150;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_178 = lean_box(0);
x_179 = lean_array_uset(x_135, x_163, x_178);
x_180 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__4___redArg(x_138, x_139, x_164);
x_181 = lean_array_uset(x_179, x_163, x_180);
if (lean_is_scalar(x_136)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_136;
}
lean_ctor_set(x_182, 0, x_134);
lean_ctor_set(x_182, 1, x_181);
x_143 = x_182;
goto block_150;
}
block_150:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; size_t x_147; size_t x_148; 
if (lean_is_scalar(x_133)) {
 x_144 = lean_alloc_ctor(0, 7, 1);
} else {
 x_144 = x_133;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_126);
lean_ctor_set(x_144, 2, x_127);
lean_ctor_set(x_144, 3, x_128);
lean_ctor_set(x_144, 4, x_130);
lean_ctor_set(x_144, 5, x_131);
lean_ctor_set(x_144, 6, x_132);
lean_ctor_set_uint8(x_144, sizeof(void*)*7, x_129);
x_145 = lean_st_ref_set(x_5, x_144, x_125);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = 1;
x_148 = lean_usize_add(x_3, x_147);
x_3 = x_148;
x_4 = x_142;
x_6 = x_146;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_12);
return x_13;
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
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
x_15 = 0;
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_14, x_13, x_15);
lean_dec_ref(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_18, x_4, x_6, x_8, x_12);
lean_dec(x_18);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
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
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
lean_ctor_set_tag(x_16, 4);
lean_ctor_set(x_16, 0, x_33);
x_34 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_16, x_6, x_27);
lean_dec_ref(x_16);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_35);
if (lean_obj_tag(x_32) == 0)
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_32, 2);
lean_inc_ref(x_39);
lean_dec_ref(x_32);
x_40 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_41);
lean_dec_ref(x_28);
x_64 = lean_ctor_get(x_40, 3);
lean_inc(x_64);
lean_dec_ref(x_40);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_array_get_size(x_41);
x_67 = lean_nat_dec_le(x_64, x_65);
if (x_67 == 0)
{
x_42 = x_64;
x_43 = x_66;
goto block_63;
}
else
{
lean_dec(x_64);
x_42 = x_65;
x_43 = x_66;
goto block_63;
}
block_63:
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l_Array_toSubarray___redArg(x_41, x_42, x_43);
x_45 = lean_array_size(x_38);
x_46 = 0;
x_47 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_38, x_45, x_46, x_44, x_3, x_37);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc(x_6);
x_49 = l_Lean_Compiler_LCNF_Simp_simp(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_38, x_6, x_51);
lean_dec(x_6);
lean_dec_ref(x_38);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
if (lean_is_scalar(x_29)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_29;
}
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
if (lean_is_scalar(x_29)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_29;
}
lean_ctor_set(x_57, 0, x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_38);
lean_dec(x_29);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_49);
if (x_59 == 0)
{
return x_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_36);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_36, 1);
x_70 = lean_ctor_get(x_36, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_32, 2);
lean_inc_ref(x_72);
lean_dec_ref(x_32);
x_73 = !lean_is_exclusive(x_28);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_28, 0);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_eq(x_74, x_75);
if (x_76 == 1)
{
lean_object* x_77; 
lean_free_object(x_28);
lean_dec(x_74);
lean_dec_ref(x_71);
lean_free_object(x_36);
x_77 = l_Lean_Compiler_LCNF_Simp_simp(x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
if (lean_is_scalar(x_29)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_29;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_77);
if (lean_is_scalar(x_29)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_29;
}
lean_ctor_set(x_83, 0, x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_29);
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_77, 0);
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_77);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_sub(x_74, x_89);
lean_dec(x_74);
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_90);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_28);
x_92 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_93 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_91, x_92, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_97 = lean_array_get(x_96, x_71, x_75);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
x_100 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_98, x_99, x_3, x_6, x_7, x_8, x_95);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec_ref(x_100);
lean_inc(x_6);
x_102 = l_Lean_Compiler_LCNF_Simp_simp(x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_71, x_6, x_104);
lean_dec(x_6);
lean_dec_ref(x_71);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 0);
lean_dec(x_107);
lean_ctor_set(x_36, 1, x_103);
lean_ctor_set(x_36, 0, x_94);
if (lean_is_scalar(x_29)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_29;
}
lean_ctor_set(x_108, 0, x_36);
lean_ctor_set(x_105, 0, x_108);
return x_105;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
lean_ctor_set(x_36, 1, x_103);
lean_ctor_set(x_36, 0, x_94);
if (lean_is_scalar(x_29)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_29;
}
lean_ctor_set(x_110, 0, x_36);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
uint8_t x_112; 
lean_dec(x_94);
lean_dec_ref(x_71);
lean_free_object(x_36);
lean_dec(x_29);
lean_dec(x_6);
x_112 = !lean_is_exclusive(x_102);
if (x_112 == 0)
{
return x_102;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_102, 0);
x_114 = lean_ctor_get(x_102, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_102);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_94);
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_free_object(x_36);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_116 = !lean_is_exclusive(x_100);
if (x_116 == 0)
{
return x_100;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_100, 0);
x_118 = lean_ctor_get(x_100, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_100);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_free_object(x_36);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_120 = !lean_is_exclusive(x_93);
if (x_120 == 0)
{
return x_93;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_93, 0);
x_122 = lean_ctor_get(x_93, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_93);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = lean_ctor_get(x_28, 0);
lean_inc(x_124);
lean_dec(x_28);
x_125 = lean_unsigned_to_nat(0u);
x_126 = lean_nat_dec_eq(x_124, x_125);
if (x_126 == 1)
{
lean_object* x_127; 
lean_dec(x_124);
lean_dec_ref(x_71);
lean_free_object(x_36);
x_127 = l_Lean_Compiler_LCNF_Simp_simp(x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_131 = lean_alloc_ctor(1, 1, 0);
} else {
 x_131 = x_29;
}
lean_ctor_set(x_131, 0, x_128);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_29);
x_133 = lean_ctor_get(x_127, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_135 = x_127;
} else {
 lean_dec_ref(x_127);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_sub(x_124, x_137);
lean_dec(x_124);
x_139 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_142 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_140, x_141, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec_ref(x_142);
x_145 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_146 = lean_array_get(x_145, x_71, x_125);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = lean_ctor_get(x_143, 0);
lean_inc(x_148);
x_149 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_147, x_148, x_3, x_6, x_7, x_8, x_144);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec_ref(x_149);
lean_inc(x_6);
x_151 = l_Lean_Compiler_LCNF_Simp_simp(x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec_ref(x_151);
x_154 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_71, x_6, x_153);
lean_dec(x_6);
lean_dec_ref(x_71);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
lean_ctor_set(x_36, 1, x_152);
lean_ctor_set(x_36, 0, x_143);
if (lean_is_scalar(x_29)) {
 x_157 = lean_alloc_ctor(1, 1, 0);
} else {
 x_157 = x_29;
}
lean_ctor_set(x_157, 0, x_36);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_143);
lean_dec_ref(x_71);
lean_free_object(x_36);
lean_dec(x_29);
lean_dec(x_6);
x_159 = lean_ctor_get(x_151, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_151, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_161 = x_151;
} else {
 lean_dec_ref(x_151);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_143);
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_free_object(x_36);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_163 = lean_ctor_get(x_149, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_149, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_165 = x_149;
} else {
 lean_dec_ref(x_149);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_free_object(x_36);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_167 = lean_ctor_get(x_142, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_142, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_169 = x_142;
} else {
 lean_dec_ref(x_142);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_171 = lean_ctor_get(x_36, 1);
lean_inc(x_171);
lean_dec(x_36);
x_172 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_32, 2);
lean_inc_ref(x_173);
lean_dec_ref(x_32);
x_174 = lean_ctor_get(x_28, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_175 = x_28;
} else {
 lean_dec_ref(x_28);
 x_175 = lean_box(0);
}
x_176 = lean_unsigned_to_nat(0u);
x_177 = lean_nat_dec_eq(x_174, x_176);
if (x_177 == 1)
{
lean_object* x_178; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec_ref(x_172);
x_178 = l_Lean_Compiler_LCNF_Simp_simp(x_173, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_171);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_29;
}
lean_ctor_set(x_182, 0, x_179);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_29);
x_184 = lean_ctor_get(x_178, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_178, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_186 = x_178;
} else {
 lean_dec_ref(x_178);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_unsigned_to_nat(1u);
x_189 = lean_nat_sub(x_174, x_188);
lean_dec(x_174);
if (lean_is_scalar(x_175)) {
 x_190 = lean_alloc_ctor(0, 1, 0);
} else {
 x_190 = x_175;
 lean_ctor_set_tag(x_190, 0);
}
lean_ctor_set(x_190, 0, x_189);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_193 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_191, x_192, x_5, x_6, x_7, x_8, x_171);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec_ref(x_193);
x_196 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_197 = lean_array_get(x_196, x_172, x_176);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec_ref(x_197);
x_199 = lean_ctor_get(x_194, 0);
lean_inc(x_199);
x_200 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_198, x_199, x_3, x_6, x_7, x_8, x_195);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec_ref(x_200);
lean_inc(x_6);
x_202 = l_Lean_Compiler_LCNF_Simp_simp(x_173, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_201);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec_ref(x_202);
x_205 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_172, x_6, x_204);
lean_dec(x_6);
lean_dec_ref(x_172);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_207 = x_205;
} else {
 lean_dec_ref(x_205);
 x_207 = lean_box(0);
}
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_194);
lean_ctor_set(x_208, 1, x_203);
if (lean_is_scalar(x_29)) {
 x_209 = lean_alloc_ctor(1, 1, 0);
} else {
 x_209 = x_29;
}
lean_ctor_set(x_209, 0, x_208);
if (lean_is_scalar(x_207)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_207;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_206);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_194);
lean_dec_ref(x_172);
lean_dec(x_29);
lean_dec(x_6);
x_211 = lean_ctor_get(x_202, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_202, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_213 = x_202;
} else {
 lean_dec_ref(x_202);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_194);
lean_dec_ref(x_173);
lean_dec_ref(x_172);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_215 = lean_ctor_get(x_200, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_200, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_217 = x_200;
} else {
 lean_dec_ref(x_200);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec_ref(x_173);
lean_dec_ref(x_172);
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_219 = lean_ctor_get(x_193, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_193, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_221 = x_193;
} else {
 lean_dec_ref(x_193);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_28);
x_223 = lean_ctor_get(x_36, 1);
lean_inc(x_223);
lean_dec_ref(x_36);
x_224 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_224);
lean_dec_ref(x_32);
x_225 = l_Lean_Compiler_LCNF_Simp_simp(x_224, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_223);
if (lean_obj_tag(x_225) == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 0);
if (lean_is_scalar(x_29)) {
 x_228 = lean_alloc_ctor(1, 1, 0);
} else {
 x_228 = x_29;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_225, 0, x_228);
return x_225;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_225, 0);
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_225);
if (lean_is_scalar(x_29)) {
 x_231 = lean_alloc_ctor(1, 1, 0);
} else {
 x_231 = x_29;
}
lean_ctor_set(x_231, 0, x_229);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
else
{
uint8_t x_233; 
lean_dec(x_29);
x_233 = !lean_is_exclusive(x_225);
if (x_233 == 0)
{
return x_225;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_225, 0);
x_235 = lean_ctor_get(x_225, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_225);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_16, 0);
lean_inc(x_237);
lean_dec(x_16);
x_238 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_237, x_4, x_6, x_8, x_12);
lean_dec(x_237);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
x_242 = lean_box(0);
if (lean_is_scalar(x_241)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_241;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_240);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_244 = lean_ctor_get(x_238, 1);
lean_inc(x_244);
lean_dec_ref(x_238);
x_245 = lean_ctor_get(x_239, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_246 = x_239;
} else {
 lean_dec_ref(x_239);
 x_246 = lean_box(0);
}
x_247 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_245);
x_248 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_247);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec_ref(x_248);
x_251 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_251, 0, x_250);
x_252 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_251, x_6, x_244);
lean_dec_ref(x_251);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_253);
if (lean_obj_tag(x_249) == 0)
{
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = lean_ctor_get(x_249, 1);
lean_inc_ref(x_256);
x_257 = lean_ctor_get(x_249, 2);
lean_inc_ref(x_257);
lean_dec_ref(x_249);
x_258 = lean_ctor_get(x_245, 0);
lean_inc_ref(x_258);
x_259 = lean_ctor_get(x_245, 1);
lean_inc_ref(x_259);
lean_dec_ref(x_245);
x_280 = lean_ctor_get(x_258, 3);
lean_inc(x_280);
lean_dec_ref(x_258);
x_281 = lean_unsigned_to_nat(0u);
x_282 = lean_array_get_size(x_259);
x_283 = lean_nat_dec_le(x_280, x_281);
if (x_283 == 0)
{
x_260 = x_280;
x_261 = x_282;
goto block_279;
}
else
{
lean_dec(x_280);
x_260 = x_281;
x_261 = x_282;
goto block_279;
}
block_279:
{
lean_object* x_262; size_t x_263; size_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_262 = l_Array_toSubarray___redArg(x_259, x_260, x_261);
x_263 = lean_array_size(x_256);
x_264 = 0;
x_265 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_256, x_263, x_264, x_262, x_3, x_255);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec_ref(x_265);
lean_inc(x_6);
x_267 = l_Lean_Compiler_LCNF_Simp_simp(x_257, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec_ref(x_267);
x_270 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_256, x_6, x_269);
lean_dec(x_6);
lean_dec_ref(x_256);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_273 = lean_alloc_ctor(1, 1, 0);
} else {
 x_273 = x_246;
}
lean_ctor_set(x_273, 0, x_268);
if (lean_is_scalar(x_272)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_272;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_271);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec_ref(x_256);
lean_dec(x_246);
lean_dec(x_6);
x_275 = lean_ctor_get(x_267, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_267, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_277 = x_267;
} else {
 lean_dec_ref(x_267);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_284 = lean_ctor_get(x_254, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_285 = x_254;
} else {
 lean_dec_ref(x_254);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_249, 1);
lean_inc_ref(x_286);
x_287 = lean_ctor_get(x_249, 2);
lean_inc_ref(x_287);
lean_dec_ref(x_249);
x_288 = lean_ctor_get(x_245, 0);
lean_inc(x_288);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 x_289 = x_245;
} else {
 lean_dec_ref(x_245);
 x_289 = lean_box(0);
}
x_290 = lean_unsigned_to_nat(0u);
x_291 = lean_nat_dec_eq(x_288, x_290);
if (x_291 == 1)
{
lean_object* x_292; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec_ref(x_286);
lean_dec(x_285);
x_292 = l_Lean_Compiler_LCNF_Simp_simp(x_287, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_284);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_295 = x_292;
} else {
 lean_dec_ref(x_292);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_296 = lean_alloc_ctor(1, 1, 0);
} else {
 x_296 = x_246;
}
lean_ctor_set(x_296, 0, x_293);
if (lean_is_scalar(x_295)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_295;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_294);
return x_297;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_246);
x_298 = lean_ctor_get(x_292, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_292, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_300 = x_292;
} else {
 lean_dec_ref(x_292);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_302 = lean_unsigned_to_nat(1u);
x_303 = lean_nat_sub(x_288, x_302);
lean_dec(x_288);
if (lean_is_scalar(x_289)) {
 x_304 = lean_alloc_ctor(0, 1, 0);
} else {
 x_304 = x_289;
 lean_ctor_set_tag(x_304, 0);
}
lean_ctor_set(x_304, 0, x_303);
x_305 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_305, 0, x_304);
x_306 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_307 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_305, x_306, x_5, x_6, x_7, x_8, x_284);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec_ref(x_307);
x_310 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_311 = lean_array_get(x_310, x_286, x_290);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
lean_dec_ref(x_311);
x_313 = lean_ctor_get(x_308, 0);
lean_inc(x_313);
x_314 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_312, x_313, x_3, x_6, x_7, x_8, x_309);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
lean_dec_ref(x_314);
lean_inc(x_6);
x_316 = l_Lean_Compiler_LCNF_Simp_simp(x_287, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_315);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec_ref(x_316);
x_319 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_286, x_6, x_318);
lean_dec(x_6);
lean_dec_ref(x_286);
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_321 = x_319;
} else {
 lean_dec_ref(x_319);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_285;
}
lean_ctor_set(x_322, 0, x_308);
lean_ctor_set(x_322, 1, x_317);
if (lean_is_scalar(x_246)) {
 x_323 = lean_alloc_ctor(1, 1, 0);
} else {
 x_323 = x_246;
}
lean_ctor_set(x_323, 0, x_322);
if (lean_is_scalar(x_321)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_321;
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_320);
return x_324;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_308);
lean_dec_ref(x_286);
lean_dec(x_285);
lean_dec(x_246);
lean_dec(x_6);
x_325 = lean_ctor_get(x_316, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_316, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_327 = x_316;
} else {
 lean_dec_ref(x_316);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_308);
lean_dec_ref(x_287);
lean_dec_ref(x_286);
lean_dec(x_285);
lean_dec(x_246);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_329 = lean_ctor_get(x_314, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_314, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_331 = x_314;
} else {
 lean_dec_ref(x_314);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec_ref(x_287);
lean_dec_ref(x_286);
lean_dec(x_285);
lean_dec(x_246);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_333 = lean_ctor_get(x_307, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_307, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_335 = x_307;
} else {
 lean_dec_ref(x_307);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_245);
x_337 = lean_ctor_get(x_254, 1);
lean_inc(x_337);
lean_dec_ref(x_254);
x_338 = lean_ctor_get(x_249, 0);
lean_inc_ref(x_338);
lean_dec_ref(x_249);
x_339 = l_Lean_Compiler_LCNF_Simp_simp(x_338, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_337);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_342 = x_339;
} else {
 lean_dec_ref(x_339);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_343 = lean_alloc_ctor(1, 1, 0);
} else {
 x_343 = x_246;
}
lean_ctor_set(x_343, 0, x_340);
if (lean_is_scalar(x_342)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_342;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_341);
return x_344;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_246);
x_345 = lean_ctor_get(x_339, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_339, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_347 = x_339;
} else {
 lean_dec_ref(x_339);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_346);
return x_348;
}
}
}
}
}
else
{
lean_object* x_349; uint8_t x_350; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_349 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_349, 0, x_352);
return x_349;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_353 = lean_ctor_get(x_349, 0);
x_354 = lean_ctor_get(x_349, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_349);
x_355 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_355, 0, x_353);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
return x_356;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_11);
x_12 = lean_st_ref_get(x_4, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_15, x_1, x_11);
lean_dec_ref(x_15);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(x_2, x_16, x_6, x_7, x_8, x_9, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Compiler_LCNF_Simp_simp___closed__1;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 4);
x_20 = lean_ctor_get(x_13, 1);
lean_dec(x_20);
x_21 = l_Lean_Compiler_LCNF_Simp_simp___closed__2;
x_22 = l_Lean_Compiler_LCNF_Simp_simp___closed__3;
lean_inc_ref(x_16);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_19);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_18);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_17);
lean_ctor_set(x_13, 4, x_26);
lean_ctor_set(x_13, 3, x_27);
lean_ctor_set(x_13, 2, x_28);
lean_ctor_set(x_13, 1, x_21);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_11, 1, x_22);
x_29 = l_ReaderT_instMonad___redArg(x_11);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_38 = lean_ctor_get(x_31, 1);
lean_dec(x_38);
x_39 = l_Lean_Compiler_LCNF_Simp_simp___closed__4;
x_40 = l_Lean_Compiler_LCNF_Simp_simp___closed__5;
lean_inc_ref(x_34);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_36);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_46, 0, x_35);
lean_ctor_set(x_31, 4, x_44);
lean_ctor_set(x_31, 3, x_45);
lean_ctor_set(x_31, 2, x_46);
lean_ctor_set(x_31, 1, x_39);
lean_ctor_set(x_31, 0, x_43);
lean_ctor_set(x_29, 1, x_40);
x_47 = l_ReaderT_instMonad___redArg(x_29);
x_48 = l_ReaderT_instMonad___redArg(x_47);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_50, 2);
x_55 = lean_ctor_get(x_50, 3);
x_56 = lean_ctor_get(x_50, 4);
x_57 = lean_ctor_get(x_50, 1);
lean_dec(x_57);
x_58 = lean_box(x_1);
x_59 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0___boxed), 10, 1);
lean_closure_set(x_59, 0, x_58);
x_60 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_61 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_53);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_62, 0, x_53);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_63, 0, x_53);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_65, 0, x_56);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_66, 0, x_55);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_67, 0, x_54);
lean_ctor_set(x_50, 4, x_65);
lean_ctor_set(x_50, 3, x_66);
lean_ctor_set(x_50, 2, x_67);
lean_ctor_set(x_50, 1, x_60);
lean_ctor_set(x_50, 0, x_64);
lean_ctor_set(x_48, 1, x_61);
x_68 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_48, x_2, x_59);
x_69 = lean_apply_8(x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_70 = lean_ctor_get(x_50, 0);
x_71 = lean_ctor_get(x_50, 2);
x_72 = lean_ctor_get(x_50, 3);
x_73 = lean_ctor_get(x_50, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_50);
x_74 = lean_box(x_1);
x_75 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0___boxed), 10, 1);
lean_closure_set(x_75, 0, x_74);
x_76 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_77 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_70);
x_78 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_78, 0, x_70);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_79, 0, x_70);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_81, 0, x_73);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_82, 0, x_72);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_83, 0, x_71);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_76);
lean_ctor_set(x_84, 2, x_83);
lean_ctor_set(x_84, 3, x_82);
lean_ctor_set(x_84, 4, x_81);
lean_ctor_set(x_48, 1, x_77);
lean_ctor_set(x_48, 0, x_84);
x_85 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_48, x_2, x_75);
x_86 = lean_apply_8(x_85, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_87 = lean_ctor_get(x_48, 0);
lean_inc(x_87);
lean_dec(x_48);
x_88 = lean_ctor_get(x_87, 0);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_87, 2);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_87, 3);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_87, 4);
lean_inc_ref(x_91);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 lean_ctor_release(x_87, 4);
 x_92 = x_87;
} else {
 lean_dec_ref(x_87);
 x_92 = lean_box(0);
}
x_93 = lean_box(x_1);
x_94 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0___boxed), 10, 1);
lean_closure_set(x_94, 0, x_93);
x_95 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_96 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_88);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_97, 0, x_88);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_98, 0, x_88);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_100, 0, x_91);
x_101 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_101, 0, x_90);
x_102 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_102, 0, x_89);
if (lean_is_scalar(x_92)) {
 x_103 = lean_alloc_ctor(0, 5, 0);
} else {
 x_103 = x_92;
}
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_95);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set(x_103, 4, x_100);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_96);
x_105 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_104, x_2, x_94);
x_106 = lean_apply_8(x_105, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_107 = lean_ctor_get(x_31, 0);
x_108 = lean_ctor_get(x_31, 2);
x_109 = lean_ctor_get(x_31, 3);
x_110 = lean_ctor_get(x_31, 4);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_31);
x_111 = l_Lean_Compiler_LCNF_Simp_simp___closed__4;
x_112 = l_Lean_Compiler_LCNF_Simp_simp___closed__5;
lean_inc_ref(x_107);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_113, 0, x_107);
x_114 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_114, 0, x_107);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_116, 0, x_110);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_117, 0, x_109);
x_118 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_118, 0, x_108);
x_119 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_119, 3, x_117);
lean_ctor_set(x_119, 4, x_116);
lean_ctor_set(x_29, 1, x_112);
lean_ctor_set(x_29, 0, x_119);
x_120 = l_ReaderT_instMonad___redArg(x_29);
x_121 = l_ReaderT_instMonad___redArg(x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc_ref(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_122, 0);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_122, 2);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_122, 3);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_122, 4);
lean_inc_ref(x_127);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 x_128 = x_122;
} else {
 lean_dec_ref(x_122);
 x_128 = lean_box(0);
}
x_129 = lean_box(x_1);
x_130 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0___boxed), 10, 1);
lean_closure_set(x_130, 0, x_129);
x_131 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_132 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_124);
x_133 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_133, 0, x_124);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_134, 0, x_124);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_136, 0, x_127);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_137, 0, x_126);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_138, 0, x_125);
if (lean_is_scalar(x_128)) {
 x_139 = lean_alloc_ctor(0, 5, 0);
} else {
 x_139 = x_128;
}
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_137);
lean_ctor_set(x_139, 4, x_136);
if (lean_is_scalar(x_123)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_123;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_132);
x_141 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_140, x_2, x_130);
x_142 = lean_apply_8(x_141, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_143 = lean_ctor_get(x_29, 0);
lean_inc(x_143);
lean_dec(x_29);
x_144 = lean_ctor_get(x_143, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_143, 2);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_143, 3);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_143, 4);
lean_inc_ref(x_147);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 x_148 = x_143;
} else {
 lean_dec_ref(x_143);
 x_148 = lean_box(0);
}
x_149 = l_Lean_Compiler_LCNF_Simp_simp___closed__4;
x_150 = l_Lean_Compiler_LCNF_Simp_simp___closed__5;
lean_inc_ref(x_144);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_151, 0, x_144);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_152, 0, x_144);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_154, 0, x_147);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_155, 0, x_146);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_156, 0, x_145);
if (lean_is_scalar(x_148)) {
 x_157 = lean_alloc_ctor(0, 5, 0);
} else {
 x_157 = x_148;
}
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_155);
lean_ctor_set(x_157, 4, x_154);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_150);
x_159 = l_ReaderT_instMonad___redArg(x_158);
x_160 = l_ReaderT_instMonad___redArg(x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_161, 0);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_161, 2);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_161, 3);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_161, 4);
lean_inc_ref(x_166);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 x_167 = x_161;
} else {
 lean_dec_ref(x_161);
 x_167 = lean_box(0);
}
x_168 = lean_box(x_1);
x_169 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0___boxed), 10, 1);
lean_closure_set(x_169, 0, x_168);
x_170 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_171 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_163);
x_172 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_172, 0, x_163);
x_173 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_173, 0, x_163);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_175, 0, x_166);
x_176 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_176, 0, x_165);
x_177 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_177, 0, x_164);
if (lean_is_scalar(x_167)) {
 x_178 = lean_alloc_ctor(0, 5, 0);
} else {
 x_178 = x_167;
}
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_170);
lean_ctor_set(x_178, 2, x_177);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set(x_178, 4, x_175);
if (lean_is_scalar(x_162)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_162;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_171);
x_180 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_179, x_2, x_169);
x_181 = lean_apply_8(x_180, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_182 = lean_ctor_get(x_13, 0);
x_183 = lean_ctor_get(x_13, 2);
x_184 = lean_ctor_get(x_13, 3);
x_185 = lean_ctor_get(x_13, 4);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_13);
x_186 = l_Lean_Compiler_LCNF_Simp_simp___closed__2;
x_187 = l_Lean_Compiler_LCNF_Simp_simp___closed__3;
lean_inc_ref(x_182);
x_188 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_188, 0, x_182);
x_189 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_189, 0, x_182);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_191, 0, x_185);
x_192 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_192, 0, x_184);
x_193 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_193, 0, x_183);
x_194 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_194, 0, x_190);
lean_ctor_set(x_194, 1, x_186);
lean_ctor_set(x_194, 2, x_193);
lean_ctor_set(x_194, 3, x_192);
lean_ctor_set(x_194, 4, x_191);
lean_ctor_set(x_11, 1, x_187);
lean_ctor_set(x_11, 0, x_194);
x_195 = l_ReaderT_instMonad___redArg(x_11);
x_196 = lean_ctor_get(x_195, 0);
lean_inc_ref(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_196, 0);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc_ref(x_199);
x_200 = lean_ctor_get(x_196, 3);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_196, 4);
lean_inc_ref(x_201);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 x_202 = x_196;
} else {
 lean_dec_ref(x_196);
 x_202 = lean_box(0);
}
x_203 = l_Lean_Compiler_LCNF_Simp_simp___closed__4;
x_204 = l_Lean_Compiler_LCNF_Simp_simp___closed__5;
lean_inc_ref(x_198);
x_205 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_205, 0, x_198);
x_206 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_206, 0, x_198);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_208, 0, x_201);
x_209 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_209, 0, x_200);
x_210 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_210, 0, x_199);
if (lean_is_scalar(x_202)) {
 x_211 = lean_alloc_ctor(0, 5, 0);
} else {
 x_211 = x_202;
}
lean_ctor_set(x_211, 0, x_207);
lean_ctor_set(x_211, 1, x_203);
lean_ctor_set(x_211, 2, x_210);
lean_ctor_set(x_211, 3, x_209);
lean_ctor_set(x_211, 4, x_208);
if (lean_is_scalar(x_197)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_197;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_204);
x_213 = l_ReaderT_instMonad___redArg(x_212);
x_214 = l_ReaderT_instMonad___redArg(x_213);
x_215 = lean_ctor_get(x_214, 0);
lean_inc_ref(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_215, 0);
lean_inc_ref(x_217);
x_218 = lean_ctor_get(x_215, 2);
lean_inc_ref(x_218);
x_219 = lean_ctor_get(x_215, 3);
lean_inc_ref(x_219);
x_220 = lean_ctor_get(x_215, 4);
lean_inc_ref(x_220);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 lean_ctor_release(x_215, 2);
 lean_ctor_release(x_215, 3);
 lean_ctor_release(x_215, 4);
 x_221 = x_215;
} else {
 lean_dec_ref(x_215);
 x_221 = lean_box(0);
}
x_222 = lean_box(x_1);
x_223 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0___boxed), 10, 1);
lean_closure_set(x_223, 0, x_222);
x_224 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_225 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_217);
x_226 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_226, 0, x_217);
x_227 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_227, 0, x_217);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_229, 0, x_220);
x_230 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_230, 0, x_219);
x_231 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_231, 0, x_218);
if (lean_is_scalar(x_221)) {
 x_232 = lean_alloc_ctor(0, 5, 0);
} else {
 x_232 = x_221;
}
lean_ctor_set(x_232, 0, x_228);
lean_ctor_set(x_232, 1, x_224);
lean_ctor_set(x_232, 2, x_231);
lean_ctor_set(x_232, 3, x_230);
lean_ctor_set(x_232, 4, x_229);
if (lean_is_scalar(x_216)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_216;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_225);
x_234 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_233, x_2, x_223);
x_235 = lean_apply_8(x_234, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_236 = lean_ctor_get(x_11, 0);
lean_inc(x_236);
lean_dec(x_11);
x_237 = lean_ctor_get(x_236, 0);
lean_inc_ref(x_237);
x_238 = lean_ctor_get(x_236, 2);
lean_inc_ref(x_238);
x_239 = lean_ctor_get(x_236, 3);
lean_inc_ref(x_239);
x_240 = lean_ctor_get(x_236, 4);
lean_inc_ref(x_240);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 lean_ctor_release(x_236, 3);
 lean_ctor_release(x_236, 4);
 x_241 = x_236;
} else {
 lean_dec_ref(x_236);
 x_241 = lean_box(0);
}
x_242 = l_Lean_Compiler_LCNF_Simp_simp___closed__2;
x_243 = l_Lean_Compiler_LCNF_Simp_simp___closed__3;
lean_inc_ref(x_237);
x_244 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_244, 0, x_237);
x_245 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_245, 0, x_237);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_247, 0, x_240);
x_248 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_248, 0, x_239);
x_249 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_249, 0, x_238);
if (lean_is_scalar(x_241)) {
 x_250 = lean_alloc_ctor(0, 5, 0);
} else {
 x_250 = x_241;
}
lean_ctor_set(x_250, 0, x_246);
lean_ctor_set(x_250, 1, x_242);
lean_ctor_set(x_250, 2, x_249);
lean_ctor_set(x_250, 3, x_248);
lean_ctor_set(x_250, 4, x_247);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_243);
x_252 = l_ReaderT_instMonad___redArg(x_251);
x_253 = lean_ctor_get(x_252, 0);
lean_inc_ref(x_253);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_254 = x_252;
} else {
 lean_dec_ref(x_252);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_253, 0);
lean_inc_ref(x_255);
x_256 = lean_ctor_get(x_253, 2);
lean_inc_ref(x_256);
x_257 = lean_ctor_get(x_253, 3);
lean_inc_ref(x_257);
x_258 = lean_ctor_get(x_253, 4);
lean_inc_ref(x_258);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 lean_ctor_release(x_253, 2);
 lean_ctor_release(x_253, 3);
 lean_ctor_release(x_253, 4);
 x_259 = x_253;
} else {
 lean_dec_ref(x_253);
 x_259 = lean_box(0);
}
x_260 = l_Lean_Compiler_LCNF_Simp_simp___closed__4;
x_261 = l_Lean_Compiler_LCNF_Simp_simp___closed__5;
lean_inc_ref(x_255);
x_262 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_262, 0, x_255);
x_263 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_263, 0, x_255);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_265, 0, x_258);
x_266 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_266, 0, x_257);
x_267 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_267, 0, x_256);
if (lean_is_scalar(x_259)) {
 x_268 = lean_alloc_ctor(0, 5, 0);
} else {
 x_268 = x_259;
}
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_260);
lean_ctor_set(x_268, 2, x_267);
lean_ctor_set(x_268, 3, x_266);
lean_ctor_set(x_268, 4, x_265);
if (lean_is_scalar(x_254)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_254;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_261);
x_270 = l_ReaderT_instMonad___redArg(x_269);
x_271 = l_ReaderT_instMonad___redArg(x_270);
x_272 = lean_ctor_get(x_271, 0);
lean_inc_ref(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_272, 0);
lean_inc_ref(x_274);
x_275 = lean_ctor_get(x_272, 2);
lean_inc_ref(x_275);
x_276 = lean_ctor_get(x_272, 3);
lean_inc_ref(x_276);
x_277 = lean_ctor_get(x_272, 4);
lean_inc_ref(x_277);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 lean_ctor_release(x_272, 4);
 x_278 = x_272;
} else {
 lean_dec_ref(x_272);
 x_278 = lean_box(0);
}
x_279 = lean_box(x_1);
x_280 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0___boxed), 10, 1);
lean_closure_set(x_280, 0, x_279);
x_281 = l_Lean_Compiler_LCNF_Simp_simp___closed__6;
x_282 = l_Lean_Compiler_LCNF_Simp_simp___closed__7;
lean_inc_ref(x_274);
x_283 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_283, 0, x_274);
x_284 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_284, 0, x_274);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_286, 0, x_277);
x_287 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_287, 0, x_276);
x_288 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_288, 0, x_275);
if (lean_is_scalar(x_278)) {
 x_289 = lean_alloc_ctor(0, 5, 0);
} else {
 x_289 = x_278;
}
lean_ctor_set(x_289, 0, x_285);
lean_ctor_set(x_289, 1, x_281);
lean_ctor_set(x_289, 2, x_288);
lean_ctor_set(x_289, 3, x_287);
lean_ctor_set(x_289, 4, x_286);
if (lean_is_scalar(x_273)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_273;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_282);
x_291 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_box(0), lean_box(0), x_290, x_2, x_280);
x_292 = lean_apply_8(x_291, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_292;
}
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
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_15);
x_16 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_17 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_16, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
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
x_24 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_23, x_16, x_14);
lean_dec_ref(x_23);
x_25 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_24, x_18, x_21, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_15);
lean_dec_ref(x_14);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__2(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__4(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lean_Compiler_LCNF_Simp_simp___lam__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___lam__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__8 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__8);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__9 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__9);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__10 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__10);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__11 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__11);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__12 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__12);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__13 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__13);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__14 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__14);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__15 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__15);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__16 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__16);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__17 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__17);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__18 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__18);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__19 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__19);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__20 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__20);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__21);
l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0);
l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__4);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__5);
l_Lean_Compiler_LCNF_Simp_simp___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__0);
l_Lean_Compiler_LCNF_Simp_simp___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__1);
l_Lean_Compiler_LCNF_Simp_simp___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__2);
l_Lean_Compiler_LCNF_Simp_simp___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__3);
l_Lean_Compiler_LCNF_Simp_simp___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__4);
l_Lean_Compiler_LCNF_Simp_simp___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__5);
l_Lean_Compiler_LCNF_Simp_simp___closed__6 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__6);
l_Lean_Compiler_LCNF_Simp_simp___closed__7 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
