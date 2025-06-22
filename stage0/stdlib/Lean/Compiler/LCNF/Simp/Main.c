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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__0;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__0;
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt;
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
lean_object* l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
size_t lean_ptr_addr(lean_object*);
uint8_t l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2068_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1208_(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_hasLocalInst(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__1;
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_1 = x_2;
goto _start;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_1 = x_4;
goto _start;
}
case 4:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Compiler_LCNF_instInhabitedAlt;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_7, x_12);
lean_dec(x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_1 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_1 = x_16;
goto _start;
}
}
}
case 5:
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_1);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
return x_19;
}
default: 
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
return x_21;
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_15 = x_4;
} else {
 lean_dec_ref(x_4);
 x_15 = lean_box(0);
}
x_16 = lean_array_uget(x_12, x_3);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_18, x_14, x_10, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Compiler_LCNF_mkAuxParam(x_20, x_23, x_5, x_6, x_7, x_8, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_array_push(x_13, x_25);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_30);
x_39 = lean_array_get_size(x_29);
x_40 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_17);
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
x_52 = lean_array_uget(x_29, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_17, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_28, x_54);
lean_dec(x_28);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_17);
lean_ctor_set(x_56, 1, x_38);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_29, x_51, x_56);
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
lean_object* x_64; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_57);
lean_ctor_set(x_14, 1, x_64);
lean_ctor_set(x_14, 0, x_55);
x_32 = x_14;
goto block_37;
}
else
{
lean_ctor_set(x_14, 1, x_57);
lean_ctor_set(x_14, 0, x_55);
x_32 = x_14;
goto block_37;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_box(0);
x_66 = lean_array_uset(x_29, x_51, x_65);
x_67 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_17, x_38, x_52);
x_68 = lean_array_uset(x_66, x_51, x_67);
lean_ctor_set(x_14, 1, x_68);
x_32 = x_14;
goto block_37;
}
block_37:
{
lean_object* x_33; size_t x_34; size_t x_35; 
if (lean_is_scalar(x_15)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_15;
}
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_3 = x_35;
x_4 = x_33;
x_9 = x_26;
goto _start;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_79; lean_object* x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; size_t x_88; size_t x_89; size_t x_90; size_t x_91; size_t x_92; lean_object* x_93; uint8_t x_94; 
x_69 = lean_ctor_get(x_14, 0);
x_70 = lean_ctor_get(x_14, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_14);
x_71 = lean_ctor_get(x_25, 0);
lean_inc(x_71);
x_72 = lean_array_push(x_13, x_25);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_71);
x_80 = lean_array_get_size(x_70);
x_81 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_17);
x_82 = 32;
x_83 = lean_uint64_shift_right(x_81, x_82);
x_84 = lean_uint64_xor(x_81, x_83);
x_85 = 16;
x_86 = lean_uint64_shift_right(x_84, x_85);
x_87 = lean_uint64_xor(x_84, x_86);
x_88 = lean_uint64_to_usize(x_87);
x_89 = lean_usize_of_nat(x_80);
lean_dec(x_80);
x_90 = 1;
x_91 = lean_usize_sub(x_89, x_90);
x_92 = lean_usize_land(x_88, x_91);
x_93 = lean_array_uget(x_70, x_92);
x_94 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_17, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_69, x_95);
lean_dec(x_69);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_17);
lean_ctor_set(x_97, 1, x_79);
lean_ctor_set(x_97, 2, x_93);
x_98 = lean_array_uset(x_70, x_92, x_97);
x_99 = lean_unsigned_to_nat(4u);
x_100 = lean_nat_mul(x_96, x_99);
x_101 = lean_unsigned_to_nat(3u);
x_102 = lean_nat_div(x_100, x_101);
lean_dec(x_100);
x_103 = lean_array_get_size(x_98);
x_104 = lean_nat_dec_le(x_102, x_103);
lean_dec(x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_98);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_105);
x_73 = x_106;
goto block_78;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_96);
lean_ctor_set(x_107, 1, x_98);
x_73 = x_107;
goto block_78;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_box(0);
x_109 = lean_array_uset(x_70, x_92, x_108);
x_110 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_17, x_79, x_93);
x_111 = lean_array_uset(x_109, x_92, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_69);
lean_ctor_set(x_112, 1, x_111);
x_73 = x_112;
goto block_78;
}
block_78:
{
lean_object* x_74; size_t x_75; size_t x_76; 
if (lean_is_scalar(x_15)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_15;
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = 1;
x_76 = lean_usize_add(x_3, x_75);
x_3 = x_76;
x_4 = x_74;
x_9 = x_26;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_3, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_14);
return x_15;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
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
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(x_10, x_18, x_19, x_17, x_9);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_array_get_size(x_10);
x_26 = l_Array_toSubarray___redArg(x_10, x_15, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 2);
lean_inc(x_28);
x_29 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
lean_ctor_set(x_21, 0, x_29);
x_30 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_26, x_30, x_31, x_21, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Lean_Compiler_LCNF_Code_internalize(x_11, x_36, x_5, x_6, x_7, x_8, x_34);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
lean_inc(x_38);
x_42 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_38, x_41, x_3, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_45 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_35, x_38, x_44, x_5, x_6, x_7, x_8, x_43);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_38);
lean_dec(x_35);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_dec(x_21);
x_51 = lean_array_get_size(x_10);
x_52 = l_Array_toSubarray___redArg(x_10, x_15, x_51);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 2);
lean_inc(x_54);
x_55 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
x_57 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_58 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_59 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_52, x_57, x_58, x_56, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_52);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l_Lean_Compiler_LCNF_Code_internalize(x_11, x_63, x_5, x_6, x_7, x_8, x_61);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(0);
x_68 = lean_unbox(x_67);
lean_inc(x_65);
x_69 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_65, x_68, x_3, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_72 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_62, x_65, x_71, x_5, x_6, x_7, x_8, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_65);
lean_dec(x_62);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
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
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_2);
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
lean_dec(x_11);
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
lean_dec(x_2);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_21, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_21, 4);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_box(0);
x_37 = lean_unbox(x_36);
x_38 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_34, x_35, x_2, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
lean_dec(x_34);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_ctor_set(x_12, 0, x_40);
lean_ctor_set(x_38, 0, x_12);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
lean_ctor_set(x_12, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_free_object(x_12);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_12, 0);
lean_inc(x_48);
lean_dec(x_12);
x_49 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_48, x_4, x_6, x_19);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_48);
lean_dec(x_2);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_48, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_48, 4);
lean_inc(x_60);
lean_dec(x_48);
x_61 = lean_box(0);
x_62 = lean_unbox(x_61);
x_63 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_59, x_60, x_2, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_58);
lean_dec(x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_inc(x_15);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
lean_inc(x_17);
x_27 = l_Lean_Environment_find_x3f(x_24, x_17, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = lean_box(0);
lean_ctor_set(x_20, 0, x_28);
return x_20;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = l_Lean_ConstantInfo_type(x_30);
lean_dec(x_30);
x_32 = l_Lean_Compiler_LCNF_hasLocalInst(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_free_object(x_27);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_20, 0, x_33);
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_41; 
lean_free_object(x_20);
x_34 = l_Lean_Meta_isInstance___redArg(x_17, x_7, x_23);
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
x_41 = lean_unbox(x_35);
lean_dec(x_35);
if (x_41 == 0)
{
if (x_32 == 0)
{
lean_free_object(x_27);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
goto block_40;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_37);
lean_inc(x_17);
x_42 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7, x_36);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_free_object(x_27);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_42, 1);
x_52 = lean_ctor_get(x_42, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = lean_array_get_size(x_19);
x_56 = l_Lean_Compiler_LCNF_Decl_getArity(x_54);
lean_dec(x_54);
x_57 = lean_nat_dec_lt(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; 
lean_free_object(x_43);
lean_free_object(x_27);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_58 = lean_box(0);
lean_ctor_set(x_42, 0, x_58);
return x_42;
}
else
{
lean_object* x_59; uint8_t x_60; 
lean_free_object(x_42);
x_59 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_51);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = lean_array_size(x_61);
x_64 = 0;
lean_inc(x_61);
x_65 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_63, x_64, x_61);
x_66 = l_Array_append___redArg(x_19, x_65);
lean_dec(x_65);
lean_ctor_set(x_13, 2, x_66);
x_67 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_68 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_67, x_4, x_5, x_6, x_7, x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 0, x_71);
lean_ctor_set(x_59, 1, x_27);
lean_ctor_set(x_59, 0, x_69);
x_72 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_73 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_61, x_59, x_72, x_4, x_5, x_6, x_7, x_70);
lean_dec(x_4);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_76, x_3, x_5, x_6, x_7, x_75);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_78);
lean_dec(x_5);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_43, 0, x_74);
lean_ctor_set(x_79, 0, x_43);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
lean_ctor_set(x_43, 0, x_74);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_43);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_74);
lean_free_object(x_43);
lean_dec(x_5);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_77);
if (x_84 == 0)
{
return x_77;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_77, 0);
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_77);
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
lean_free_object(x_43);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_73);
if (x_88 == 0)
{
return x_73;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_73, 0);
x_90 = lean_ctor_get(x_73, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_73);
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
lean_free_object(x_59);
lean_dec(x_61);
lean_free_object(x_43);
lean_free_object(x_27);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_68);
if (x_92 == 0)
{
return x_68;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_68, 0);
x_94 = lean_ctor_get(x_68, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_68);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_59, 0);
x_97 = lean_ctor_get(x_59, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_59);
x_98 = lean_array_size(x_96);
x_99 = 0;
lean_inc(x_96);
x_100 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_98, x_99, x_96);
x_101 = l_Array_append___redArg(x_19, x_100);
lean_dec(x_100);
lean_ctor_set(x_13, 2, x_101);
x_102 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_103 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_102, x_4, x_5, x_6, x_7, x_97);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 0, x_106);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_27);
x_108 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_109 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_96, x_107, x_108, x_4, x_5, x_6, x_7, x_105);
lean_dec(x_4);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_112, x_3, x_5, x_6, x_7, x_111);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_114);
lean_dec(x_5);
lean_dec(x_1);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_110);
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_43);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_110);
lean_free_object(x_43);
lean_dec(x_5);
lean_dec(x_1);
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_free_object(x_43);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_123 = lean_ctor_get(x_109, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_109, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_125 = x_109;
} else {
 lean_dec_ref(x_109);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_96);
lean_free_object(x_43);
lean_free_object(x_27);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_127 = lean_ctor_get(x_103, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_103, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_129 = x_103;
} else {
 lean_dec_ref(x_103);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_43, 0);
lean_inc(x_131);
lean_dec(x_43);
x_132 = lean_array_get_size(x_19);
x_133 = l_Lean_Compiler_LCNF_Decl_getArity(x_131);
lean_dec(x_131);
x_134 = lean_nat_dec_lt(x_132, x_133);
lean_dec(x_133);
lean_dec(x_132);
if (x_134 == 0)
{
lean_object* x_135; 
lean_free_object(x_27);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_135 = lean_box(0);
lean_ctor_set(x_42, 0, x_135);
return x_42;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; size_t x_140; size_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_free_object(x_42);
x_136 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_51);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = lean_array_size(x_137);
x_141 = 0;
lean_inc(x_137);
x_142 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_140, x_141, x_137);
x_143 = l_Array_append___redArg(x_19, x_142);
lean_dec(x_142);
lean_ctor_set(x_13, 2, x_143);
x_144 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_145 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_144, x_4, x_5, x_6, x_7, x_138);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 0, x_148);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_27);
x_150 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_151 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_137, x_149, x_150, x_4, x_5, x_6, x_7, x_147);
lean_dec(x_4);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
x_155 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_154, x_3, x_5, x_6, x_7, x_153);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_156);
lean_dec(x_5);
lean_dec(x_1);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_152);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_152);
lean_dec(x_5);
lean_dec(x_1);
x_162 = lean_ctor_get(x_155, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_155, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_164 = x_155;
} else {
 lean_dec_ref(x_155);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_166 = lean_ctor_get(x_151, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_151, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_168 = x_151;
} else {
 lean_dec_ref(x_151);
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
lean_dec(x_139);
lean_dec(x_137);
lean_free_object(x_27);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_170 = lean_ctor_get(x_145, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_145, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_172 = x_145;
} else {
 lean_dec_ref(x_145);
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
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_174 = lean_ctor_get(x_42, 1);
lean_inc(x_174);
lean_dec(x_42);
x_175 = lean_ctor_get(x_43, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_176 = x_43;
} else {
 lean_dec_ref(x_43);
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
lean_free_object(x_27);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_174);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; size_t x_186; size_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_182 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_174);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
x_186 = lean_array_size(x_183);
x_187 = 0;
lean_inc(x_183);
x_188 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_186, x_187, x_183);
x_189 = l_Array_append___redArg(x_19, x_188);
lean_dec(x_188);
lean_ctor_set(x_13, 2, x_189);
x_190 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_191 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_190, x_4, x_5, x_6, x_7, x_184);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 0, x_194);
if (lean_is_scalar(x_185)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_185;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_27);
x_196 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_197 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_183, x_195, x_196, x_4, x_5, x_6, x_7, x_193);
lean_dec(x_4);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_200, x_3, x_5, x_6, x_7, x_199);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_203 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_202);
lean_dec(x_5);
lean_dec(x_1);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_205 = x_203;
} else {
 lean_dec_ref(x_203);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_206 = lean_alloc_ctor(1, 1, 0);
} else {
 x_206 = x_176;
}
lean_ctor_set(x_206, 0, x_198);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_198);
lean_dec(x_176);
lean_dec(x_5);
lean_dec(x_1);
x_208 = lean_ctor_get(x_201, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_201, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_210 = x_201;
} else {
 lean_dec_ref(x_201);
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
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_176);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_212 = lean_ctor_get(x_197, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_197, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_214 = x_197;
} else {
 lean_dec_ref(x_197);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_176);
lean_free_object(x_27);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_216 = lean_ctor_get(x_191, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_191, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_218 = x_191;
} else {
 lean_dec_ref(x_191);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
}
}
}
}
else
{
lean_free_object(x_27);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
goto block_40;
}
block_40:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
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
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_220 = lean_ctor_get(x_27, 0);
lean_inc(x_220);
lean_dec(x_27);
x_221 = l_Lean_ConstantInfo_type(x_220);
lean_dec(x_220);
x_222 = l_Lean_Compiler_LCNF_hasLocalInst(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_223 = lean_box(0);
lean_ctor_set(x_20, 0, x_223);
return x_20;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_231; 
lean_free_object(x_20);
x_224 = l_Lean_Meta_isInstance___redArg(x_17, x_7, x_23);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
x_231 = lean_unbox(x_225);
lean_dec(x_225);
if (x_231 == 0)
{
if (x_222 == 0)
{
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
goto block_230;
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_227);
lean_inc(x_17);
x_232 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7, x_226);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
x_236 = lean_box(0);
if (lean_is_scalar(x_235)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_235;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_234);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_238 = lean_ctor_get(x_232, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_239 = x_232;
} else {
 lean_dec_ref(x_232);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_233, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 x_241 = x_233;
} else {
 lean_dec_ref(x_233);
 x_241 = lean_box(0);
}
x_242 = lean_array_get_size(x_19);
x_243 = l_Lean_Compiler_LCNF_Decl_getArity(x_240);
lean_dec(x_240);
x_244 = lean_nat_dec_lt(x_242, x_243);
lean_dec(x_243);
lean_dec(x_242);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_241);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_245 = lean_box(0);
if (lean_is_scalar(x_239)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_239;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_238);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; size_t x_251; size_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_239);
x_247 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_238);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
x_251 = lean_array_size(x_248);
x_252 = 0;
lean_inc(x_248);
x_253 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_251, x_252, x_248);
x_254 = l_Array_append___redArg(x_19, x_253);
lean_dec(x_253);
lean_ctor_set(x_13, 2, x_254);
x_255 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_256 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_255, x_4, x_5, x_6, x_7, x_249);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
x_260 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_260, 0, x_259);
if (lean_is_scalar(x_250)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_250;
}
lean_ctor_set(x_261, 0, x_257);
lean_ctor_set(x_261, 1, x_260);
x_262 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_263 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_248, x_261, x_262, x_4, x_5, x_6, x_7, x_258);
lean_dec(x_4);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_266 = lean_ctor_get(x_264, 0);
lean_inc(x_266);
x_267 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_266, x_3, x_5, x_6, x_7, x_265);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
x_269 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_268);
lean_dec(x_5);
lean_dec(x_1);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_272 = lean_alloc_ctor(1, 1, 0);
} else {
 x_272 = x_241;
}
lean_ctor_set(x_272, 0, x_264);
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_271;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_270);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_264);
lean_dec(x_241);
lean_dec(x_5);
lean_dec(x_1);
x_274 = lean_ctor_get(x_267, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_267, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_276 = x_267;
} else {
 lean_dec_ref(x_267);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_241);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_278 = lean_ctor_get(x_263, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_263, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_280 = x_263;
} else {
 lean_dec_ref(x_263);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_250);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_282 = lean_ctor_get(x_256, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_256, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_284 = x_256;
} else {
 lean_dec_ref(x_256);
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
}
}
}
else
{
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
goto block_230;
}
block_230:
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_box(0);
if (lean_is_scalar(x_227)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_227;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_226);
return x_229;
}
}
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; 
x_286 = lean_ctor_get(x_20, 0);
x_287 = lean_ctor_get(x_20, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_20);
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_box(0);
x_290 = lean_unbox(x_289);
lean_inc(x_17);
x_291 = l_Lean_Environment_find_x3f(x_288, x_17, x_290);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; 
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_292 = lean_box(0);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_287);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_294 = lean_ctor_get(x_291, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_295 = x_291;
} else {
 lean_dec_ref(x_291);
 x_295 = lean_box(0);
}
x_296 = l_Lean_ConstantInfo_type(x_294);
lean_dec(x_294);
x_297 = l_Lean_Compiler_LCNF_hasLocalInst(x_296);
lean_dec(x_296);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_295);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_298 = lean_box(0);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_287);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_307; 
x_300 = l_Lean_Meta_isInstance___redArg(x_17, x_7, x_287);
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
x_307 = lean_unbox(x_301);
lean_dec(x_301);
if (x_307 == 0)
{
if (x_297 == 0)
{
lean_dec(x_295);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
goto block_306;
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_303);
lean_inc(x_17);
x_308 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_17, x_4, x_7, x_302);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_295);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_311 = x_308;
} else {
 lean_dec_ref(x_308);
 x_311 = lean_box(0);
}
x_312 = lean_box(0);
if (lean_is_scalar(x_311)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_311;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_310);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_314 = lean_ctor_get(x_308, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_315 = x_308;
} else {
 lean_dec_ref(x_308);
 x_315 = lean_box(0);
}
x_316 = lean_ctor_get(x_309, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_317 = x_309;
} else {
 lean_dec_ref(x_309);
 x_317 = lean_box(0);
}
x_318 = lean_array_get_size(x_19);
x_319 = l_Lean_Compiler_LCNF_Decl_getArity(x_316);
lean_dec(x_316);
x_320 = lean_nat_dec_lt(x_318, x_319);
lean_dec(x_319);
lean_dec(x_318);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
lean_dec(x_317);
lean_dec(x_295);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_321 = lean_box(0);
if (lean_is_scalar(x_315)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_315;
}
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_314);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; size_t x_327; size_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_315);
x_323 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_314);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
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
x_327 = lean_array_size(x_324);
x_328 = 0;
lean_inc(x_324);
x_329 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_327, x_328, x_324);
x_330 = l_Array_append___redArg(x_19, x_329);
lean_dec(x_329);
lean_ctor_set(x_13, 2, x_330);
x_331 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_332 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_331, x_4, x_5, x_6, x_7, x_325);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_ctor_get(x_333, 0);
lean_inc(x_335);
if (lean_is_scalar(x_295)) {
 x_336 = lean_alloc_ctor(5, 1, 0);
} else {
 x_336 = x_295;
 lean_ctor_set_tag(x_336, 5);
}
lean_ctor_set(x_336, 0, x_335);
if (lean_is_scalar(x_326)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_326;
}
lean_ctor_set(x_337, 0, x_333);
lean_ctor_set(x_337, 1, x_336);
x_338 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_339 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_324, x_337, x_338, x_4, x_5, x_6, x_7, x_334);
lean_dec(x_4);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_ctor_get(x_340, 0);
lean_inc(x_342);
x_343 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_342, x_3, x_5, x_6, x_7, x_341);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
lean_dec(x_343);
x_345 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_344);
lean_dec(x_5);
lean_dec(x_1);
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_347 = x_345;
} else {
 lean_dec_ref(x_345);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_348 = lean_alloc_ctor(1, 1, 0);
} else {
 x_348 = x_317;
}
lean_ctor_set(x_348, 0, x_340);
if (lean_is_scalar(x_347)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_347;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_346);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_340);
lean_dec(x_317);
lean_dec(x_5);
lean_dec(x_1);
x_350 = lean_ctor_get(x_343, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_343, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_352 = x_343;
} else {
 lean_dec_ref(x_343);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_317);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_354 = lean_ctor_get(x_339, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_339, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_356 = x_339;
} else {
 lean_dec_ref(x_339);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_326);
lean_dec(x_324);
lean_dec(x_317);
lean_dec(x_295);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_358 = lean_ctor_get(x_332, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_332, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_360 = x_332;
} else {
 lean_dec_ref(x_332);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
}
}
}
else
{
lean_dec(x_295);
lean_free_object(x_13);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
goto block_306;
}
block_306:
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_box(0);
if (lean_is_scalar(x_303)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_303;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_302);
return x_305;
}
}
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; 
x_362 = lean_ctor_get(x_13, 0);
x_363 = lean_ctor_get(x_13, 1);
x_364 = lean_ctor_get(x_13, 2);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_13);
x_365 = lean_st_ref_get(x_7, x_8);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_368 = x_365;
} else {
 lean_dec_ref(x_365);
 x_368 = lean_box(0);
}
x_369 = lean_ctor_get(x_366, 0);
lean_inc(x_369);
lean_dec(x_366);
x_370 = lean_box(0);
x_371 = lean_unbox(x_370);
lean_inc(x_362);
x_372 = l_Lean_Environment_find_x3f(x_369, x_362, x_371);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; 
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_373 = lean_box(0);
if (lean_is_scalar(x_368)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_368;
}
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_367);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_375 = lean_ctor_get(x_372, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_376 = x_372;
} else {
 lean_dec_ref(x_372);
 x_376 = lean_box(0);
}
x_377 = l_Lean_ConstantInfo_type(x_375);
lean_dec(x_375);
x_378 = l_Lean_Compiler_LCNF_hasLocalInst(x_377);
lean_dec(x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_376);
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_379 = lean_box(0);
if (lean_is_scalar(x_368)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_368;
}
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_367);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_388; 
lean_dec(x_368);
x_381 = l_Lean_Meta_isInstance___redArg(x_362, x_7, x_367);
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
x_388 = lean_unbox(x_382);
lean_dec(x_382);
if (x_388 == 0)
{
if (x_378 == 0)
{
lean_dec(x_376);
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
goto block_387;
}
else
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_384);
lean_inc(x_362);
x_389 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_362, x_4, x_7, x_383);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_376);
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_392 = x_389;
} else {
 lean_dec_ref(x_389);
 x_392 = lean_box(0);
}
x_393 = lean_box(0);
if (lean_is_scalar(x_392)) {
 x_394 = lean_alloc_ctor(0, 2, 0);
} else {
 x_394 = x_392;
}
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_391);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_395 = lean_ctor_get(x_389, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_396 = x_389;
} else {
 lean_dec_ref(x_389);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_390, 0);
lean_inc(x_397);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_398 = x_390;
} else {
 lean_dec_ref(x_390);
 x_398 = lean_box(0);
}
x_399 = lean_array_get_size(x_364);
x_400 = l_Lean_Compiler_LCNF_Decl_getArity(x_397);
lean_dec(x_397);
x_401 = lean_nat_dec_lt(x_399, x_400);
lean_dec(x_400);
lean_dec(x_399);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; 
lean_dec(x_398);
lean_dec(x_376);
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_402 = lean_box(0);
if (lean_is_scalar(x_396)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_396;
}
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_395);
return x_403;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; size_t x_408; size_t x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_396);
x_404 = l_Lean_Compiler_LCNF_mkNewParams(x_15, x_4, x_5, x_6, x_7, x_395);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_407 = x_404;
} else {
 lean_dec_ref(x_404);
 x_407 = lean_box(0);
}
x_408 = lean_array_size(x_405);
x_409 = 0;
lean_inc(x_405);
x_410 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_408, x_409, x_405);
x_411 = l_Array_append___redArg(x_364, x_410);
lean_dec(x_410);
x_412 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_412, 0, x_362);
lean_ctor_set(x_412, 1, x_363);
lean_ctor_set(x_412, 2, x_411);
x_413 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_414 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_412, x_413, x_4, x_5, x_6, x_7, x_406);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = lean_ctor_get(x_415, 0);
lean_inc(x_417);
if (lean_is_scalar(x_376)) {
 x_418 = lean_alloc_ctor(5, 1, 0);
} else {
 x_418 = x_376;
 lean_ctor_set_tag(x_418, 5);
}
lean_ctor_set(x_418, 0, x_417);
if (lean_is_scalar(x_407)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_407;
}
lean_ctor_set(x_419, 0, x_415);
lean_ctor_set(x_419, 1, x_418);
x_420 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_421 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_405, x_419, x_420, x_4, x_5, x_6, x_7, x_416);
lean_dec(x_4);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
x_425 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_14, x_424, x_3, x_5, x_6, x_7, x_423);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
lean_dec(x_425);
x_427 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_5, x_426);
lean_dec(x_5);
lean_dec(x_1);
x_428 = lean_ctor_get(x_427, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_429 = x_427;
} else {
 lean_dec_ref(x_427);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_430 = lean_alloc_ctor(1, 1, 0);
} else {
 x_430 = x_398;
}
lean_ctor_set(x_430, 0, x_422);
if (lean_is_scalar(x_429)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_429;
}
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_428);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_422);
lean_dec(x_398);
lean_dec(x_5);
lean_dec(x_1);
x_432 = lean_ctor_get(x_425, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_425, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_434 = x_425;
} else {
 lean_dec_ref(x_425);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 2, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_433);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_398);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_436 = lean_ctor_get(x_421, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_421, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_438 = x_421;
} else {
 lean_dec_ref(x_421);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_407);
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_376);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_440 = lean_ctor_get(x_414, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_414, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_442 = x_414;
} else {
 lean_dec_ref(x_414);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 2, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_440);
lean_ctor_set(x_443, 1, x_441);
return x_443;
}
}
}
}
}
else
{
lean_dec(x_376);
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
goto block_387;
}
block_387:
{
lean_object* x_385; lean_object* x_386; 
x_385 = lean_box(0);
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_383);
return x_386;
}
}
}
}
}
else
{
lean_object* x_444; lean_object* x_445; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_444 = lean_box(0);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_8);
return x_445;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_1);
x_6 = lean_st_ref_get(x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_9, x_5, x_11);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_name_eq(x_13, x_2);
lean_dec(x_13);
x_15 = lean_box(x_14);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_18, x_5, x_20);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_name_eq(x_22, x_2);
lean_dec(x_22);
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_9);
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
lean_dec(x_15);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_1, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3, x_6, x_8, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Compiler_LCNF_Simp_simp(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = l_Array_toSubarray___redArg(x_5, x_1, x_2);
x_24 = l_Array_ofSubarray___redArg(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_27 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_25, x_26, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3, x_30, x_8, x_11, x_12, x_13, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_4);
x_34 = l_Lean_Compiler_LCNF_Simp_simp(x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
lean_dec(x_11);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
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
lean_dec(x_13);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 3);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 2);
x_29 = lean_array_get_size(x_27);
x_30 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_21);
lean_inc(x_27);
lean_inc(x_2);
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
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_12, 0);
lean_inc(x_257);
lean_dec(x_12);
lean_inc(x_3);
lean_inc(x_257);
x_258 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_28, x_257, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = !lean_is_exclusive(x_3);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_ctor_get(x_3, 2);
x_263 = lean_ctor_get(x_3, 3);
lean_inc(x_257);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_257);
lean_ctor_set(x_264, 1, x_262);
x_265 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_263, x_257, x_259);
lean_ctor_set(x_3, 3, x_265);
lean_ctor_set(x_3, 2, x_264);
x_179 = x_3;
x_180 = x_4;
x_181 = x_5;
x_182 = x_6;
x_183 = x_7;
x_184 = x_8;
x_185 = x_9;
x_186 = x_260;
goto block_256;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_266 = lean_ctor_get(x_3, 0);
x_267 = lean_ctor_get(x_3, 1);
x_268 = lean_ctor_get(x_3, 2);
x_269 = lean_ctor_get(x_3, 3);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_3);
lean_inc(x_257);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_257);
lean_ctor_set(x_270, 1, x_268);
x_271 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_269, x_257, x_259);
x_272 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_272, 0, x_266);
lean_ctor_set(x_272, 1, x_267);
lean_ctor_set(x_272, 2, x_270);
lean_ctor_set(x_272, 3, x_271);
x_179 = x_272;
x_180 = x_4;
x_181 = x_5;
x_182 = x_6;
x_183 = x_7;
x_184 = x_8;
x_185 = x_9;
x_186 = x_260;
goto block_256;
}
}
else
{
uint8_t x_273; 
lean_dec(x_257);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_273 = !lean_is_exclusive(x_258);
if (x_273 == 0)
{
return x_258;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_258, 0);
x_275 = lean_ctor_get(x_258, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_258);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
else
{
lean_dec(x_12);
x_179 = x_3;
x_180 = x_4;
x_181 = x_5;
x_182 = x_6;
x_183 = x_7;
x_184 = x_8;
x_185 = x_9;
x_186 = x_23;
goto block_256;
}
block_178:
{
lean_object* x_45; 
lean_inc(x_36);
lean_inc(x_41);
lean_inc(x_38);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_37);
lean_inc(x_34);
x_45 = l_Lean_Compiler_LCNF_Simp_simp(x_33, x_34, x_37, x_44, x_40, x_38, x_41, x_36, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_46);
x_48 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_39);
x_49 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_37, x_47);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Compiler_LCNF_inferAppType(x_26, x_43, x_40, x_38, x_41, x_36, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_52);
x_54 = l_Lean_Expr_headBeta(x_52);
x_55 = l_Lean_Expr_isForall(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_35);
x_56 = l_Lean_Compiler_LCNF_mkAuxParam(x_52, x_32, x_40, x_38, x_41, x_36, x_53);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_inc(x_36);
lean_inc(x_41);
lean_inc(x_38);
lean_inc(x_40);
x_61 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_30, x_29, x_11, x_2, x_27, x_60, x_34, x_37, x_44, x_40, x_38, x_41, x_36, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unsigned_to_nat(1u);
x_65 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_66 = lean_array_push(x_65, x_58);
x_67 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_68 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_66, x_62, x_67, x_40, x_38, x_41, x_36, x_63);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_69);
x_71 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_71, 0, x_69);
lean_closure_set(x_71, 1, x_64);
x_72 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_46, x_71, x_40, x_38, x_41, x_36, x_70);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
lean_ctor_set_tag(x_56, 2);
lean_ctor_set(x_56, 1, x_74);
lean_ctor_set(x_56, 0, x_69);
if (lean_is_scalar(x_22)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_22;
}
lean_ctor_set(x_75, 0, x_56);
lean_ctor_set(x_72, 0, x_75);
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
lean_ctor_set_tag(x_56, 2);
lean_ctor_set(x_56, 1, x_76);
lean_ctor_set(x_56, 0, x_69);
if (lean_is_scalar(x_22)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_22;
}
lean_ctor_set(x_78, 0, x_56);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_69);
lean_free_object(x_56);
lean_dec(x_22);
x_80 = !lean_is_exclusive(x_72);
if (x_80 == 0)
{
return x_72;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_72, 0);
x_82 = lean_ctor_get(x_72, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_72);
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
lean_free_object(x_56);
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_22);
x_84 = !lean_is_exclusive(x_68);
if (x_84 == 0)
{
return x_68;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_68, 0);
x_86 = lean_ctor_get(x_68, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_68);
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
lean_free_object(x_56);
lean_dec(x_58);
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_22);
x_88 = !lean_is_exclusive(x_61);
if (x_88 == 0)
{
return x_61;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_61, 0);
x_90 = lean_ctor_get(x_61, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_61);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_56, 0);
x_93 = lean_ctor_get(x_56, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_56);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_inc(x_36);
lean_inc(x_41);
lean_inc(x_38);
lean_inc(x_40);
x_95 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_30, x_29, x_11, x_2, x_27, x_94, x_34, x_37, x_44, x_40, x_38, x_41, x_36, x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_unsigned_to_nat(1u);
x_99 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_100 = lean_array_push(x_99, x_92);
x_101 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_102 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_100, x_96, x_101, x_40, x_38, x_41, x_36, x_97);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_103);
x_105 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_105, 0, x_103);
lean_closure_set(x_105, 1, x_98);
x_106 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_46, x_105, x_40, x_38, x_41, x_36, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_103);
lean_ctor_set(x_110, 1, x_107);
if (lean_is_scalar(x_22)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_22;
}
lean_ctor_set(x_111, 0, x_110);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_103);
lean_dec(x_22);
x_113 = lean_ctor_get(x_106, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_106, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_115 = x_106;
} else {
 lean_dec_ref(x_106);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_22);
x_117 = lean_ctor_get(x_102, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_102, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_119 = x_102;
} else {
 lean_dec_ref(x_102);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_92);
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_22);
x_121 = lean_ctor_get(x_95, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_95, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_123 = x_95;
} else {
 lean_dec_ref(x_95);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_52);
x_125 = lean_mk_empty_array_with_capacity(x_35);
lean_dec(x_35);
x_126 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__7;
x_127 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_125, x_46, x_126, x_40, x_38, x_41, x_36, x_53);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_36);
lean_inc(x_41);
lean_inc(x_38);
lean_inc(x_40);
x_130 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_128, x_40, x_38, x_41, x_36, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_inc(x_36);
lean_inc(x_41);
lean_inc(x_38);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_37);
lean_inc(x_34);
x_134 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_30, x_29, x_11, x_2, x_27, x_133, x_34, x_37, x_44, x_40, x_38, x_41, x_36, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_131);
x_138 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_139 = lean_array_push(x_138, x_137);
x_140 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_139, x_135, x_34, x_37, x_44, x_40, x_38, x_41, x_36, x_136);
lean_dec(x_36);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_40);
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_139);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
if (lean_is_scalar(x_22)) {
 x_143 = lean_alloc_ctor(1, 1, 0);
} else {
 x_143 = x_22;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_140, 0, x_143);
return x_140;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_140, 0);
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_140);
if (lean_is_scalar(x_22)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_22;
}
lean_ctor_set(x_146, 0, x_144);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
uint8_t x_148; 
lean_dec(x_131);
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_22);
x_148 = !lean_is_exclusive(x_134);
if (x_148 == 0)
{
return x_134;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_134, 0);
x_150 = lean_ctor_get(x_134, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_134);
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
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_130);
if (x_152 == 0)
{
return x_130;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_130, 0);
x_154 = lean_ctor_get(x_130, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_130);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_127);
if (x_156 == 0)
{
return x_127;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_127, 0);
x_158 = lean_ctor_get(x_127, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_127);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_2);
x_160 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_37, x_47);
lean_dec(x_37);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_46, x_39, x_40, x_38, x_41, x_36, x_161);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_162, 0);
if (lean_is_scalar(x_22)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_22;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_162, 0, x_165);
return x_162;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_162, 0);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_162);
if (lean_is_scalar(x_22)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_22;
}
lean_ctor_set(x_168, 0, x_166);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
uint8_t x_170; 
lean_dec(x_22);
x_170 = !lean_is_exclusive(x_162);
if (x_170 == 0)
{
return x_162;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_162, 0);
x_172 = lean_ctor_get(x_162, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_162);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_2);
x_174 = !lean_is_exclusive(x_45);
if (x_174 == 0)
{
return x_45;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_45, 0);
x_176 = lean_ctor_get(x_45, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_45);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
block_256:
{
if (x_32 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_21);
x_187 = lean_unsigned_to_nat(0u);
lean_inc(x_30);
lean_inc(x_27);
x_188 = l_Array_toSubarray___redArg(x_27, x_187, x_30);
x_189 = l_Array_ofSubarray___redArg(x_188);
lean_dec(x_188);
lean_inc(x_189);
x_190 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_24, x_25, x_189, x_32, x_179, x_180, x_181, x_182, x_183, x_184, x_185, x_186);
lean_dec(x_24);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
lean_inc(x_181);
lean_inc(x_179);
lean_inc(x_180);
x_193 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2), 10, 4);
lean_closure_set(x_193, 0, x_180);
lean_closure_set(x_193, 1, x_31);
lean_closure_set(x_193, 2, x_179);
lean_closure_set(x_193, 3, x_181);
x_194 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_11);
if (x_194 == 0)
{
x_33 = x_191;
x_34 = x_179;
x_35 = x_187;
x_36 = x_185;
x_37 = x_180;
x_38 = x_183;
x_39 = x_193;
x_40 = x_182;
x_41 = x_184;
x_42 = x_192;
x_43 = x_189;
x_44 = x_181;
goto block_178;
}
else
{
uint8_t x_195; 
x_195 = lean_nat_dec_eq(x_29, x_30);
if (x_195 == 0)
{
x_33 = x_191;
x_34 = x_179;
x_35 = x_187;
x_36 = x_185;
x_37 = x_180;
x_38 = x_183;
x_39 = x_193;
x_40 = x_182;
x_41 = x_184;
x_42 = x_192;
x_43 = x_189;
x_44 = x_181;
goto block_178;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_193);
lean_dec(x_189);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_2);
x_196 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_180, x_192);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = l_Lean_Compiler_LCNF_Simp_simp(x_191, x_179, x_180, x_181, x_182, x_183, x_184, x_185, x_197);
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
lean_dec(x_189);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_2);
x_210 = !lean_is_exclusive(x_190);
if (x_210 == 0)
{
return x_190;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_190, 0);
x_212 = lean_ctor_get(x_190, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_190);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
lean_object* x_214; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
x_214 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_179, x_180, x_181, x_182, x_183, x_184, x_185, x_186);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
x_218 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_217, x_180, x_183, x_184, x_185, x_216);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_180, x_219);
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_220, 1);
x_223 = lean_ctor_get(x_220, 0);
lean_dec(x_223);
lean_ctor_set_tag(x_220, 1);
lean_ctor_set(x_220, 1, x_2);
lean_ctor_set(x_220, 0, x_215);
x_224 = l_Lean_Compiler_LCNF_Simp_simp(x_220, x_179, x_180, x_181, x_182, x_183, x_184, x_185, x_222);
if (lean_obj_tag(x_224) == 0)
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_224, 0);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_224, 0, x_227);
return x_224;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_224, 0);
x_229 = lean_ctor_get(x_224, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_224);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_228);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
else
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_224);
if (x_232 == 0)
{
return x_224;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_224, 0);
x_234 = lean_ctor_get(x_224, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_224);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_220, 1);
lean_inc(x_236);
lean_dec(x_220);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_215);
lean_ctor_set(x_237, 1, x_2);
x_238 = l_Lean_Compiler_LCNF_Simp_simp(x_237, x_179, x_180, x_181, x_182, x_183, x_184, x_185, x_236);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
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
x_242 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_242, 0, x_239);
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
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_238, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_238, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_246 = x_238;
} else {
 lean_dec_ref(x_238);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_215);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_2);
x_248 = !lean_is_exclusive(x_218);
if (x_248 == 0)
{
return x_218;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_218, 0);
x_250 = lean_ctor_get(x_218, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_218);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
else
{
uint8_t x_252; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_11);
lean_dec(x_2);
x_252 = !lean_is_exclusive(x_214);
if (x_252 == 0)
{
return x_214;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_214, 0);
x_254 = lean_ctor_get(x_214, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_214);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_277 = !lean_is_exclusive(x_13);
if (x_277 == 0)
{
return x_13;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_13, 0);
x_279 = lean_ctor_get(x_13, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_13);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_st_ref_get(x_3, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_11, x_1, x_6);
lean_dec(x_11);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_15, x_7, x_1);
lean_dec(x_15);
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(x_2, x_16, x_17, x_4, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_1, x_2, x_4, x_7, x_10);
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
lean_inc(x_8);
lean_dec(x_7);
x_9 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_8, x_2, x_1);
lean_dec(x_8);
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
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_12, x_2, x_1);
lean_dec(x_12);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(x_8, x_4, x_5);
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
lean_dec(x_9);
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
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1, x_2, x_3, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_16 = lean_array_fget(x_4, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_50; uint8_t x_51; lean_object* x_66; uint8_t x_67; uint8_t x_69; lean_object* x_70; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_16, 2);
lean_inc(x_32);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_array_get_size(x_31);
x_74 = lean_nat_dec_lt(x_72, x_73);
if (x_74 == 0)
{
lean_dec(x_73);
x_69 = x_2;
x_70 = x_12;
goto block_71;
}
else
{
if (x_74 == 0)
{
lean_dec(x_73);
x_69 = x_2;
x_70 = x_12;
goto block_71;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_77 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_31, x_75, x_76, x_11, x_12);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_69 = x_80;
x_70 = x_79;
goto block_71;
}
}
block_49:
{
lean_object* x_34; 
lean_inc(x_7);
lean_inc(x_1);
x_34 = l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_30, x_31, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_37 = l_Lean_Compiler_LCNF_Simp_simp(x_32, x_5, x_6, x_35, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_16);
x_40 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_38);
x_17 = x_40;
x_18 = x_39;
goto block_29;
}
else
{
uint8_t x_41; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
block_65:
{
if (x_51 == 0)
{
x_33 = x_50;
goto block_49;
}
else
{
lean_object* x_52; 
lean_dec(x_31);
lean_dec(x_30);
lean_inc(x_32);
x_52 = l_Lean_Compiler_LCNF_Code_inferType(x_32, x_8, x_9, x_10, x_11, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_32, x_9, x_54);
lean_dec(x_32);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_6, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_59, 0, x_53);
lean_inc(x_16);
x_60 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_59);
x_17 = x_60;
x_18 = x_58;
goto block_29;
}
else
{
uint8_t x_61; 
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_52);
if (x_61 == 0)
{
return x_52;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_52, 0);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_52);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
block_68:
{
if (x_2 == 0)
{
x_33 = x_66;
goto block_49;
}
else
{
x_50 = x_66;
x_51 = x_67;
goto block_65;
}
}
block_71:
{
if (lean_obj_tag(x_32) == 6)
{
x_66 = x_70;
x_67 = x_69;
goto block_68;
}
else
{
if (x_2 == 0)
{
x_50 = x_70;
x_51 = x_69;
goto block_65;
}
else
{
x_66 = x_70;
x_67 = x_69;
goto block_68;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_16, 0);
lean_inc(x_81);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_82 = l_Lean_Compiler_LCNF_Simp_simp(x_81, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_16);
x_85 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_83);
x_17 = x_85;
x_18 = x_84;
goto block_29;
}
else
{
uint8_t x_86; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
return x_82;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_82, 0);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_82);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
block_29:
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_16);
lean_dec(x_16);
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
lean_dec(x_17);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget(x_4, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_50; uint8_t x_51; uint8_t x_66; lean_object* x_67; uint8_t x_69; lean_object* x_70; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_16, 2);
lean_inc(x_32);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_array_get_size(x_31);
x_74 = lean_nat_dec_lt(x_72, x_73);
if (x_74 == 0)
{
lean_dec(x_73);
x_69 = x_2;
x_70 = x_12;
goto block_71;
}
else
{
if (x_74 == 0)
{
lean_dec(x_73);
x_69 = x_2;
x_70 = x_12;
goto block_71;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_77 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_31, x_75, x_76, x_11, x_12);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_69 = x_80;
x_70 = x_79;
goto block_71;
}
}
block_49:
{
lean_object* x_34; 
lean_inc(x_7);
lean_inc(x_1);
x_34 = l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_30, x_31, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_37 = l_Lean_Compiler_LCNF_Simp_simp(x_32, x_5, x_6, x_35, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_16);
x_40 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_38);
x_17 = x_40;
x_18 = x_39;
goto block_29;
}
else
{
uint8_t x_41; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
block_65:
{
if (x_51 == 0)
{
x_33 = x_50;
goto block_49;
}
else
{
lean_object* x_52; 
lean_dec(x_31);
lean_dec(x_30);
lean_inc(x_32);
x_52 = l_Lean_Compiler_LCNF_Code_inferType(x_32, x_8, x_9, x_10, x_11, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_32, x_9, x_54);
lean_dec(x_32);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_6, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_59, 0, x_53);
lean_inc(x_16);
x_60 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_59);
x_17 = x_60;
x_18 = x_58;
goto block_29;
}
else
{
uint8_t x_61; 
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_52);
if (x_61 == 0)
{
return x_52;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_52, 0);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_52);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
block_68:
{
if (x_2 == 0)
{
x_33 = x_67;
goto block_49;
}
else
{
x_50 = x_67;
x_51 = x_66;
goto block_65;
}
}
block_71:
{
if (lean_obj_tag(x_32) == 6)
{
x_66 = x_69;
x_67 = x_70;
goto block_68;
}
else
{
if (x_2 == 0)
{
x_50 = x_70;
x_51 = x_69;
goto block_65;
}
else
{
x_66 = x_69;
x_67 = x_70;
goto block_68;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_16, 0);
lean_inc(x_81);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_82 = l_Lean_Compiler_LCNF_Simp_simp(x_81, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_16);
x_85 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_83);
x_17 = x_85;
x_18 = x_84;
goto block_29;
}
else
{
uint8_t x_86; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
return x_82;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_82, 0);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_82);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
block_29:
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_16);
lean_dec(x_16);
x_20 = lean_ptr_addr(x_17);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
x_24 = lean_array_fset(x_4, x_3, x_17);
x_25 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3_spec__3(x_1, x_2, x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3_spec__3(x_1, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_8, x_5, x_6);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1, x_2, x_3, x_4, x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_7);
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
lean_dec(x_9);
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
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_1, x_2, x_3, x_5, x_11);
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_24; uint8_t x_25; lean_object* x_30; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
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
lean_inc(x_51);
x_52 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_51, x_7, x_16);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(x_4, x_7, x_10, x_55);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
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
if (x_3 == 0)
{
lean_object* x_61; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_dec(x_52);
x_30 = x_61;
goto block_50;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_dec(x_52);
lean_inc(x_4);
x_63 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_62);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_30 = x_64;
goto block_50;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
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
lean_dec(x_4);
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
lean_dec(x_2);
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
lean_dec(x_4);
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
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ptr_addr(x_32);
lean_dec(x_32);
x_34 = lean_ptr_addr(x_15);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_dec(x_31);
x_18 = x_30;
x_19 = x_35;
goto block_23;
}
else
{
size_t x_36; size_t x_37; uint8_t x_38; 
x_36 = lean_ptr_addr(x_31);
lean_dec(x_31);
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
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
x_41 = lean_ptr_addr(x_40);
lean_dec(x_40);
x_42 = lean_ptr_addr(x_15);
x_43 = lean_usize_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_dec(x_39);
x_24 = x_30;
x_25 = x_43;
goto block_29;
}
else
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = lean_ptr_addr(x_39);
lean_dec(x_39);
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
lean_dec(x_4);
lean_dec(x_2);
x_47 = l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3;
x_48 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_47);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_38 = lean_ctor_get(x_7, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_7, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 6);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 7);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 8);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 9);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 10);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_50 = lean_ctor_get(x_7, 11);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_52 = lean_ctor_get(x_7, 12);
lean_inc(x_52);
x_53 = lean_nat_dec_eq(x_41, x_42);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_7);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_124; lean_object* x_125; 
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
x_68 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_add(x_41, x_124);
lean_dec(x_41);
lean_ctor_set(x_7, 3, x_125);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_398; 
x_126 = lean_ctor_get(x_1, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_1, 1);
lean_inc(x_127);
lean_inc(x_126);
x_365 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_53, x_126, x_3, x_6, x_69);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_398 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2068_(x_126, x_366);
if (x_398 == 0)
{
goto block_397;
}
else
{
if (x_53 == 0)
{
x_368 = x_2;
x_369 = x_3;
x_370 = x_4;
x_371 = x_5;
x_372 = x_6;
x_373 = x_7;
x_374 = x_8;
x_375 = x_367;
goto block_394;
}
else
{
goto block_397;
}
}
block_151:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_131);
lean_ctor_set(x_145, 2, x_132);
lean_ctor_set(x_145, 3, x_133);
lean_ctor_set(x_145, 4, x_135);
lean_ctor_set(x_145, 5, x_136);
lean_ctor_set(x_145, 6, x_137);
lean_ctor_set_uint8(x_145, sizeof(void*)*7, x_134);
x_146 = lean_st_ref_set(x_143, x_145, x_141);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_148 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_138, x_143, x_142, x_147);
lean_dec(x_138);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_1 = x_127;
x_2 = x_129;
x_3 = x_143;
x_4 = x_128;
x_5 = x_140;
x_6 = x_142;
x_7 = x_130;
x_8 = x_139;
x_9 = x_149;
goto _start;
}
block_349:
{
if (x_161 == 0)
{
lean_object* x_162; 
lean_inc(x_157);
lean_inc(x_155);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_156);
x_162 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_156, x_158, x_159, x_155, x_157, x_152);
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
lean_dec(x_162);
lean_inc(x_157);
lean_inc(x_155);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_156);
x_165 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_156, x_154, x_160, x_158, x_159, x_155, x_157, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_156, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_156, 3);
lean_inc(x_169);
lean_inc(x_169);
x_170 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_169, x_167);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
lean_inc(x_157);
lean_inc(x_155);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_153);
lean_inc(x_160);
lean_inc(x_154);
lean_inc(x_127);
lean_inc(x_156);
x_173 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_156, x_127, x_154, x_160, x_153, x_158, x_159, x_155, x_157, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
lean_inc(x_157);
lean_inc(x_155);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_153);
lean_inc(x_160);
lean_inc(x_154);
x_176 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_169, x_154, x_160, x_153, x_158, x_159, x_155, x_157, x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
lean_inc(x_157);
lean_inc(x_155);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_153);
lean_inc(x_160);
lean_inc(x_154);
lean_inc(x_127);
x_179 = l_Lean_Compiler_LCNF_Simp_simp(x_127, x_154, x_160, x_153, x_158, x_159, x_155, x_157, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_168, x_160, x_181);
lean_dec(x_168);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_unbox(x_183);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_1);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_156, x_160, x_159, x_185);
lean_dec(x_159);
lean_dec(x_160);
lean_dec(x_156);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_186, 0);
lean_dec(x_188);
lean_ctor_set(x_186, 0, x_180);
return x_186;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_180);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; size_t x_194; size_t x_195; uint8_t x_196; 
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
lean_dec(x_182);
lean_inc(x_156);
x_192 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_156, x_154, x_160, x_153, x_158, x_159, x_155, x_157, x_191);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_153);
lean_dec(x_160);
lean_dec(x_154);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_ptr_addr(x_127);
lean_dec(x_127);
x_195 = lean_ptr_addr(x_180);
x_196 = lean_usize_dec_eq(x_194, x_195);
if (x_196 == 0)
{
lean_dec(x_126);
x_30 = x_193;
x_31 = x_156;
x_32 = x_180;
x_33 = x_196;
goto block_37;
}
else
{
size_t x_197; size_t x_198; uint8_t x_199; 
x_197 = lean_ptr_addr(x_126);
lean_dec(x_126);
x_198 = lean_ptr_addr(x_156);
x_199 = lean_usize_dec_eq(x_197, x_198);
x_30 = x_193;
x_31 = x_156;
x_32 = x_180;
x_33 = x_199;
goto block_37;
}
}
}
else
{
lean_dec(x_168);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_1);
return x_179;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_126);
lean_dec(x_1);
x_200 = lean_ctor_get(x_177, 0);
lean_inc(x_200);
lean_dec(x_177);
x_201 = lean_ctor_get(x_176, 1);
lean_inc(x_201);
lean_dec(x_176);
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
x_204 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_168, x_203, x_160, x_159, x_155, x_157, x_201);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
x_206 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_156, x_160, x_159, x_205);
lean_dec(x_156);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
lean_inc(x_157);
lean_inc(x_155);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_153);
lean_inc(x_160);
lean_inc(x_154);
x_208 = l_Lean_Compiler_LCNF_Simp_simp(x_127, x_154, x_160, x_153, x_158, x_159, x_155, x_157, x_207);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_202, x_209, x_154, x_160, x_153, x_158, x_159, x_155, x_157, x_210);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_153);
lean_dec(x_160);
lean_dec(x_154);
lean_dec(x_202);
return x_211;
}
else
{
lean_dec(x_202);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
return x_208;
}
}
else
{
uint8_t x_212; 
lean_dec(x_202);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_127);
x_212 = !lean_is_exclusive(x_204);
if (x_212 == 0)
{
return x_204;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_204, 0);
x_214 = lean_ctor_get(x_204, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_204);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_168);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_1);
x_216 = !lean_is_exclusive(x_176);
if (x_216 == 0)
{
return x_176;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_176, 0);
x_218 = lean_ctor_get(x_176, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_176);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_1);
x_220 = lean_ctor_get(x_173, 1);
lean_inc(x_220);
lean_dec(x_173);
x_221 = lean_ctor_get(x_174, 0);
lean_inc(x_221);
lean_dec(x_174);
x_222 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_156, x_160, x_159, x_220);
lean_dec(x_159);
lean_dec(x_160);
lean_dec(x_156);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_222, 0);
lean_dec(x_224);
lean_ctor_set(x_222, 0, x_221);
return x_222;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_221);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
else
{
uint8_t x_227; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_1);
x_227 = !lean_is_exclusive(x_173);
if (x_227 == 0)
{
return x_173;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_173, 0);
x_229 = lean_ctor_get(x_173, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_173);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_169);
lean_dec(x_126);
lean_dec(x_1);
x_231 = lean_ctor_get(x_170, 1);
lean_inc(x_231);
lean_dec(x_170);
x_232 = lean_ctor_get(x_171, 0);
lean_inc(x_232);
lean_dec(x_171);
x_233 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_168, x_232, x_160, x_159, x_155, x_157, x_231);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_156, x_160, x_159, x_234);
lean_dec(x_156);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_1 = x_127;
x_2 = x_154;
x_3 = x_160;
x_4 = x_153;
x_5 = x_158;
x_6 = x_159;
x_7 = x_155;
x_8 = x_157;
x_9 = x_236;
goto _start;
}
else
{
uint8_t x_238; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_127);
x_238 = !lean_is_exclusive(x_233);
if (x_238 == 0)
{
return x_233;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_233, 0);
x_240 = lean_ctor_get(x_233, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_233);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_156);
lean_dec(x_126);
x_242 = !lean_is_exclusive(x_1);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_1, 1);
lean_dec(x_243);
x_244 = lean_ctor_get(x_1, 0);
lean_dec(x_244);
x_245 = lean_ctor_get(x_165, 1);
lean_inc(x_245);
lean_dec(x_165);
x_246 = lean_ctor_get(x_166, 0);
lean_inc(x_246);
lean_dec(x_166);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_246);
x_2 = x_154;
x_3 = x_160;
x_4 = x_153;
x_5 = x_158;
x_6 = x_159;
x_7 = x_155;
x_8 = x_157;
x_9 = x_245;
goto _start;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_1);
x_248 = lean_ctor_get(x_165, 1);
lean_inc(x_248);
lean_dec(x_165);
x_249 = lean_ctor_get(x_166, 0);
lean_inc(x_249);
lean_dec(x_166);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_127);
x_1 = x_250;
x_2 = x_154;
x_3 = x_160;
x_4 = x_153;
x_5 = x_158;
x_6 = x_159;
x_7 = x_155;
x_8 = x_157;
x_9 = x_248;
goto _start;
}
}
}
else
{
uint8_t x_252; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_1);
x_252 = !lean_is_exclusive(x_165);
if (x_252 == 0)
{
return x_165;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_165, 0);
x_254 = lean_ctor_get(x_165, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_165);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_156);
lean_dec(x_126);
lean_dec(x_1);
x_256 = lean_ctor_get(x_162, 1);
lean_inc(x_256);
lean_dec(x_162);
x_257 = lean_ctor_get(x_163, 0);
lean_inc(x_257);
lean_dec(x_163);
x_258 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_160, x_256);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
lean_inc(x_157);
lean_inc(x_155);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_153);
lean_inc(x_160);
lean_inc(x_154);
x_260 = l_Lean_Compiler_LCNF_Simp_simp(x_127, x_154, x_160, x_153, x_158, x_159, x_155, x_157, x_259);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_257, x_261, x_154, x_160, x_153, x_158, x_159, x_155, x_157, x_262);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_153);
lean_dec(x_160);
lean_dec(x_154);
lean_dec(x_257);
return x_263;
}
else
{
lean_dec(x_257);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
return x_260;
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_1);
x_264 = !lean_is_exclusive(x_162);
if (x_264 == 0)
{
return x_162;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_162, 0);
x_266 = lean_ctor_get(x_162, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_162);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
lean_dec(x_126);
lean_dec(x_1);
x_268 = lean_st_ref_take(x_160, x_152);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec(x_268);
x_272 = lean_ctor_get(x_269, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_269, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_269, 3);
lean_inc(x_274);
x_275 = lean_ctor_get_uint8(x_269, sizeof(void*)*7);
x_276 = lean_ctor_get(x_269, 4);
lean_inc(x_276);
x_277 = lean_ctor_get(x_269, 5);
lean_inc(x_277);
x_278 = lean_ctor_get(x_269, 6);
lean_inc(x_278);
lean_dec(x_269);
x_279 = !lean_is_exclusive(x_270);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint64_t x_285; uint64_t x_286; uint64_t x_287; uint64_t x_288; uint64_t x_289; uint64_t x_290; uint64_t x_291; size_t x_292; size_t x_293; size_t x_294; size_t x_295; size_t x_296; lean_object* x_297; uint8_t x_298; 
x_280 = lean_ctor_get(x_270, 0);
x_281 = lean_ctor_get(x_270, 1);
x_282 = lean_ctor_get(x_156, 0);
lean_inc(x_282);
x_283 = lean_box(0);
x_284 = lean_array_get_size(x_281);
x_285 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_282);
x_286 = 32;
x_287 = lean_uint64_shift_right(x_285, x_286);
x_288 = lean_uint64_xor(x_285, x_287);
x_289 = 16;
x_290 = lean_uint64_shift_right(x_288, x_289);
x_291 = lean_uint64_xor(x_288, x_290);
x_292 = lean_uint64_to_usize(x_291);
x_293 = lean_usize_of_nat(x_284);
lean_dec(x_284);
x_294 = 1;
x_295 = lean_usize_sub(x_293, x_294);
x_296 = lean_usize_land(x_292, x_295);
x_297 = lean_array_uget(x_281, x_296);
x_298 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_282, x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_299 = lean_nat_add(x_280, x_124);
lean_dec(x_280);
x_300 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_300, 0, x_282);
lean_ctor_set(x_300, 1, x_283);
lean_ctor_set(x_300, 2, x_297);
x_301 = lean_array_uset(x_281, x_296, x_300);
x_302 = lean_unsigned_to_nat(4u);
x_303 = lean_nat_mul(x_299, x_302);
x_304 = lean_unsigned_to_nat(3u);
x_305 = lean_nat_div(x_303, x_304);
lean_dec(x_303);
x_306 = lean_array_get_size(x_301);
x_307 = lean_nat_dec_le(x_305, x_306);
lean_dec(x_306);
lean_dec(x_305);
if (x_307 == 0)
{
lean_object* x_308; 
x_308 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_301);
lean_ctor_set(x_270, 1, x_308);
lean_ctor_set(x_270, 0, x_299);
x_128 = x_153;
x_129 = x_154;
x_130 = x_155;
x_131 = x_272;
x_132 = x_273;
x_133 = x_274;
x_134 = x_275;
x_135 = x_276;
x_136 = x_277;
x_137 = x_278;
x_138 = x_156;
x_139 = x_157;
x_140 = x_158;
x_141 = x_271;
x_142 = x_159;
x_143 = x_160;
x_144 = x_270;
goto block_151;
}
else
{
lean_ctor_set(x_270, 1, x_301);
lean_ctor_set(x_270, 0, x_299);
x_128 = x_153;
x_129 = x_154;
x_130 = x_155;
x_131 = x_272;
x_132 = x_273;
x_133 = x_274;
x_134 = x_275;
x_135 = x_276;
x_136 = x_277;
x_137 = x_278;
x_138 = x_156;
x_139 = x_157;
x_140 = x_158;
x_141 = x_271;
x_142 = x_159;
x_143 = x_160;
x_144 = x_270;
goto block_151;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_box(0);
x_310 = lean_array_uset(x_281, x_296, x_309);
x_311 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_282, x_283, x_297);
x_312 = lean_array_uset(x_310, x_296, x_311);
lean_ctor_set(x_270, 1, x_312);
x_128 = x_153;
x_129 = x_154;
x_130 = x_155;
x_131 = x_272;
x_132 = x_273;
x_133 = x_274;
x_134 = x_275;
x_135 = x_276;
x_136 = x_277;
x_137 = x_278;
x_138 = x_156;
x_139 = x_157;
x_140 = x_158;
x_141 = x_271;
x_142 = x_159;
x_143 = x_160;
x_144 = x_270;
goto block_151;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint64_t x_318; uint64_t x_319; uint64_t x_320; uint64_t x_321; uint64_t x_322; uint64_t x_323; uint64_t x_324; size_t x_325; size_t x_326; size_t x_327; size_t x_328; size_t x_329; lean_object* x_330; uint8_t x_331; 
x_313 = lean_ctor_get(x_270, 0);
x_314 = lean_ctor_get(x_270, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_270);
x_315 = lean_ctor_get(x_156, 0);
lean_inc(x_315);
x_316 = lean_box(0);
x_317 = lean_array_get_size(x_314);
x_318 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_315);
x_319 = 32;
x_320 = lean_uint64_shift_right(x_318, x_319);
x_321 = lean_uint64_xor(x_318, x_320);
x_322 = 16;
x_323 = lean_uint64_shift_right(x_321, x_322);
x_324 = lean_uint64_xor(x_321, x_323);
x_325 = lean_uint64_to_usize(x_324);
x_326 = lean_usize_of_nat(x_317);
lean_dec(x_317);
x_327 = 1;
x_328 = lean_usize_sub(x_326, x_327);
x_329 = lean_usize_land(x_325, x_328);
x_330 = lean_array_uget(x_314, x_329);
x_331 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_315, x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_332 = lean_nat_add(x_313, x_124);
lean_dec(x_313);
x_333 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_333, 0, x_315);
lean_ctor_set(x_333, 1, x_316);
lean_ctor_set(x_333, 2, x_330);
x_334 = lean_array_uset(x_314, x_329, x_333);
x_335 = lean_unsigned_to_nat(4u);
x_336 = lean_nat_mul(x_332, x_335);
x_337 = lean_unsigned_to_nat(3u);
x_338 = lean_nat_div(x_336, x_337);
lean_dec(x_336);
x_339 = lean_array_get_size(x_334);
x_340 = lean_nat_dec_le(x_338, x_339);
lean_dec(x_339);
lean_dec(x_338);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; 
x_341 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_334);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_332);
lean_ctor_set(x_342, 1, x_341);
x_128 = x_153;
x_129 = x_154;
x_130 = x_155;
x_131 = x_272;
x_132 = x_273;
x_133 = x_274;
x_134 = x_275;
x_135 = x_276;
x_136 = x_277;
x_137 = x_278;
x_138 = x_156;
x_139 = x_157;
x_140 = x_158;
x_141 = x_271;
x_142 = x_159;
x_143 = x_160;
x_144 = x_342;
goto block_151;
}
else
{
lean_object* x_343; 
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_332);
lean_ctor_set(x_343, 1, x_334);
x_128 = x_153;
x_129 = x_154;
x_130 = x_155;
x_131 = x_272;
x_132 = x_273;
x_133 = x_274;
x_134 = x_275;
x_135 = x_276;
x_136 = x_277;
x_137 = x_278;
x_138 = x_156;
x_139 = x_157;
x_140 = x_158;
x_141 = x_271;
x_142 = x_159;
x_143 = x_160;
x_144 = x_343;
goto block_151;
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_344 = lean_box(0);
x_345 = lean_array_uset(x_314, x_329, x_344);
x_346 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_315, x_316, x_330);
x_347 = lean_array_uset(x_345, x_329, x_346);
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_313);
lean_ctor_set(x_348, 1, x_347);
x_128 = x_153;
x_129 = x_154;
x_130 = x_155;
x_131 = x_272;
x_132 = x_273;
x_133 = x_274;
x_134 = x_275;
x_135 = x_276;
x_136 = x_277;
x_137 = x_278;
x_138 = x_156;
x_139 = x_157;
x_140 = x_158;
x_141 = x_271;
x_142 = x_159;
x_143 = x_160;
x_144 = x_348;
goto block_151;
}
}
}
}
block_364:
{
uint8_t x_361; 
x_361 = l_Lean_Expr_isErased(x_351);
lean_dec(x_351);
if (x_361 == 0)
{
lean_dec(x_352);
x_152 = x_360;
x_153 = x_355;
x_154 = x_353;
x_155 = x_358;
x_156 = x_350;
x_157 = x_359;
x_158 = x_356;
x_159 = x_357;
x_160 = x_354;
x_161 = x_53;
goto block_349;
}
else
{
lean_object* x_362; uint8_t x_363; 
x_362 = lean_box(1);
x_363 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1208_(x_352, x_362);
lean_dec(x_352);
if (x_363 == 0)
{
x_152 = x_360;
x_153 = x_355;
x_154 = x_353;
x_155 = x_358;
x_156 = x_350;
x_157 = x_359;
x_158 = x_356;
x_159 = x_357;
x_160 = x_354;
x_161 = x_361;
goto block_349;
}
else
{
x_152 = x_360;
x_153 = x_355;
x_154 = x_353;
x_155 = x_358;
x_156 = x_350;
x_157 = x_359;
x_158 = x_356;
x_159 = x_357;
x_160 = x_354;
x_161 = x_53;
goto block_349;
}
}
}
block_394:
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_366, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_366, 3);
lean_inc(x_377);
lean_inc(x_374);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
lean_inc(x_370);
lean_inc(x_377);
x_378 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_377, x_368, x_370, x_371, x_372, x_373, x_374, x_375);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; 
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_350 = x_366;
x_351 = x_376;
x_352 = x_377;
x_353 = x_368;
x_354 = x_369;
x_355 = x_370;
x_356 = x_371;
x_357 = x_372;
x_358 = x_373;
x_359 = x_374;
x_360 = x_380;
goto block_364;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_377);
lean_dec(x_376);
x_381 = lean_ctor_get(x_378, 1);
lean_inc(x_381);
lean_dec(x_378);
x_382 = lean_ctor_get(x_379, 0);
lean_inc(x_382);
lean_dec(x_379);
x_383 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_369, x_381);
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
lean_dec(x_383);
x_385 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_366, x_382, x_372, x_384);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = lean_ctor_get(x_386, 2);
lean_inc(x_388);
x_389 = lean_ctor_get(x_386, 3);
lean_inc(x_389);
x_350 = x_386;
x_351 = x_388;
x_352 = x_389;
x_353 = x_368;
x_354 = x_369;
x_355 = x_370;
x_356 = x_371;
x_357 = x_372;
x_358 = x_373;
x_359 = x_374;
x_360 = x_387;
goto block_364;
}
}
else
{
uint8_t x_390; 
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_366);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_1);
x_390 = !lean_is_exclusive(x_378);
if (x_390 == 0)
{
return x_378;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_378, 0);
x_392 = lean_ctor_get(x_378, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_378);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
}
block_397:
{
lean_object* x_395; lean_object* x_396; 
x_395 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_367);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
lean_dec(x_395);
x_368 = x_2;
x_369 = x_3;
x_370 = x_4;
x_371 = x_5;
x_372 = x_6;
x_373 = x_7;
x_374 = x_8;
x_375 = x_396;
goto block_394;
}
}
case 3:
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_399 = lean_ctor_get(x_1, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_1, 1);
lean_inc(x_400);
x_401 = lean_st_ref_get(x_3, x_69);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_ctor_get(x_402, 0);
lean_inc(x_404);
lean_dec(x_402);
lean_inc(x_399);
x_405 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_404, x_399, x_53);
lean_dec(x_404);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_421; lean_object* x_427; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
lean_dec(x_405);
lean_inc(x_400);
x_407 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_53, x_400, x_3, x_403);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_410 = x_407;
} else {
 lean_dec_ref(x_407);
 x_410 = lean_box(0);
}
lean_inc(x_408);
x_427 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_406, x_408, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_409);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
lean_inc(x_406);
x_430 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_406, x_3, x_429);
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
lean_dec(x_430);
x_432 = lean_unsigned_to_nat(0u);
x_433 = lean_array_get_size(x_408);
x_434 = lean_nat_dec_lt(x_432, x_433);
if (x_434 == 0)
{
lean_dec(x_433);
lean_dec(x_3);
x_421 = x_431;
goto block_426;
}
else
{
uint8_t x_435; 
x_435 = lean_nat_dec_le(x_433, x_433);
if (x_435 == 0)
{
lean_dec(x_433);
lean_dec(x_3);
x_421 = x_431;
goto block_426;
}
else
{
lean_object* x_436; size_t x_437; size_t x_438; lean_object* x_439; lean_object* x_440; 
x_436 = lean_box(0);
x_437 = 0;
x_438 = lean_usize_of_nat(x_433);
lean_dec(x_433);
x_439 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(x_408, x_437, x_438, x_436, x_3, x_431);
lean_dec(x_3);
x_440 = lean_ctor_get(x_439, 1);
lean_inc(x_440);
lean_dec(x_439);
x_421 = x_440;
goto block_426;
}
}
}
else
{
lean_object* x_441; lean_object* x_442; 
lean_dec(x_410);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_1);
x_441 = lean_ctor_get(x_427, 1);
lean_inc(x_441);
lean_dec(x_427);
x_442 = lean_ctor_get(x_428, 0);
lean_inc(x_442);
lean_dec(x_428);
x_1 = x_442;
x_9 = x_441;
goto _start;
}
}
else
{
uint8_t x_444; 
lean_dec(x_410);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_444 = !lean_is_exclusive(x_427);
if (x_444 == 0)
{
return x_427;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_427, 0);
x_446 = lean_ctor_get(x_427, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_427);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
block_420:
{
if (x_412 == 0)
{
uint8_t x_413; 
x_413 = !lean_is_exclusive(x_1);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_1, 1);
lean_dec(x_414);
x_415 = lean_ctor_get(x_1, 0);
lean_dec(x_415);
lean_ctor_set(x_1, 1, x_408);
lean_ctor_set(x_1, 0, x_406);
if (lean_is_scalar(x_410)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_410;
}
lean_ctor_set(x_416, 0, x_1);
lean_ctor_set(x_416, 1, x_411);
return x_416;
}
else
{
lean_object* x_417; lean_object* x_418; 
lean_dec(x_1);
x_417 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_417, 0, x_406);
lean_ctor_set(x_417, 1, x_408);
if (lean_is_scalar(x_410)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_410;
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_411);
return x_418;
}
}
else
{
lean_object* x_419; 
lean_dec(x_408);
lean_dec(x_406);
if (lean_is_scalar(x_410)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_410;
}
lean_ctor_set(x_419, 0, x_1);
lean_ctor_set(x_419, 1, x_411);
return x_419;
}
}
block_426:
{
uint8_t x_422; 
x_422 = lean_name_eq(x_399, x_406);
lean_dec(x_399);
if (x_422 == 0)
{
lean_dec(x_400);
x_411 = x_421;
x_412 = x_422;
goto block_420;
}
else
{
size_t x_423; size_t x_424; uint8_t x_425; 
x_423 = lean_ptr_addr(x_400);
lean_dec(x_400);
x_424 = lean_ptr_addr(x_408);
x_425 = lean_usize_dec_eq(x_423, x_424);
x_411 = x_421;
x_412 = x_425;
goto block_420;
}
}
}
else
{
lean_object* x_448; 
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_448 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_403);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_448;
}
}
case 4:
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_1, 0);
lean_inc(x_449);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_449);
x_450 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_449, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
x_453 = lean_st_ref_get(x_3, x_452);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_456 = lean_ctor_get(x_449, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_449, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_449, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_449, 3);
lean_inc(x_459);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 lean_ctor_release(x_449, 2);
 lean_ctor_release(x_449, 3);
 x_460 = x_449;
} else {
 lean_dec_ref(x_449);
 x_460 = lean_box(0);
}
x_461 = lean_ctor_get(x_454, 0);
lean_inc(x_461);
lean_dec(x_454);
lean_inc(x_458);
x_462 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_461, x_458, x_53);
lean_dec(x_461);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 x_464 = x_462;
} else {
 lean_dec_ref(x_462);
 x_464 = lean_box(0);
}
x_465 = lean_st_ref_get(x_3, x_455);
x_466 = !lean_is_exclusive(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_467 = lean_ctor_get(x_465, 0);
x_468 = lean_ctor_get(x_465, 1);
x_469 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_459);
lean_inc(x_463);
x_470 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3(x_463, x_53, x_469, x_459, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_468);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_473 = x_470;
} else {
 lean_dec_ref(x_470);
 x_473 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_474 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_471, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_472);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_485; uint8_t x_486; lean_object* x_490; lean_object* x_491; lean_object* x_501; uint8_t x_502; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_477 = x_474;
} else {
 lean_dec_ref(x_474);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_467, 0);
lean_inc(x_478);
lean_dec(x_467);
lean_inc(x_457);
x_479 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_478, x_53, x_457);
lean_dec(x_478);
x_501 = lean_array_get_size(x_475);
x_502 = lean_nat_dec_eq(x_501, x_124);
lean_dec(x_501);
if (x_502 == 0)
{
lean_free_object(x_465);
lean_dec(x_6);
x_490 = x_3;
x_491 = x_476;
goto block_500;
}
else
{
lean_object* x_503; 
x_503 = lean_array_fget(x_475, x_469);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_513; lean_object* x_514; uint8_t x_523; lean_object* x_524; uint8_t x_526; 
lean_free_object(x_465);
x_504 = lean_ctor_get(x_503, 1);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 2);
lean_inc(x_505);
lean_dec(x_503);
x_513 = lean_array_get_size(x_504);
x_526 = lean_nat_dec_lt(x_469, x_513);
if (x_526 == 0)
{
x_523 = x_53;
x_524 = x_476;
goto block_525;
}
else
{
if (x_526 == 0)
{
x_523 = x_53;
x_524 = x_476;
goto block_525;
}
else
{
size_t x_527; size_t x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; 
x_527 = 0;
x_528 = lean_usize_of_nat(x_513);
x_529 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_504, x_527, x_528, x_3, x_476);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_532 = lean_unbox(x_530);
lean_dec(x_530);
x_523 = x_532;
x_524 = x_531;
goto block_525;
}
}
block_512:
{
lean_object* x_507; uint8_t x_508; 
x_507 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_506);
lean_dec(x_3);
x_508 = !lean_is_exclusive(x_507);
if (x_508 == 0)
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_507, 0);
lean_dec(x_509);
lean_ctor_set(x_507, 0, x_505);
return x_507;
}
else
{
lean_object* x_510; lean_object* x_511; 
x_510 = lean_ctor_get(x_507, 1);
lean_inc(x_510);
lean_dec(x_507);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_505);
lean_ctor_set(x_511, 1, x_510);
return x_511;
}
}
block_522:
{
uint8_t x_515; 
x_515 = lean_nat_dec_lt(x_469, x_513);
if (x_515 == 0)
{
lean_dec(x_513);
lean_dec(x_504);
lean_dec(x_6);
x_506 = x_514;
goto block_512;
}
else
{
uint8_t x_516; 
x_516 = lean_nat_dec_le(x_513, x_513);
if (x_516 == 0)
{
lean_dec(x_513);
lean_dec(x_504);
lean_dec(x_6);
x_506 = x_514;
goto block_512;
}
else
{
lean_object* x_517; size_t x_518; size_t x_519; lean_object* x_520; lean_object* x_521; 
x_517 = lean_box(0);
x_518 = 0;
x_519 = lean_usize_of_nat(x_513);
lean_dec(x_513);
x_520 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_504, x_518, x_519, x_517, x_6, x_514);
lean_dec(x_6);
lean_dec(x_504);
x_521 = lean_ctor_get(x_520, 1);
lean_inc(x_521);
lean_dec(x_520);
x_506 = x_521;
goto block_512;
}
}
}
block_525:
{
if (x_523 == 0)
{
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_1);
x_514 = x_524;
goto block_522;
}
else
{
if (x_53 == 0)
{
lean_dec(x_513);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_6);
x_490 = x_3;
x_491 = x_524;
goto block_500;
}
else
{
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_1);
x_514 = x_524;
goto block_522;
}
}
}
}
else
{
lean_object* x_533; 
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_533 = lean_ctor_get(x_503, 0);
lean_inc(x_533);
lean_dec(x_503);
lean_ctor_set(x_465, 1, x_476);
lean_ctor_set(x_465, 0, x_533);
return x_465;
}
}
block_484:
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
if (lean_is_scalar(x_460)) {
 x_481 = lean_alloc_ctor(0, 4, 0);
} else {
 x_481 = x_460;
}
lean_ctor_set(x_481, 0, x_456);
lean_ctor_set(x_481, 1, x_479);
lean_ctor_set(x_481, 2, x_463);
lean_ctor_set(x_481, 3, x_475);
if (lean_is_scalar(x_464)) {
 x_482 = lean_alloc_ctor(4, 1, 0);
} else {
 x_482 = x_464;
 lean_ctor_set_tag(x_482, 4);
}
lean_ctor_set(x_482, 0, x_481);
if (lean_is_scalar(x_477)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_477;
}
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_480);
return x_483;
}
block_489:
{
if (x_486 == 0)
{
lean_dec(x_473);
lean_dec(x_458);
lean_dec(x_1);
x_480 = x_485;
goto block_484;
}
else
{
uint8_t x_487; 
x_487 = lean_name_eq(x_458, x_463);
lean_dec(x_458);
if (x_487 == 0)
{
lean_dec(x_473);
lean_dec(x_1);
x_480 = x_485;
goto block_484;
}
else
{
lean_object* x_488; 
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_475);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_456);
if (lean_is_scalar(x_473)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_473;
}
lean_ctor_set(x_488, 0, x_1);
lean_ctor_set(x_488, 1, x_485);
return x_488;
}
}
}
block_500:
{
lean_object* x_492; lean_object* x_493; size_t x_494; size_t x_495; uint8_t x_496; 
lean_inc(x_463);
x_492 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_463, x_490, x_491);
lean_dec(x_490);
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
lean_dec(x_492);
x_494 = lean_ptr_addr(x_459);
lean_dec(x_459);
x_495 = lean_ptr_addr(x_475);
x_496 = lean_usize_dec_eq(x_494, x_495);
if (x_496 == 0)
{
lean_dec(x_457);
x_485 = x_493;
x_486 = x_496;
goto block_489;
}
else
{
size_t x_497; size_t x_498; uint8_t x_499; 
x_497 = lean_ptr_addr(x_457);
lean_dec(x_457);
x_498 = lean_ptr_addr(x_479);
x_499 = lean_usize_dec_eq(x_497, x_498);
x_485 = x_493;
x_486 = x_499;
goto block_489;
}
}
}
else
{
uint8_t x_534; 
lean_dec(x_473);
lean_free_object(x_465);
lean_dec(x_467);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_534 = !lean_is_exclusive(x_474);
if (x_534 == 0)
{
return x_474;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_474, 0);
x_536 = lean_ctor_get(x_474, 1);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_474);
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set(x_537, 1, x_536);
return x_537;
}
}
}
else
{
uint8_t x_538; 
lean_free_object(x_465);
lean_dec(x_467);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_538 = !lean_is_exclusive(x_470);
if (x_538 == 0)
{
return x_470;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_470, 0);
x_540 = lean_ctor_get(x_470, 1);
lean_inc(x_540);
lean_inc(x_539);
lean_dec(x_470);
x_541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_541, 0, x_539);
lean_ctor_set(x_541, 1, x_540);
return x_541;
}
}
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_542 = lean_ctor_get(x_465, 0);
x_543 = lean_ctor_get(x_465, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_465);
x_544 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_459);
lean_inc(x_463);
x_545 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3(x_463, x_53, x_544, x_459, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_543);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_548 = x_545;
} else {
 lean_dec_ref(x_545);
 x_548 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_549 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_546, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_547);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_560; uint8_t x_561; lean_object* x_565; lean_object* x_566; lean_object* x_576; uint8_t x_577; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_552 = x_549;
} else {
 lean_dec_ref(x_549);
 x_552 = lean_box(0);
}
x_553 = lean_ctor_get(x_542, 0);
lean_inc(x_553);
lean_dec(x_542);
lean_inc(x_457);
x_554 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_553, x_53, x_457);
lean_dec(x_553);
x_576 = lean_array_get_size(x_550);
x_577 = lean_nat_dec_eq(x_576, x_124);
lean_dec(x_576);
if (x_577 == 0)
{
lean_dec(x_6);
x_565 = x_3;
x_566 = x_551;
goto block_575;
}
else
{
lean_object* x_578; 
x_578 = lean_array_fget(x_550, x_544);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_587; lean_object* x_588; uint8_t x_597; lean_object* x_598; uint8_t x_600; 
x_579 = lean_ctor_get(x_578, 1);
lean_inc(x_579);
x_580 = lean_ctor_get(x_578, 2);
lean_inc(x_580);
lean_dec(x_578);
x_587 = lean_array_get_size(x_579);
x_600 = lean_nat_dec_lt(x_544, x_587);
if (x_600 == 0)
{
x_597 = x_53;
x_598 = x_551;
goto block_599;
}
else
{
if (x_600 == 0)
{
x_597 = x_53;
x_598 = x_551;
goto block_599;
}
else
{
size_t x_601; size_t x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; uint8_t x_606; 
x_601 = 0;
x_602 = lean_usize_of_nat(x_587);
x_603 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_579, x_601, x_602, x_3, x_551);
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
x_606 = lean_unbox(x_604);
lean_dec(x_604);
x_597 = x_606;
x_598 = x_605;
goto block_599;
}
}
block_586:
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_582 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_581);
lean_dec(x_3);
x_583 = lean_ctor_get(x_582, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_584 = x_582;
} else {
 lean_dec_ref(x_582);
 x_584 = lean_box(0);
}
if (lean_is_scalar(x_584)) {
 x_585 = lean_alloc_ctor(0, 2, 0);
} else {
 x_585 = x_584;
}
lean_ctor_set(x_585, 0, x_580);
lean_ctor_set(x_585, 1, x_583);
return x_585;
}
block_596:
{
uint8_t x_589; 
x_589 = lean_nat_dec_lt(x_544, x_587);
if (x_589 == 0)
{
lean_dec(x_587);
lean_dec(x_579);
lean_dec(x_6);
x_581 = x_588;
goto block_586;
}
else
{
uint8_t x_590; 
x_590 = lean_nat_dec_le(x_587, x_587);
if (x_590 == 0)
{
lean_dec(x_587);
lean_dec(x_579);
lean_dec(x_6);
x_581 = x_588;
goto block_586;
}
else
{
lean_object* x_591; size_t x_592; size_t x_593; lean_object* x_594; lean_object* x_595; 
x_591 = lean_box(0);
x_592 = 0;
x_593 = lean_usize_of_nat(x_587);
lean_dec(x_587);
x_594 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_579, x_592, x_593, x_591, x_6, x_588);
lean_dec(x_6);
lean_dec(x_579);
x_595 = lean_ctor_get(x_594, 1);
lean_inc(x_595);
lean_dec(x_594);
x_581 = x_595;
goto block_586;
}
}
}
block_599:
{
if (x_597 == 0)
{
lean_dec(x_554);
lean_dec(x_552);
lean_dec(x_550);
lean_dec(x_548);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_1);
x_588 = x_598;
goto block_596;
}
else
{
if (x_53 == 0)
{
lean_dec(x_587);
lean_dec(x_580);
lean_dec(x_579);
lean_dec(x_6);
x_565 = x_3;
x_566 = x_598;
goto block_575;
}
else
{
lean_dec(x_554);
lean_dec(x_552);
lean_dec(x_550);
lean_dec(x_548);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_1);
x_588 = x_598;
goto block_596;
}
}
}
}
else
{
lean_object* x_607; lean_object* x_608; 
lean_dec(x_554);
lean_dec(x_552);
lean_dec(x_550);
lean_dec(x_548);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_607 = lean_ctor_get(x_578, 0);
lean_inc(x_607);
lean_dec(x_578);
x_608 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_608, 0, x_607);
lean_ctor_set(x_608, 1, x_551);
return x_608;
}
}
block_559:
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
if (lean_is_scalar(x_460)) {
 x_556 = lean_alloc_ctor(0, 4, 0);
} else {
 x_556 = x_460;
}
lean_ctor_set(x_556, 0, x_456);
lean_ctor_set(x_556, 1, x_554);
lean_ctor_set(x_556, 2, x_463);
lean_ctor_set(x_556, 3, x_550);
if (lean_is_scalar(x_464)) {
 x_557 = lean_alloc_ctor(4, 1, 0);
} else {
 x_557 = x_464;
 lean_ctor_set_tag(x_557, 4);
}
lean_ctor_set(x_557, 0, x_556);
if (lean_is_scalar(x_552)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_552;
}
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_555);
return x_558;
}
block_564:
{
if (x_561 == 0)
{
lean_dec(x_548);
lean_dec(x_458);
lean_dec(x_1);
x_555 = x_560;
goto block_559;
}
else
{
uint8_t x_562; 
x_562 = lean_name_eq(x_458, x_463);
lean_dec(x_458);
if (x_562 == 0)
{
lean_dec(x_548);
lean_dec(x_1);
x_555 = x_560;
goto block_559;
}
else
{
lean_object* x_563; 
lean_dec(x_554);
lean_dec(x_552);
lean_dec(x_550);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_456);
if (lean_is_scalar(x_548)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_548;
}
lean_ctor_set(x_563, 0, x_1);
lean_ctor_set(x_563, 1, x_560);
return x_563;
}
}
}
block_575:
{
lean_object* x_567; lean_object* x_568; size_t x_569; size_t x_570; uint8_t x_571; 
lean_inc(x_463);
x_567 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_463, x_565, x_566);
lean_dec(x_565);
x_568 = lean_ctor_get(x_567, 1);
lean_inc(x_568);
lean_dec(x_567);
x_569 = lean_ptr_addr(x_459);
lean_dec(x_459);
x_570 = lean_ptr_addr(x_550);
x_571 = lean_usize_dec_eq(x_569, x_570);
if (x_571 == 0)
{
lean_dec(x_457);
x_560 = x_568;
x_561 = x_571;
goto block_564;
}
else
{
size_t x_572; size_t x_573; uint8_t x_574; 
x_572 = lean_ptr_addr(x_457);
lean_dec(x_457);
x_573 = lean_ptr_addr(x_554);
x_574 = lean_usize_dec_eq(x_572, x_573);
x_560 = x_568;
x_561 = x_574;
goto block_564;
}
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_548);
lean_dec(x_542);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_609 = lean_ctor_get(x_549, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_549, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_611 = x_549;
} else {
 lean_dec_ref(x_549);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(1, 2, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_609);
lean_ctor_set(x_612, 1, x_610);
return x_612;
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_542);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_613 = lean_ctor_get(x_545, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_545, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_615 = x_545;
} else {
 lean_dec_ref(x_545);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(1, 2, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_613);
lean_ctor_set(x_616, 1, x_614);
return x_616;
}
}
}
else
{
lean_object* x_617; 
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_617 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_455);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_617;
}
}
else
{
uint8_t x_618; 
lean_dec(x_449);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_618 = !lean_is_exclusive(x_450);
if (x_618 == 0)
{
lean_object* x_619; lean_object* x_620; 
x_619 = lean_ctor_get(x_450, 0);
lean_dec(x_619);
x_620 = lean_ctor_get(x_451, 0);
lean_inc(x_620);
lean_dec(x_451);
lean_ctor_set(x_450, 0, x_620);
return x_450;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_621 = lean_ctor_get(x_450, 1);
lean_inc(x_621);
lean_dec(x_450);
x_622 = lean_ctor_get(x_451, 0);
lean_inc(x_622);
lean_dec(x_451);
x_623 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_621);
return x_623;
}
}
}
else
{
uint8_t x_624; 
lean_dec(x_449);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_624 = !lean_is_exclusive(x_450);
if (x_624 == 0)
{
return x_450;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_625 = lean_ctor_get(x_450, 0);
x_626 = lean_ctor_get(x_450, 1);
lean_inc(x_626);
lean_inc(x_625);
lean_dec(x_450);
x_627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_627, 0, x_625);
lean_ctor_set(x_627, 1, x_626);
return x_627;
}
}
}
case 5:
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
lean_dec(x_4);
lean_dec(x_2);
x_628 = lean_ctor_get(x_1, 0);
lean_inc(x_628);
x_629 = lean_st_ref_get(x_3, x_69);
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec(x_629);
x_632 = lean_ctor_get(x_630, 0);
lean_inc(x_632);
lean_dec(x_630);
lean_inc(x_628);
x_633 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_632, x_628, x_53);
lean_dec(x_632);
if (lean_obj_tag(x_633) == 0)
{
lean_object* x_634; lean_object* x_635; uint8_t x_636; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_634 = lean_ctor_get(x_633, 0);
lean_inc(x_634);
lean_dec(x_633);
lean_inc(x_634);
x_635 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_634, x_3, x_631);
lean_dec(x_3);
x_636 = !lean_is_exclusive(x_635);
if (x_636 == 0)
{
lean_object* x_637; uint8_t x_638; 
x_637 = lean_ctor_get(x_635, 0);
lean_dec(x_637);
x_638 = lean_name_eq(x_628, x_634);
lean_dec(x_628);
if (x_638 == 0)
{
uint8_t x_639; 
x_639 = !lean_is_exclusive(x_1);
if (x_639 == 0)
{
lean_object* x_640; 
x_640 = lean_ctor_get(x_1, 0);
lean_dec(x_640);
lean_ctor_set(x_1, 0, x_634);
lean_ctor_set(x_635, 0, x_1);
return x_635;
}
else
{
lean_object* x_641; 
lean_dec(x_1);
x_641 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_641, 0, x_634);
lean_ctor_set(x_635, 0, x_641);
return x_635;
}
}
else
{
lean_dec(x_634);
lean_ctor_set(x_635, 0, x_1);
return x_635;
}
}
else
{
lean_object* x_642; uint8_t x_643; 
x_642 = lean_ctor_get(x_635, 1);
lean_inc(x_642);
lean_dec(x_635);
x_643 = lean_name_eq(x_628, x_634);
lean_dec(x_628);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_644 = x_1;
} else {
 lean_dec_ref(x_1);
 x_644 = lean_box(0);
}
if (lean_is_scalar(x_644)) {
 x_645 = lean_alloc_ctor(5, 1, 0);
} else {
 x_645 = x_644;
}
lean_ctor_set(x_645, 0, x_634);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_642);
return x_646;
}
else
{
lean_object* x_647; 
lean_dec(x_634);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_1);
lean_ctor_set(x_647, 1, x_642);
return x_647;
}
}
}
else
{
lean_object* x_648; 
lean_dec(x_628);
lean_dec(x_3);
lean_dec(x_1);
x_648 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_631);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_648;
}
}
case 6:
{
lean_object* x_649; lean_object* x_650; uint8_t x_651; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_649 = lean_ctor_get(x_1, 0);
lean_inc(x_649);
x_650 = lean_st_ref_get(x_3, x_69);
lean_dec(x_3);
x_651 = !lean_is_exclusive(x_650);
if (x_651 == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; size_t x_655; size_t x_656; uint8_t x_657; 
x_652 = lean_ctor_get(x_650, 0);
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
lean_dec(x_652);
lean_inc(x_649);
x_654 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_653, x_53, x_649);
lean_dec(x_653);
x_655 = lean_ptr_addr(x_649);
lean_dec(x_649);
x_656 = lean_ptr_addr(x_654);
x_657 = lean_usize_dec_eq(x_655, x_656);
if (x_657 == 0)
{
uint8_t x_658; 
x_658 = !lean_is_exclusive(x_1);
if (x_658 == 0)
{
lean_object* x_659; 
x_659 = lean_ctor_get(x_1, 0);
lean_dec(x_659);
lean_ctor_set(x_1, 0, x_654);
lean_ctor_set(x_650, 0, x_1);
return x_650;
}
else
{
lean_object* x_660; 
lean_dec(x_1);
x_660 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_660, 0, x_654);
lean_ctor_set(x_650, 0, x_660);
return x_650;
}
}
else
{
lean_dec(x_654);
lean_ctor_set(x_650, 0, x_1);
return x_650;
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; size_t x_665; size_t x_666; uint8_t x_667; 
x_661 = lean_ctor_get(x_650, 0);
x_662 = lean_ctor_get(x_650, 1);
lean_inc(x_662);
lean_inc(x_661);
lean_dec(x_650);
x_663 = lean_ctor_get(x_661, 0);
lean_inc(x_663);
lean_dec(x_661);
lean_inc(x_649);
x_664 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_663, x_53, x_649);
lean_dec(x_663);
x_665 = lean_ptr_addr(x_649);
lean_dec(x_649);
x_666 = lean_ptr_addr(x_664);
x_667 = lean_usize_dec_eq(x_665, x_666);
if (x_667 == 0)
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_668 = x_1;
} else {
 lean_dec_ref(x_1);
 x_668 = lean_box(0);
}
if (lean_is_scalar(x_668)) {
 x_669 = lean_alloc_ctor(6, 1, 0);
} else {
 x_669 = x_668;
}
lean_ctor_set(x_669, 0, x_664);
x_670 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_670, 0, x_669);
lean_ctor_set(x_670, 1, x_662);
return x_670;
}
else
{
lean_object* x_671; 
lean_dec(x_664);
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_1);
lean_ctor_set(x_671, 1, x_662);
return x_671;
}
}
}
default: 
{
lean_object* x_672; lean_object* x_673; 
x_672 = lean_ctor_get(x_1, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_1, 1);
lean_inc(x_673);
x_70 = x_672;
x_71 = x_673;
x_72 = x_2;
x_73 = x_3;
x_74 = x_4;
x_75 = x_5;
x_76 = x_6;
x_77 = x_7;
x_78 = x_8;
goto block_123;
}
}
block_123:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_70, 3);
lean_inc(x_81);
x_82 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_79, x_73, x_69);
lean_dec(x_79);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_83);
lean_inc(x_1);
lean_inc(x_71);
x_85 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_85, 0, x_71);
lean_closure_set(x_85, 1, x_1);
lean_closure_set(x_85, 2, x_83);
x_86 = lean_unbox(x_83);
if (x_86 == 0)
{
uint8_t x_87; 
lean_dec(x_83);
lean_dec(x_71);
x_87 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_87 == 0)
{
lean_dec(x_81);
lean_dec(x_80);
x_10 = x_85;
x_11 = x_70;
x_12 = x_72;
x_13 = x_73;
x_14 = x_74;
x_15 = x_75;
x_16 = x_76;
x_17 = x_77;
x_18 = x_78;
x_19 = x_84;
goto block_29;
}
else
{
uint8_t x_88; 
x_88 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_81, x_80);
lean_dec(x_80);
if (x_88 == 0)
{
x_10 = x_85;
x_11 = x_70;
x_12 = x_72;
x_13 = x_73;
x_14 = x_74;
x_15 = x_75;
x_16 = x_76;
x_17 = x_77;
x_18 = x_78;
x_19 = x_84;
goto block_29;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_st_ref_get(x_73, x_84);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
x_93 = l_Lean_Compiler_LCNF_normFunDeclImp(x_53, x_70, x_92, x_75, x_76, x_77, x_78, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
x_96 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_94, x_75, x_76, x_77, x_78, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_73, x_98);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_10 = x_85;
x_11 = x_97;
x_12 = x_72;
x_13 = x_73;
x_14 = x_74;
x_15 = x_75;
x_16 = x_76;
x_17 = x_77;
x_18 = x_78;
x_19 = x_100;
goto block_29;
}
else
{
uint8_t x_101; 
lean_dec(x_85);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
x_101 = !lean_is_exclusive(x_96);
if (x_101 == 0)
{
return x_96;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_96, 0);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_96);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_85);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
x_105 = !lean_is_exclusive(x_93);
if (x_105 == 0)
{
return x_93;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_93, 0);
x_107 = lean_ctor_get(x_93, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_93);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_85);
lean_dec(x_81);
lean_dec(x_80);
x_109 = lean_st_ref_get(x_73, x_84);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
x_113 = l_Lean_Compiler_LCNF_normFunDeclImp(x_53, x_70, x_112, x_75, x_76, x_77, x_78, x_111);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_box(0);
x_117 = lean_unbox(x_83);
lean_dec(x_83);
x_118 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_71, x_1, x_117, x_114, x_116, x_72, x_73, x_74, x_75, x_76, x_77, x_78, x_115);
return x_118;
}
else
{
uint8_t x_119; 
lean_dec(x_83);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_113);
if (x_119 == 0)
{
return x_113;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_113, 0);
x_121 = lean_ctor_get(x_113, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_113);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_dec(x_7);
x_674 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3, x_9);
x_675 = lean_ctor_get(x_674, 1);
lean_inc(x_675);
lean_dec(x_674);
x_730 = lean_unsigned_to_nat(1u);
x_731 = lean_nat_add(x_41, x_730);
lean_dec(x_41);
x_732 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_732, 0, x_38);
lean_ctor_set(x_732, 1, x_39);
lean_ctor_set(x_732, 2, x_40);
lean_ctor_set(x_732, 3, x_731);
lean_ctor_set(x_732, 4, x_42);
lean_ctor_set(x_732, 5, x_43);
lean_ctor_set(x_732, 6, x_44);
lean_ctor_set(x_732, 7, x_45);
lean_ctor_set(x_732, 8, x_46);
lean_ctor_set(x_732, 9, x_47);
lean_ctor_set(x_732, 10, x_48);
lean_ctor_set(x_732, 11, x_50);
lean_ctor_set(x_732, 12, x_52);
lean_ctor_set_uint8(x_732, sizeof(void*)*13, x_49);
lean_ctor_set_uint8(x_732, sizeof(void*)*13 + 1, x_51);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; uint8_t x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; uint8_t x_768; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; uint8_t x_965; 
x_733 = lean_ctor_get(x_1, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_1, 1);
lean_inc(x_734);
lean_inc(x_733);
x_932 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_53, x_733, x_3, x_6, x_675);
x_933 = lean_ctor_get(x_932, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_932, 1);
lean_inc(x_934);
lean_dec(x_932);
x_965 = l_Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_2068_(x_733, x_933);
if (x_965 == 0)
{
goto block_964;
}
else
{
if (x_53 == 0)
{
x_935 = x_2;
x_936 = x_3;
x_937 = x_4;
x_938 = x_5;
x_939 = x_6;
x_940 = x_732;
x_941 = x_8;
x_942 = x_934;
goto block_961;
}
else
{
goto block_964;
}
}
block_758:
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_752 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_752, 0, x_751);
lean_ctor_set(x_752, 1, x_738);
lean_ctor_set(x_752, 2, x_739);
lean_ctor_set(x_752, 3, x_740);
lean_ctor_set(x_752, 4, x_742);
lean_ctor_set(x_752, 5, x_743);
lean_ctor_set(x_752, 6, x_744);
lean_ctor_set_uint8(x_752, sizeof(void*)*7, x_741);
x_753 = lean_st_ref_set(x_750, x_752, x_748);
x_754 = lean_ctor_get(x_753, 1);
lean_inc(x_754);
lean_dec(x_753);
x_755 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_745, x_750, x_749, x_754);
lean_dec(x_745);
x_756 = lean_ctor_get(x_755, 1);
lean_inc(x_756);
lean_dec(x_755);
x_1 = x_734;
x_2 = x_736;
x_3 = x_750;
x_4 = x_735;
x_5 = x_747;
x_6 = x_749;
x_7 = x_737;
x_8 = x_746;
x_9 = x_756;
goto _start;
}
block_916:
{
if (x_768 == 0)
{
lean_object* x_769; 
lean_inc(x_764);
lean_inc(x_762);
lean_inc(x_766);
lean_inc(x_765);
lean_inc(x_763);
x_769 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_763, x_765, x_766, x_762, x_764, x_759);
if (lean_obj_tag(x_769) == 0)
{
lean_object* x_770; 
x_770 = lean_ctor_get(x_769, 0);
lean_inc(x_770);
if (lean_obj_tag(x_770) == 0)
{
lean_object* x_771; lean_object* x_772; 
x_771 = lean_ctor_get(x_769, 1);
lean_inc(x_771);
lean_dec(x_769);
lean_inc(x_764);
lean_inc(x_762);
lean_inc(x_766);
lean_inc(x_765);
lean_inc(x_763);
x_772 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg(x_763, x_761, x_767, x_765, x_766, x_762, x_764, x_771);
if (lean_obj_tag(x_772) == 0)
{
lean_object* x_773; 
x_773 = lean_ctor_get(x_772, 0);
lean_inc(x_773);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_774 = lean_ctor_get(x_772, 1);
lean_inc(x_774);
lean_dec(x_772);
x_775 = lean_ctor_get(x_763, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_763, 3);
lean_inc(x_776);
lean_inc(x_776);
x_777 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_776, x_774);
x_778 = lean_ctor_get(x_777, 0);
lean_inc(x_778);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; 
x_779 = lean_ctor_get(x_777, 1);
lean_inc(x_779);
lean_dec(x_777);
lean_inc(x_764);
lean_inc(x_762);
lean_inc(x_766);
lean_inc(x_765);
lean_inc(x_760);
lean_inc(x_767);
lean_inc(x_761);
lean_inc(x_734);
lean_inc(x_763);
x_780 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_763, x_734, x_761, x_767, x_760, x_765, x_766, x_762, x_764, x_779);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; lean_object* x_783; 
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
lean_inc(x_764);
lean_inc(x_762);
lean_inc(x_766);
lean_inc(x_765);
lean_inc(x_760);
lean_inc(x_767);
lean_inc(x_761);
x_783 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_776, x_761, x_767, x_760, x_765, x_766, x_762, x_764, x_782);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; 
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; 
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
lean_dec(x_783);
lean_inc(x_764);
lean_inc(x_762);
lean_inc(x_766);
lean_inc(x_765);
lean_inc(x_760);
lean_inc(x_767);
lean_inc(x_761);
lean_inc(x_734);
x_786 = l_Lean_Compiler_LCNF_Simp_simp(x_734, x_761, x_767, x_760, x_765, x_766, x_762, x_764, x_785);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec(x_786);
x_789 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_775, x_767, x_788);
lean_dec(x_775);
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_unbox(x_790);
lean_dec(x_790);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_1);
x_792 = lean_ctor_get(x_789, 1);
lean_inc(x_792);
lean_dec(x_789);
x_793 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_763, x_767, x_766, x_792);
lean_dec(x_766);
lean_dec(x_767);
lean_dec(x_763);
x_794 = lean_ctor_get(x_793, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_793)) {
 lean_ctor_release(x_793, 0);
 lean_ctor_release(x_793, 1);
 x_795 = x_793;
} else {
 lean_dec_ref(x_793);
 x_795 = lean_box(0);
}
if (lean_is_scalar(x_795)) {
 x_796 = lean_alloc_ctor(0, 2, 0);
} else {
 x_796 = x_795;
}
lean_ctor_set(x_796, 0, x_787);
lean_ctor_set(x_796, 1, x_794);
return x_796;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; size_t x_800; size_t x_801; uint8_t x_802; 
x_797 = lean_ctor_get(x_789, 1);
lean_inc(x_797);
lean_dec(x_789);
lean_inc(x_763);
x_798 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_763, x_761, x_767, x_760, x_765, x_766, x_762, x_764, x_797);
lean_dec(x_764);
lean_dec(x_762);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_760);
lean_dec(x_767);
lean_dec(x_761);
x_799 = lean_ctor_get(x_798, 1);
lean_inc(x_799);
lean_dec(x_798);
x_800 = lean_ptr_addr(x_734);
lean_dec(x_734);
x_801 = lean_ptr_addr(x_787);
x_802 = lean_usize_dec_eq(x_800, x_801);
if (x_802 == 0)
{
lean_dec(x_733);
x_30 = x_799;
x_31 = x_763;
x_32 = x_787;
x_33 = x_802;
goto block_37;
}
else
{
size_t x_803; size_t x_804; uint8_t x_805; 
x_803 = lean_ptr_addr(x_733);
lean_dec(x_733);
x_804 = lean_ptr_addr(x_763);
x_805 = lean_usize_dec_eq(x_803, x_804);
x_30 = x_799;
x_31 = x_763;
x_32 = x_787;
x_33 = x_805;
goto block_37;
}
}
}
else
{
lean_dec(x_775);
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_1);
return x_786;
}
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_733);
lean_dec(x_1);
x_806 = lean_ctor_get(x_784, 0);
lean_inc(x_806);
lean_dec(x_784);
x_807 = lean_ctor_get(x_783, 1);
lean_inc(x_807);
lean_dec(x_783);
x_808 = lean_ctor_get(x_806, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_806, 1);
lean_inc(x_809);
lean_dec(x_806);
x_810 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_775, x_809, x_767, x_766, x_762, x_764, x_807);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_810, 1);
lean_inc(x_811);
lean_dec(x_810);
x_812 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_763, x_767, x_766, x_811);
lean_dec(x_763);
x_813 = lean_ctor_get(x_812, 1);
lean_inc(x_813);
lean_dec(x_812);
lean_inc(x_764);
lean_inc(x_762);
lean_inc(x_766);
lean_inc(x_765);
lean_inc(x_760);
lean_inc(x_767);
lean_inc(x_761);
x_814 = l_Lean_Compiler_LCNF_Simp_simp(x_734, x_761, x_767, x_760, x_765, x_766, x_762, x_764, x_813);
if (lean_obj_tag(x_814) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_815 = lean_ctor_get(x_814, 0);
lean_inc(x_815);
x_816 = lean_ctor_get(x_814, 1);
lean_inc(x_816);
lean_dec(x_814);
x_817 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_808, x_815, x_761, x_767, x_760, x_765, x_766, x_762, x_764, x_816);
lean_dec(x_764);
lean_dec(x_762);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_760);
lean_dec(x_767);
lean_dec(x_761);
lean_dec(x_808);
return x_817;
}
else
{
lean_dec(x_808);
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
return x_814;
}
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
lean_dec(x_808);
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_734);
x_818 = lean_ctor_get(x_810, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_810, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 x_820 = x_810;
} else {
 lean_dec_ref(x_810);
 x_820 = lean_box(0);
}
if (lean_is_scalar(x_820)) {
 x_821 = lean_alloc_ctor(1, 2, 0);
} else {
 x_821 = x_820;
}
lean_ctor_set(x_821, 0, x_818);
lean_ctor_set(x_821, 1, x_819);
return x_821;
}
}
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
lean_dec(x_775);
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_1);
x_822 = lean_ctor_get(x_783, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_783, 1);
lean_inc(x_823);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 lean_ctor_release(x_783, 1);
 x_824 = x_783;
} else {
 lean_dec_ref(x_783);
 x_824 = lean_box(0);
}
if (lean_is_scalar(x_824)) {
 x_825 = lean_alloc_ctor(1, 2, 0);
} else {
 x_825 = x_824;
}
lean_ctor_set(x_825, 0, x_822);
lean_ctor_set(x_825, 1, x_823);
return x_825;
}
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_1);
x_826 = lean_ctor_get(x_780, 1);
lean_inc(x_826);
lean_dec(x_780);
x_827 = lean_ctor_get(x_781, 0);
lean_inc(x_827);
lean_dec(x_781);
x_828 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_763, x_767, x_766, x_826);
lean_dec(x_766);
lean_dec(x_767);
lean_dec(x_763);
x_829 = lean_ctor_get(x_828, 1);
lean_inc(x_829);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_830 = x_828;
} else {
 lean_dec_ref(x_828);
 x_830 = lean_box(0);
}
if (lean_is_scalar(x_830)) {
 x_831 = lean_alloc_ctor(0, 2, 0);
} else {
 x_831 = x_830;
}
lean_ctor_set(x_831, 0, x_827);
lean_ctor_set(x_831, 1, x_829);
return x_831;
}
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_1);
x_832 = lean_ctor_get(x_780, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_780, 1);
lean_inc(x_833);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 x_834 = x_780;
} else {
 lean_dec_ref(x_780);
 x_834 = lean_box(0);
}
if (lean_is_scalar(x_834)) {
 x_835 = lean_alloc_ctor(1, 2, 0);
} else {
 x_835 = x_834;
}
lean_ctor_set(x_835, 0, x_832);
lean_ctor_set(x_835, 1, x_833);
return x_835;
}
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
lean_dec(x_776);
lean_dec(x_733);
lean_dec(x_1);
x_836 = lean_ctor_get(x_777, 1);
lean_inc(x_836);
lean_dec(x_777);
x_837 = lean_ctor_get(x_778, 0);
lean_inc(x_837);
lean_dec(x_778);
x_838 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_775, x_837, x_767, x_766, x_762, x_764, x_836);
if (lean_obj_tag(x_838) == 0)
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_839 = lean_ctor_get(x_838, 1);
lean_inc(x_839);
lean_dec(x_838);
x_840 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_763, x_767, x_766, x_839);
lean_dec(x_763);
x_841 = lean_ctor_get(x_840, 1);
lean_inc(x_841);
lean_dec(x_840);
x_1 = x_734;
x_2 = x_761;
x_3 = x_767;
x_4 = x_760;
x_5 = x_765;
x_6 = x_766;
x_7 = x_762;
x_8 = x_764;
x_9 = x_841;
goto _start;
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_734);
x_843 = lean_ctor_get(x_838, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_838, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_838)) {
 lean_ctor_release(x_838, 0);
 lean_ctor_release(x_838, 1);
 x_845 = x_838;
} else {
 lean_dec_ref(x_838);
 x_845 = lean_box(0);
}
if (lean_is_scalar(x_845)) {
 x_846 = lean_alloc_ctor(1, 2, 0);
} else {
 x_846 = x_845;
}
lean_ctor_set(x_846, 0, x_843);
lean_ctor_set(x_846, 1, x_844);
return x_846;
}
}
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_763);
lean_dec(x_733);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_847 = x_1;
} else {
 lean_dec_ref(x_1);
 x_847 = lean_box(0);
}
x_848 = lean_ctor_get(x_772, 1);
lean_inc(x_848);
lean_dec(x_772);
x_849 = lean_ctor_get(x_773, 0);
lean_inc(x_849);
lean_dec(x_773);
if (lean_is_scalar(x_847)) {
 x_850 = lean_alloc_ctor(1, 2, 0);
} else {
 x_850 = x_847;
 lean_ctor_set_tag(x_850, 1);
}
lean_ctor_set(x_850, 0, x_849);
lean_ctor_set(x_850, 1, x_734);
x_1 = x_850;
x_2 = x_761;
x_3 = x_767;
x_4 = x_760;
x_5 = x_765;
x_6 = x_766;
x_7 = x_762;
x_8 = x_764;
x_9 = x_848;
goto _start;
}
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_1);
x_852 = lean_ctor_get(x_772, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_772, 1);
lean_inc(x_853);
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 lean_ctor_release(x_772, 1);
 x_854 = x_772;
} else {
 lean_dec_ref(x_772);
 x_854 = lean_box(0);
}
if (lean_is_scalar(x_854)) {
 x_855 = lean_alloc_ctor(1, 2, 0);
} else {
 x_855 = x_854;
}
lean_ctor_set(x_855, 0, x_852);
lean_ctor_set(x_855, 1, x_853);
return x_855;
}
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
lean_dec(x_763);
lean_dec(x_733);
lean_dec(x_1);
x_856 = lean_ctor_get(x_769, 1);
lean_inc(x_856);
lean_dec(x_769);
x_857 = lean_ctor_get(x_770, 0);
lean_inc(x_857);
lean_dec(x_770);
x_858 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_767, x_856);
x_859 = lean_ctor_get(x_858, 1);
lean_inc(x_859);
lean_dec(x_858);
lean_inc(x_764);
lean_inc(x_762);
lean_inc(x_766);
lean_inc(x_765);
lean_inc(x_760);
lean_inc(x_767);
lean_inc(x_761);
x_860 = l_Lean_Compiler_LCNF_Simp_simp(x_734, x_761, x_767, x_760, x_765, x_766, x_762, x_764, x_859);
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
lean_dec(x_860);
x_863 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_857, x_861, x_761, x_767, x_760, x_765, x_766, x_762, x_764, x_862);
lean_dec(x_764);
lean_dec(x_762);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_760);
lean_dec(x_767);
lean_dec(x_761);
lean_dec(x_857);
return x_863;
}
else
{
lean_dec(x_857);
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
return x_860;
}
}
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_1);
x_864 = lean_ctor_get(x_769, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_769, 1);
lean_inc(x_865);
if (lean_is_exclusive(x_769)) {
 lean_ctor_release(x_769, 0);
 lean_ctor_release(x_769, 1);
 x_866 = x_769;
} else {
 lean_dec_ref(x_769);
 x_866 = lean_box(0);
}
if (lean_is_scalar(x_866)) {
 x_867 = lean_alloc_ctor(1, 2, 0);
} else {
 x_867 = x_866;
}
lean_ctor_set(x_867, 0, x_864);
lean_ctor_set(x_867, 1, x_865);
return x_867;
}
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; uint8_t x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; uint64_t x_885; uint64_t x_886; uint64_t x_887; uint64_t x_888; uint64_t x_889; uint64_t x_890; uint64_t x_891; size_t x_892; size_t x_893; size_t x_894; size_t x_895; size_t x_896; lean_object* x_897; uint8_t x_898; 
lean_dec(x_733);
lean_dec(x_1);
x_868 = lean_st_ref_take(x_767, x_759);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_868, 1);
lean_inc(x_871);
lean_dec(x_868);
x_872 = lean_ctor_get(x_869, 1);
lean_inc(x_872);
x_873 = lean_ctor_get(x_869, 2);
lean_inc(x_873);
x_874 = lean_ctor_get(x_869, 3);
lean_inc(x_874);
x_875 = lean_ctor_get_uint8(x_869, sizeof(void*)*7);
x_876 = lean_ctor_get(x_869, 4);
lean_inc(x_876);
x_877 = lean_ctor_get(x_869, 5);
lean_inc(x_877);
x_878 = lean_ctor_get(x_869, 6);
lean_inc(x_878);
lean_dec(x_869);
x_879 = lean_ctor_get(x_870, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_870, 1);
lean_inc(x_880);
if (lean_is_exclusive(x_870)) {
 lean_ctor_release(x_870, 0);
 lean_ctor_release(x_870, 1);
 x_881 = x_870;
} else {
 lean_dec_ref(x_870);
 x_881 = lean_box(0);
}
x_882 = lean_ctor_get(x_763, 0);
lean_inc(x_882);
x_883 = lean_box(0);
x_884 = lean_array_get_size(x_880);
x_885 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_882);
x_886 = 32;
x_887 = lean_uint64_shift_right(x_885, x_886);
x_888 = lean_uint64_xor(x_885, x_887);
x_889 = 16;
x_890 = lean_uint64_shift_right(x_888, x_889);
x_891 = lean_uint64_xor(x_888, x_890);
x_892 = lean_uint64_to_usize(x_891);
x_893 = lean_usize_of_nat(x_884);
lean_dec(x_884);
x_894 = 1;
x_895 = lean_usize_sub(x_893, x_894);
x_896 = lean_usize_land(x_892, x_895);
x_897 = lean_array_uget(x_880, x_896);
x_898 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_882, x_897);
if (x_898 == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; uint8_t x_907; 
x_899 = lean_nat_add(x_879, x_730);
lean_dec(x_879);
x_900 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_900, 0, x_882);
lean_ctor_set(x_900, 1, x_883);
lean_ctor_set(x_900, 2, x_897);
x_901 = lean_array_uset(x_880, x_896, x_900);
x_902 = lean_unsigned_to_nat(4u);
x_903 = lean_nat_mul(x_899, x_902);
x_904 = lean_unsigned_to_nat(3u);
x_905 = lean_nat_div(x_903, x_904);
lean_dec(x_903);
x_906 = lean_array_get_size(x_901);
x_907 = lean_nat_dec_le(x_905, x_906);
lean_dec(x_906);
lean_dec(x_905);
if (x_907 == 0)
{
lean_object* x_908; lean_object* x_909; 
x_908 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_901);
if (lean_is_scalar(x_881)) {
 x_909 = lean_alloc_ctor(0, 2, 0);
} else {
 x_909 = x_881;
}
lean_ctor_set(x_909, 0, x_899);
lean_ctor_set(x_909, 1, x_908);
x_735 = x_760;
x_736 = x_761;
x_737 = x_762;
x_738 = x_872;
x_739 = x_873;
x_740 = x_874;
x_741 = x_875;
x_742 = x_876;
x_743 = x_877;
x_744 = x_878;
x_745 = x_763;
x_746 = x_764;
x_747 = x_765;
x_748 = x_871;
x_749 = x_766;
x_750 = x_767;
x_751 = x_909;
goto block_758;
}
else
{
lean_object* x_910; 
if (lean_is_scalar(x_881)) {
 x_910 = lean_alloc_ctor(0, 2, 0);
} else {
 x_910 = x_881;
}
lean_ctor_set(x_910, 0, x_899);
lean_ctor_set(x_910, 1, x_901);
x_735 = x_760;
x_736 = x_761;
x_737 = x_762;
x_738 = x_872;
x_739 = x_873;
x_740 = x_874;
x_741 = x_875;
x_742 = x_876;
x_743 = x_877;
x_744 = x_878;
x_745 = x_763;
x_746 = x_764;
x_747 = x_765;
x_748 = x_871;
x_749 = x_766;
x_750 = x_767;
x_751 = x_910;
goto block_758;
}
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_911 = lean_box(0);
x_912 = lean_array_uset(x_880, x_896, x_911);
x_913 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_882, x_883, x_897);
x_914 = lean_array_uset(x_912, x_896, x_913);
if (lean_is_scalar(x_881)) {
 x_915 = lean_alloc_ctor(0, 2, 0);
} else {
 x_915 = x_881;
}
lean_ctor_set(x_915, 0, x_879);
lean_ctor_set(x_915, 1, x_914);
x_735 = x_760;
x_736 = x_761;
x_737 = x_762;
x_738 = x_872;
x_739 = x_873;
x_740 = x_874;
x_741 = x_875;
x_742 = x_876;
x_743 = x_877;
x_744 = x_878;
x_745 = x_763;
x_746 = x_764;
x_747 = x_765;
x_748 = x_871;
x_749 = x_766;
x_750 = x_767;
x_751 = x_915;
goto block_758;
}
}
}
block_931:
{
uint8_t x_928; 
x_928 = l_Lean_Expr_isErased(x_918);
lean_dec(x_918);
if (x_928 == 0)
{
lean_dec(x_919);
x_759 = x_927;
x_760 = x_922;
x_761 = x_920;
x_762 = x_925;
x_763 = x_917;
x_764 = x_926;
x_765 = x_923;
x_766 = x_924;
x_767 = x_921;
x_768 = x_53;
goto block_916;
}
else
{
lean_object* x_929; uint8_t x_930; 
x_929 = lean_box(1);
x_930 = l_Lean_Compiler_LCNF_beqLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1208_(x_919, x_929);
lean_dec(x_919);
if (x_930 == 0)
{
x_759 = x_927;
x_760 = x_922;
x_761 = x_920;
x_762 = x_925;
x_763 = x_917;
x_764 = x_926;
x_765 = x_923;
x_766 = x_924;
x_767 = x_921;
x_768 = x_928;
goto block_916;
}
else
{
x_759 = x_927;
x_760 = x_922;
x_761 = x_920;
x_762 = x_925;
x_763 = x_917;
x_764 = x_926;
x_765 = x_923;
x_766 = x_924;
x_767 = x_921;
x_768 = x_53;
goto block_916;
}
}
}
block_961:
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_943 = lean_ctor_get(x_933, 2);
lean_inc(x_943);
x_944 = lean_ctor_get(x_933, 3);
lean_inc(x_944);
lean_inc(x_941);
lean_inc(x_940);
lean_inc(x_939);
lean_inc(x_938);
lean_inc(x_937);
lean_inc(x_944);
x_945 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_944, x_935, x_937, x_938, x_939, x_940, x_941, x_942);
if (lean_obj_tag(x_945) == 0)
{
lean_object* x_946; 
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
if (lean_obj_tag(x_946) == 0)
{
lean_object* x_947; 
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
lean_dec(x_945);
x_917 = x_933;
x_918 = x_943;
x_919 = x_944;
x_920 = x_935;
x_921 = x_936;
x_922 = x_937;
x_923 = x_938;
x_924 = x_939;
x_925 = x_940;
x_926 = x_941;
x_927 = x_947;
goto block_931;
}
else
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
lean_dec(x_944);
lean_dec(x_943);
x_948 = lean_ctor_get(x_945, 1);
lean_inc(x_948);
lean_dec(x_945);
x_949 = lean_ctor_get(x_946, 0);
lean_inc(x_949);
lean_dec(x_946);
x_950 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_936, x_948);
x_951 = lean_ctor_get(x_950, 1);
lean_inc(x_951);
lean_dec(x_950);
x_952 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_933, x_949, x_939, x_951);
x_953 = lean_ctor_get(x_952, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_952, 1);
lean_inc(x_954);
lean_dec(x_952);
x_955 = lean_ctor_get(x_953, 2);
lean_inc(x_955);
x_956 = lean_ctor_get(x_953, 3);
lean_inc(x_956);
x_917 = x_953;
x_918 = x_955;
x_919 = x_956;
x_920 = x_935;
x_921 = x_936;
x_922 = x_937;
x_923 = x_938;
x_924 = x_939;
x_925 = x_940;
x_926 = x_941;
x_927 = x_954;
goto block_931;
}
}
else
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
lean_dec(x_944);
lean_dec(x_943);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_938);
lean_dec(x_937);
lean_dec(x_936);
lean_dec(x_935);
lean_dec(x_933);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_1);
x_957 = lean_ctor_get(x_945, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_945, 1);
lean_inc(x_958);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_959 = x_945;
} else {
 lean_dec_ref(x_945);
 x_959 = lean_box(0);
}
if (lean_is_scalar(x_959)) {
 x_960 = lean_alloc_ctor(1, 2, 0);
} else {
 x_960 = x_959;
}
lean_ctor_set(x_960, 0, x_957);
lean_ctor_set(x_960, 1, x_958);
return x_960;
}
}
block_964:
{
lean_object* x_962; lean_object* x_963; 
x_962 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_934);
x_963 = lean_ctor_get(x_962, 1);
lean_inc(x_963);
lean_dec(x_962);
x_935 = x_2;
x_936 = x_3;
x_937 = x_4;
x_938 = x_5;
x_939 = x_6;
x_940 = x_732;
x_941 = x_8;
x_942 = x_963;
goto block_961;
}
}
case 3:
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; 
x_966 = lean_ctor_get(x_1, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_1, 1);
lean_inc(x_967);
x_968 = lean_st_ref_get(x_3, x_675);
x_969 = lean_ctor_get(x_968, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_968, 1);
lean_inc(x_970);
lean_dec(x_968);
x_971 = lean_ctor_get(x_969, 0);
lean_inc(x_971);
lean_dec(x_969);
lean_inc(x_966);
x_972 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_971, x_966, x_53);
lean_dec(x_971);
if (lean_obj_tag(x_972) == 0)
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; uint8_t x_979; lean_object* x_985; lean_object* x_991; 
x_973 = lean_ctor_get(x_972, 0);
lean_inc(x_973);
lean_dec(x_972);
lean_inc(x_967);
x_974 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_53, x_967, x_3, x_970);
x_975 = lean_ctor_get(x_974, 0);
lean_inc(x_975);
x_976 = lean_ctor_get(x_974, 1);
lean_inc(x_976);
if (lean_is_exclusive(x_974)) {
 lean_ctor_release(x_974, 0);
 lean_ctor_release(x_974, 1);
 x_977 = x_974;
} else {
 lean_dec_ref(x_974);
 x_977 = lean_box(0);
}
lean_inc(x_975);
x_991 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_973, x_975, x_2, x_3, x_4, x_5, x_6, x_732, x_8, x_976);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; 
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
if (lean_obj_tag(x_992) == 0)
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; uint8_t x_998; 
lean_dec(x_732);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
lean_dec(x_991);
lean_inc(x_973);
x_994 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_973, x_3, x_993);
x_995 = lean_ctor_get(x_994, 1);
lean_inc(x_995);
lean_dec(x_994);
x_996 = lean_unsigned_to_nat(0u);
x_997 = lean_array_get_size(x_975);
x_998 = lean_nat_dec_lt(x_996, x_997);
if (x_998 == 0)
{
lean_dec(x_997);
lean_dec(x_3);
x_985 = x_995;
goto block_990;
}
else
{
uint8_t x_999; 
x_999 = lean_nat_dec_le(x_997, x_997);
if (x_999 == 0)
{
lean_dec(x_997);
lean_dec(x_3);
x_985 = x_995;
goto block_990;
}
else
{
lean_object* x_1000; size_t x_1001; size_t x_1002; lean_object* x_1003; lean_object* x_1004; 
x_1000 = lean_box(0);
x_1001 = 0;
x_1002 = lean_usize_of_nat(x_997);
lean_dec(x_997);
x_1003 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(x_975, x_1001, x_1002, x_1000, x_3, x_995);
lean_dec(x_3);
x_1004 = lean_ctor_get(x_1003, 1);
lean_inc(x_1004);
lean_dec(x_1003);
x_985 = x_1004;
goto block_990;
}
}
}
else
{
lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_977);
lean_dec(x_975);
lean_dec(x_973);
lean_dec(x_967);
lean_dec(x_966);
lean_dec(x_1);
x_1005 = lean_ctor_get(x_991, 1);
lean_inc(x_1005);
lean_dec(x_991);
x_1006 = lean_ctor_get(x_992, 0);
lean_inc(x_1006);
lean_dec(x_992);
x_1 = x_1006;
x_7 = x_732;
x_9 = x_1005;
goto _start;
}
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
lean_dec(x_977);
lean_dec(x_975);
lean_dec(x_973);
lean_dec(x_967);
lean_dec(x_966);
lean_dec(x_732);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1008 = lean_ctor_get(x_991, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_991, 1);
lean_inc(x_1009);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_1010 = x_991;
} else {
 lean_dec_ref(x_991);
 x_1010 = lean_box(0);
}
if (lean_is_scalar(x_1010)) {
 x_1011 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1011 = x_1010;
}
lean_ctor_set(x_1011, 0, x_1008);
lean_ctor_set(x_1011, 1, x_1009);
return x_1011;
}
block_984:
{
if (x_979 == 0)
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_980 = x_1;
} else {
 lean_dec_ref(x_1);
 x_980 = lean_box(0);
}
if (lean_is_scalar(x_980)) {
 x_981 = lean_alloc_ctor(3, 2, 0);
} else {
 x_981 = x_980;
}
lean_ctor_set(x_981, 0, x_973);
lean_ctor_set(x_981, 1, x_975);
if (lean_is_scalar(x_977)) {
 x_982 = lean_alloc_ctor(0, 2, 0);
} else {
 x_982 = x_977;
}
lean_ctor_set(x_982, 0, x_981);
lean_ctor_set(x_982, 1, x_978);
return x_982;
}
else
{
lean_object* x_983; 
lean_dec(x_975);
lean_dec(x_973);
if (lean_is_scalar(x_977)) {
 x_983 = lean_alloc_ctor(0, 2, 0);
} else {
 x_983 = x_977;
}
lean_ctor_set(x_983, 0, x_1);
lean_ctor_set(x_983, 1, x_978);
return x_983;
}
}
block_990:
{
uint8_t x_986; 
x_986 = lean_name_eq(x_966, x_973);
lean_dec(x_966);
if (x_986 == 0)
{
lean_dec(x_967);
x_978 = x_985;
x_979 = x_986;
goto block_984;
}
else
{
size_t x_987; size_t x_988; uint8_t x_989; 
x_987 = lean_ptr_addr(x_967);
lean_dec(x_967);
x_988 = lean_ptr_addr(x_975);
x_989 = lean_usize_dec_eq(x_987, x_988);
x_978 = x_985;
x_979 = x_989;
goto block_984;
}
}
}
else
{
lean_object* x_1012; 
lean_dec(x_967);
lean_dec(x_966);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1012 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_732, x_8, x_970);
lean_dec(x_8);
lean_dec(x_732);
lean_dec(x_6);
lean_dec(x_5);
return x_1012;
}
}
case 4:
{
lean_object* x_1013; lean_object* x_1014; 
x_1013 = lean_ctor_get(x_1, 0);
lean_inc(x_1013);
lean_inc(x_8);
lean_inc(x_732);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1013);
x_1014 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1013, x_2, x_3, x_4, x_5, x_6, x_732, x_8, x_675);
if (lean_obj_tag(x_1014) == 0)
{
lean_object* x_1015; 
x_1015 = lean_ctor_get(x_1014, 0);
lean_inc(x_1015);
if (lean_obj_tag(x_1015) == 0)
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1016 = lean_ctor_get(x_1014, 1);
lean_inc(x_1016);
lean_dec(x_1014);
x_1017 = lean_st_ref_get(x_3, x_1016);
x_1018 = lean_ctor_get(x_1017, 0);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_1017, 1);
lean_inc(x_1019);
lean_dec(x_1017);
x_1020 = lean_ctor_get(x_1013, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1013, 1);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1013, 2);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1013, 3);
lean_inc(x_1023);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 lean_ctor_release(x_1013, 1);
 lean_ctor_release(x_1013, 2);
 lean_ctor_release(x_1013, 3);
 x_1024 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1024 = lean_box(0);
}
x_1025 = lean_ctor_get(x_1018, 0);
lean_inc(x_1025);
lean_dec(x_1018);
lean_inc(x_1022);
x_1026 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_1025, x_1022, x_53);
lean_dec(x_1025);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1027 = lean_ctor_get(x_1026, 0);
lean_inc(x_1027);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 x_1028 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1028 = lean_box(0);
}
x_1029 = lean_st_ref_get(x_3, x_1019);
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 lean_ctor_release(x_1029, 1);
 x_1032 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1032 = lean_box(0);
}
x_1033 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_732);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1023);
lean_inc(x_1027);
x_1034 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3(x_1027, x_53, x_1033, x_1023, x_2, x_3, x_4, x_5, x_6, x_732, x_8, x_1031);
if (lean_obj_tag(x_1034) == 0)
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1035 = lean_ctor_get(x_1034, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1034, 1);
lean_inc(x_1036);
if (lean_is_exclusive(x_1034)) {
 lean_ctor_release(x_1034, 0);
 lean_ctor_release(x_1034, 1);
 x_1037 = x_1034;
} else {
 lean_dec_ref(x_1034);
 x_1037 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_3);
x_1038 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1035, x_2, x_3, x_4, x_5, x_6, x_732, x_8, x_1036);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1049; uint8_t x_1050; lean_object* x_1054; lean_object* x_1055; lean_object* x_1065; uint8_t x_1066; 
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1038, 1);
lean_inc(x_1040);
if (lean_is_exclusive(x_1038)) {
 lean_ctor_release(x_1038, 0);
 lean_ctor_release(x_1038, 1);
 x_1041 = x_1038;
} else {
 lean_dec_ref(x_1038);
 x_1041 = lean_box(0);
}
x_1042 = lean_ctor_get(x_1030, 0);
lean_inc(x_1042);
lean_dec(x_1030);
lean_inc(x_1021);
x_1043 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1042, x_53, x_1021);
lean_dec(x_1042);
x_1065 = lean_array_get_size(x_1039);
x_1066 = lean_nat_dec_eq(x_1065, x_730);
lean_dec(x_1065);
if (x_1066 == 0)
{
lean_dec(x_1032);
lean_dec(x_6);
x_1054 = x_3;
x_1055 = x_1040;
goto block_1064;
}
else
{
lean_object* x_1067; 
x_1067 = lean_array_fget(x_1039, x_1033);
if (lean_obj_tag(x_1067) == 0)
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1076; lean_object* x_1077; uint8_t x_1086; lean_object* x_1087; uint8_t x_1089; 
lean_dec(x_1032);
x_1068 = lean_ctor_get(x_1067, 1);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1067, 2);
lean_inc(x_1069);
lean_dec(x_1067);
x_1076 = lean_array_get_size(x_1068);
x_1089 = lean_nat_dec_lt(x_1033, x_1076);
if (x_1089 == 0)
{
x_1086 = x_53;
x_1087 = x_1040;
goto block_1088;
}
else
{
if (x_1089 == 0)
{
x_1086 = x_53;
x_1087 = x_1040;
goto block_1088;
}
else
{
size_t x_1090; size_t x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; uint8_t x_1095; 
x_1090 = 0;
x_1091 = lean_usize_of_nat(x_1076);
x_1092 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_1068, x_1090, x_1091, x_3, x_1040);
x_1093 = lean_ctor_get(x_1092, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1092, 1);
lean_inc(x_1094);
lean_dec(x_1092);
x_1095 = lean_unbox(x_1093);
lean_dec(x_1093);
x_1086 = x_1095;
x_1087 = x_1094;
goto block_1088;
}
}
block_1075:
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1071 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_1070);
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
if (lean_is_scalar(x_1073)) {
 x_1074 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1074 = x_1073;
}
lean_ctor_set(x_1074, 0, x_1069);
lean_ctor_set(x_1074, 1, x_1072);
return x_1074;
}
block_1085:
{
uint8_t x_1078; 
x_1078 = lean_nat_dec_lt(x_1033, x_1076);
if (x_1078 == 0)
{
lean_dec(x_1076);
lean_dec(x_1068);
lean_dec(x_6);
x_1070 = x_1077;
goto block_1075;
}
else
{
uint8_t x_1079; 
x_1079 = lean_nat_dec_le(x_1076, x_1076);
if (x_1079 == 0)
{
lean_dec(x_1076);
lean_dec(x_1068);
lean_dec(x_6);
x_1070 = x_1077;
goto block_1075;
}
else
{
lean_object* x_1080; size_t x_1081; size_t x_1082; lean_object* x_1083; lean_object* x_1084; 
x_1080 = lean_box(0);
x_1081 = 0;
x_1082 = lean_usize_of_nat(x_1076);
lean_dec(x_1076);
x_1083 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1068, x_1081, x_1082, x_1080, x_6, x_1077);
lean_dec(x_6);
lean_dec(x_1068);
x_1084 = lean_ctor_get(x_1083, 1);
lean_inc(x_1084);
lean_dec(x_1083);
x_1070 = x_1084;
goto block_1075;
}
}
}
block_1088:
{
if (x_1086 == 0)
{
lean_dec(x_1043);
lean_dec(x_1041);
lean_dec(x_1039);
lean_dec(x_1037);
lean_dec(x_1028);
lean_dec(x_1027);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec(x_1);
x_1077 = x_1087;
goto block_1085;
}
else
{
if (x_53 == 0)
{
lean_dec(x_1076);
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_6);
x_1054 = x_3;
x_1055 = x_1087;
goto block_1064;
}
else
{
lean_dec(x_1043);
lean_dec(x_1041);
lean_dec(x_1039);
lean_dec(x_1037);
lean_dec(x_1028);
lean_dec(x_1027);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec(x_1);
x_1077 = x_1087;
goto block_1085;
}
}
}
}
else
{
lean_object* x_1096; lean_object* x_1097; 
lean_dec(x_1043);
lean_dec(x_1041);
lean_dec(x_1039);
lean_dec(x_1037);
lean_dec(x_1028);
lean_dec(x_1027);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1096 = lean_ctor_get(x_1067, 0);
lean_inc(x_1096);
lean_dec(x_1067);
if (lean_is_scalar(x_1032)) {
 x_1097 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1097 = x_1032;
}
lean_ctor_set(x_1097, 0, x_1096);
lean_ctor_set(x_1097, 1, x_1040);
return x_1097;
}
}
block_1048:
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
if (lean_is_scalar(x_1024)) {
 x_1045 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1045 = x_1024;
}
lean_ctor_set(x_1045, 0, x_1020);
lean_ctor_set(x_1045, 1, x_1043);
lean_ctor_set(x_1045, 2, x_1027);
lean_ctor_set(x_1045, 3, x_1039);
if (lean_is_scalar(x_1028)) {
 x_1046 = lean_alloc_ctor(4, 1, 0);
} else {
 x_1046 = x_1028;
 lean_ctor_set_tag(x_1046, 4);
}
lean_ctor_set(x_1046, 0, x_1045);
if (lean_is_scalar(x_1041)) {
 x_1047 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1047 = x_1041;
}
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_1044);
return x_1047;
}
block_1053:
{
if (x_1050 == 0)
{
lean_dec(x_1037);
lean_dec(x_1022);
lean_dec(x_1);
x_1044 = x_1049;
goto block_1048;
}
else
{
uint8_t x_1051; 
x_1051 = lean_name_eq(x_1022, x_1027);
lean_dec(x_1022);
if (x_1051 == 0)
{
lean_dec(x_1037);
lean_dec(x_1);
x_1044 = x_1049;
goto block_1048;
}
else
{
lean_object* x_1052; 
lean_dec(x_1043);
lean_dec(x_1041);
lean_dec(x_1039);
lean_dec(x_1028);
lean_dec(x_1027);
lean_dec(x_1024);
lean_dec(x_1020);
if (lean_is_scalar(x_1037)) {
 x_1052 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1052 = x_1037;
}
lean_ctor_set(x_1052, 0, x_1);
lean_ctor_set(x_1052, 1, x_1049);
return x_1052;
}
}
}
block_1064:
{
lean_object* x_1056; lean_object* x_1057; size_t x_1058; size_t x_1059; uint8_t x_1060; 
lean_inc(x_1027);
x_1056 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1027, x_1054, x_1055);
lean_dec(x_1054);
x_1057 = lean_ctor_get(x_1056, 1);
lean_inc(x_1057);
lean_dec(x_1056);
x_1058 = lean_ptr_addr(x_1023);
lean_dec(x_1023);
x_1059 = lean_ptr_addr(x_1039);
x_1060 = lean_usize_dec_eq(x_1058, x_1059);
if (x_1060 == 0)
{
lean_dec(x_1021);
x_1049 = x_1057;
x_1050 = x_1060;
goto block_1053;
}
else
{
size_t x_1061; size_t x_1062; uint8_t x_1063; 
x_1061 = lean_ptr_addr(x_1021);
lean_dec(x_1021);
x_1062 = lean_ptr_addr(x_1043);
x_1063 = lean_usize_dec_eq(x_1061, x_1062);
x_1049 = x_1057;
x_1050 = x_1063;
goto block_1053;
}
}
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
lean_dec(x_1037);
lean_dec(x_1032);
lean_dec(x_1030);
lean_dec(x_1028);
lean_dec(x_1027);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_1098 = lean_ctor_get(x_1038, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1038, 1);
lean_inc(x_1099);
if (lean_is_exclusive(x_1038)) {
 lean_ctor_release(x_1038, 0);
 lean_ctor_release(x_1038, 1);
 x_1100 = x_1038;
} else {
 lean_dec_ref(x_1038);
 x_1100 = lean_box(0);
}
if (lean_is_scalar(x_1100)) {
 x_1101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1101 = x_1100;
}
lean_ctor_set(x_1101, 0, x_1098);
lean_ctor_set(x_1101, 1, x_1099);
return x_1101;
}
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
lean_dec(x_1032);
lean_dec(x_1030);
lean_dec(x_1028);
lean_dec(x_1027);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec(x_732);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1102 = lean_ctor_get(x_1034, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1034, 1);
lean_inc(x_1103);
if (lean_is_exclusive(x_1034)) {
 lean_ctor_release(x_1034, 0);
 lean_ctor_release(x_1034, 1);
 x_1104 = x_1034;
} else {
 lean_dec_ref(x_1034);
 x_1104 = lean_box(0);
}
if (lean_is_scalar(x_1104)) {
 x_1105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1105 = x_1104;
}
lean_ctor_set(x_1105, 0, x_1102);
lean_ctor_set(x_1105, 1, x_1103);
return x_1105;
}
}
else
{
lean_object* x_1106; 
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1106 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_732, x_8, x_1019);
lean_dec(x_8);
lean_dec(x_732);
lean_dec(x_6);
lean_dec(x_5);
return x_1106;
}
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
lean_dec(x_1013);
lean_dec(x_732);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1107 = lean_ctor_get(x_1014, 1);
lean_inc(x_1107);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 lean_ctor_release(x_1014, 1);
 x_1108 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1108 = lean_box(0);
}
x_1109 = lean_ctor_get(x_1015, 0);
lean_inc(x_1109);
lean_dec(x_1015);
if (lean_is_scalar(x_1108)) {
 x_1110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1110 = x_1108;
}
lean_ctor_set(x_1110, 0, x_1109);
lean_ctor_set(x_1110, 1, x_1107);
return x_1110;
}
}
else
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
lean_dec(x_1013);
lean_dec(x_732);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1111 = lean_ctor_get(x_1014, 0);
lean_inc(x_1111);
x_1112 = lean_ctor_get(x_1014, 1);
lean_inc(x_1112);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 lean_ctor_release(x_1014, 1);
 x_1113 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1113 = lean_box(0);
}
if (lean_is_scalar(x_1113)) {
 x_1114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1114 = x_1113;
}
lean_ctor_set(x_1114, 0, x_1111);
lean_ctor_set(x_1114, 1, x_1112);
return x_1114;
}
}
case 5:
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
lean_dec(x_4);
lean_dec(x_2);
x_1115 = lean_ctor_get(x_1, 0);
lean_inc(x_1115);
x_1116 = lean_st_ref_get(x_3, x_675);
x_1117 = lean_ctor_get(x_1116, 0);
lean_inc(x_1117);
x_1118 = lean_ctor_get(x_1116, 1);
lean_inc(x_1118);
lean_dec(x_1116);
x_1119 = lean_ctor_get(x_1117, 0);
lean_inc(x_1119);
lean_dec(x_1117);
lean_inc(x_1115);
x_1120 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_1119, x_1115, x_53);
lean_dec(x_1119);
if (lean_obj_tag(x_1120) == 0)
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; uint8_t x_1125; 
lean_dec(x_732);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_1121 = lean_ctor_get(x_1120, 0);
lean_inc(x_1121);
lean_dec(x_1120);
lean_inc(x_1121);
x_1122 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1121, x_3, x_1118);
lean_dec(x_3);
x_1123 = lean_ctor_get(x_1122, 1);
lean_inc(x_1123);
if (lean_is_exclusive(x_1122)) {
 lean_ctor_release(x_1122, 0);
 lean_ctor_release(x_1122, 1);
 x_1124 = x_1122;
} else {
 lean_dec_ref(x_1122);
 x_1124 = lean_box(0);
}
x_1125 = lean_name_eq(x_1115, x_1121);
lean_dec(x_1115);
if (x_1125 == 0)
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1126 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1126 = lean_box(0);
}
if (lean_is_scalar(x_1126)) {
 x_1127 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1127 = x_1126;
}
lean_ctor_set(x_1127, 0, x_1121);
if (lean_is_scalar(x_1124)) {
 x_1128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1128 = x_1124;
}
lean_ctor_set(x_1128, 0, x_1127);
lean_ctor_set(x_1128, 1, x_1123);
return x_1128;
}
else
{
lean_object* x_1129; 
lean_dec(x_1121);
if (lean_is_scalar(x_1124)) {
 x_1129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1129 = x_1124;
}
lean_ctor_set(x_1129, 0, x_1);
lean_ctor_set(x_1129, 1, x_1123);
return x_1129;
}
}
else
{
lean_object* x_1130; 
lean_dec(x_1115);
lean_dec(x_3);
lean_dec(x_1);
x_1130 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_732, x_8, x_1118);
lean_dec(x_8);
lean_dec(x_732);
lean_dec(x_6);
lean_dec(x_5);
return x_1130;
}
}
case 6:
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; size_t x_1138; size_t x_1139; uint8_t x_1140; 
lean_dec(x_732);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1131 = lean_ctor_get(x_1, 0);
lean_inc(x_1131);
x_1132 = lean_st_ref_get(x_3, x_675);
lean_dec(x_3);
x_1133 = lean_ctor_get(x_1132, 0);
lean_inc(x_1133);
x_1134 = lean_ctor_get(x_1132, 1);
lean_inc(x_1134);
if (lean_is_exclusive(x_1132)) {
 lean_ctor_release(x_1132, 0);
 lean_ctor_release(x_1132, 1);
 x_1135 = x_1132;
} else {
 lean_dec_ref(x_1132);
 x_1135 = lean_box(0);
}
x_1136 = lean_ctor_get(x_1133, 0);
lean_inc(x_1136);
lean_dec(x_1133);
lean_inc(x_1131);
x_1137 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1136, x_53, x_1131);
lean_dec(x_1136);
x_1138 = lean_ptr_addr(x_1131);
lean_dec(x_1131);
x_1139 = lean_ptr_addr(x_1137);
x_1140 = lean_usize_dec_eq(x_1138, x_1139);
if (x_1140 == 0)
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1141 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1141 = lean_box(0);
}
if (lean_is_scalar(x_1141)) {
 x_1142 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1142 = x_1141;
}
lean_ctor_set(x_1142, 0, x_1137);
if (lean_is_scalar(x_1135)) {
 x_1143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1143 = x_1135;
}
lean_ctor_set(x_1143, 0, x_1142);
lean_ctor_set(x_1143, 1, x_1134);
return x_1143;
}
else
{
lean_object* x_1144; 
lean_dec(x_1137);
if (lean_is_scalar(x_1135)) {
 x_1144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1144 = x_1135;
}
lean_ctor_set(x_1144, 0, x_1);
lean_ctor_set(x_1144, 1, x_1134);
return x_1144;
}
}
default: 
{
lean_object* x_1145; lean_object* x_1146; 
x_1145 = lean_ctor_get(x_1, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1, 1);
lean_inc(x_1146);
x_676 = x_1145;
x_677 = x_1146;
x_678 = x_2;
x_679 = x_3;
x_680 = x_4;
x_681 = x_5;
x_682 = x_6;
x_683 = x_732;
x_684 = x_8;
goto block_729;
}
}
block_729:
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; uint8_t x_692; 
x_685 = lean_ctor_get(x_676, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_676, 2);
lean_inc(x_686);
x_687 = lean_ctor_get(x_676, 3);
lean_inc(x_687);
x_688 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_685, x_679, x_675);
lean_dec(x_685);
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec(x_688);
lean_inc(x_689);
lean_inc(x_1);
lean_inc(x_677);
x_691 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_691, 0, x_677);
lean_closure_set(x_691, 1, x_1);
lean_closure_set(x_691, 2, x_689);
x_692 = lean_unbox(x_689);
if (x_692 == 0)
{
uint8_t x_693; 
lean_dec(x_689);
lean_dec(x_677);
x_693 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_693 == 0)
{
lean_dec(x_687);
lean_dec(x_686);
x_10 = x_691;
x_11 = x_676;
x_12 = x_678;
x_13 = x_679;
x_14 = x_680;
x_15 = x_681;
x_16 = x_682;
x_17 = x_683;
x_18 = x_684;
x_19 = x_690;
goto block_29;
}
else
{
uint8_t x_694; 
x_694 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_687, x_686);
lean_dec(x_686);
if (x_694 == 0)
{
x_10 = x_691;
x_11 = x_676;
x_12 = x_678;
x_13 = x_679;
x_14 = x_680;
x_15 = x_681;
x_16 = x_682;
x_17 = x_683;
x_18 = x_684;
x_19 = x_690;
goto block_29;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_695 = lean_st_ref_get(x_679, x_690);
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
x_698 = lean_ctor_get(x_696, 0);
lean_inc(x_698);
lean_dec(x_696);
lean_inc(x_684);
lean_inc(x_683);
lean_inc(x_682);
lean_inc(x_681);
x_699 = l_Lean_Compiler_LCNF_normFunDeclImp(x_53, x_676, x_698, x_681, x_682, x_683, x_684, x_697);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
lean_inc(x_684);
lean_inc(x_683);
lean_inc(x_682);
lean_inc(x_681);
x_702 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_700, x_681, x_682, x_683, x_684, x_701);
if (lean_obj_tag(x_702) == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_702, 1);
lean_inc(x_704);
lean_dec(x_702);
x_705 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_679, x_704);
x_706 = lean_ctor_get(x_705, 1);
lean_inc(x_706);
lean_dec(x_705);
x_10 = x_691;
x_11 = x_703;
x_12 = x_678;
x_13 = x_679;
x_14 = x_680;
x_15 = x_681;
x_16 = x_682;
x_17 = x_683;
x_18 = x_684;
x_19 = x_706;
goto block_29;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; 
lean_dec(x_691);
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
lean_dec(x_681);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_678);
x_707 = lean_ctor_get(x_702, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_702, 1);
lean_inc(x_708);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_709 = x_702;
} else {
 lean_dec_ref(x_702);
 x_709 = lean_box(0);
}
if (lean_is_scalar(x_709)) {
 x_710 = lean_alloc_ctor(1, 2, 0);
} else {
 x_710 = x_709;
}
lean_ctor_set(x_710, 0, x_707);
lean_ctor_set(x_710, 1, x_708);
return x_710;
}
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
lean_dec(x_691);
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
lean_dec(x_681);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_678);
x_711 = lean_ctor_get(x_699, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_699, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_713 = x_699;
} else {
 lean_dec_ref(x_699);
 x_713 = lean_box(0);
}
if (lean_is_scalar(x_713)) {
 x_714 = lean_alloc_ctor(1, 2, 0);
} else {
 x_714 = x_713;
}
lean_ctor_set(x_714, 0, x_711);
lean_ctor_set(x_714, 1, x_712);
return x_714;
}
}
}
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec(x_691);
lean_dec(x_687);
lean_dec(x_686);
x_715 = lean_st_ref_get(x_679, x_690);
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec(x_715);
x_718 = lean_ctor_get(x_716, 0);
lean_inc(x_718);
lean_dec(x_716);
lean_inc(x_684);
lean_inc(x_683);
lean_inc(x_682);
lean_inc(x_681);
x_719 = l_Lean_Compiler_LCNF_normFunDeclImp(x_53, x_676, x_718, x_681, x_682, x_683, x_684, x_717);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; uint8_t x_723; lean_object* x_724; 
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_722 = lean_box(0);
x_723 = lean_unbox(x_689);
lean_dec(x_689);
x_724 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_677, x_1, x_723, x_720, x_722, x_678, x_679, x_680, x_681, x_682, x_683, x_684, x_721);
return x_724;
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
lean_dec(x_689);
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
lean_dec(x_681);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_677);
lean_dec(x_1);
x_725 = lean_ctor_get(x_719, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_719, 1);
lean_inc(x_726);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_727 = x_719;
} else {
 lean_dec_ref(x_719);
 x_727 = lean_box(0);
}
if (lean_is_scalar(x_727)) {
 x_728 = lean_alloc_ctor(1, 2, 0);
} else {
 x_728 = x_727;
}
lean_ctor_set(x_728, 0, x_725);
lean_ctor_set(x_728, 1, x_726);
return x_728;
}
}
}
}
}
else
{
lean_object* x_1147; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_48);
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
lean_dec(x_1);
x_1147 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1147;
}
block_29:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_20 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_apply_10(x_10, x_21, x_23, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
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
block_37:
{
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_30);
return x_36;
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
lean_inc(x_9);
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
lean_dec(x_9);
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
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 3);
lean_inc(x_24);
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
lean_dec(x_33);
x_35 = lean_array_fget(x_9, x_10);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_10, x_36);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_37);
x_46 = lean_array_get_size(x_32);
x_47 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_34);
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
x_60 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_34, x_59);
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
x_70 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_63);
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
x_73 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_34, x_35, x_59);
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
lean_dec(x_40);
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
lean_dec(x_77);
x_79 = lean_array_fget(x_9, x_10);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_10, x_80);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_81);
x_90 = lean_array_get_size(x_76);
x_91 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_78);
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
x_104 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_78, x_103);
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
x_114 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_107);
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
x_119 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_78, x_79, x_103);
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
lean_dec(x_84);
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
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 3);
lean_inc(x_128);
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
lean_inc(x_135);
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
lean_dec(x_137);
x_139 = lean_array_fget(x_9, x_10);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_add(x_10, x_140);
lean_dec(x_10);
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_9);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_11);
x_151 = lean_array_get_size(x_135);
x_152 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_138);
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
x_165 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_138, x_164);
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
x_175 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_168);
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
x_180 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_138, x_139, x_164);
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
lean_dec(x_145);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_14, x_13, x_16);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_19, x_4, x_6, x_8, x_12);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_free_object(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_30);
x_32 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set_tag(x_17, 4);
lean_ctor_set(x_17, 0, x_34);
x_35 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_17, x_6, x_28);
lean_dec(x_17);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_36);
if (lean_obj_tag(x_33) == 0)
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_33, 2);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_ctor_get(x_38, 3);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_array_get_size(x_42);
x_45 = l_Array_toSubarray___redArg(x_42, x_43, x_44);
x_46 = lean_array_size(x_40);
x_47 = 0;
x_48 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_40, x_46, x_47, x_45, x_3, x_39);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_6);
x_50 = l_Lean_Compiler_LCNF_Simp_simp(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_40, x_6, x_52);
lean_dec(x_6);
lean_dec(x_40);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_21, 0, x_51);
lean_ctor_set(x_53, 0, x_21);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
lean_ctor_set(x_21, 0, x_51);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_40);
lean_free_object(x_21);
lean_dec(x_6);
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_37);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_37, 1);
x_64 = lean_ctor_get(x_37, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_33, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_33, 2);
lean_inc(x_66);
lean_dec(x_33);
x_67 = !lean_is_exclusive(x_30);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_30, 0);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_eq(x_68, x_69);
if (x_70 == 1)
{
lean_object* x_71; 
lean_free_object(x_30);
lean_dec(x_68);
lean_dec(x_65);
lean_free_object(x_37);
x_71 = l_Lean_Compiler_LCNF_Simp_simp(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_ctor_set(x_21, 0, x_73);
lean_ctor_set(x_71, 0, x_21);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_71, 0);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_71);
lean_ctor_set(x_21, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_21);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_free_object(x_21);
x_77 = !lean_is_exclusive(x_71);
if (x_77 == 0)
{
return x_71;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_71, 0);
x_79 = lean_ctor_get(x_71, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_71);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_sub(x_68, x_81);
lean_dec(x_68);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_82);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_30);
x_84 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_85 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_83, x_84, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_89 = lean_array_get(x_88, x_65, x_69);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_ctor_get(x_86, 0);
lean_inc(x_91);
x_92 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_90, x_91, x_3, x_6, x_7, x_8, x_87);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_inc(x_6);
x_94 = l_Lean_Compiler_LCNF_Simp_simp(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_65, x_6, x_96);
lean_dec(x_6);
lean_dec(x_65);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_97, 0);
lean_dec(x_99);
lean_ctor_set(x_37, 1, x_95);
lean_ctor_set(x_37, 0, x_86);
lean_ctor_set(x_21, 0, x_37);
lean_ctor_set(x_97, 0, x_21);
return x_97;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
lean_ctor_set(x_37, 1, x_95);
lean_ctor_set(x_37, 0, x_86);
lean_ctor_set(x_21, 0, x_37);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_21);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_86);
lean_dec(x_65);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_6);
x_102 = !lean_is_exclusive(x_94);
if (x_102 == 0)
{
return x_94;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_94, 0);
x_104 = lean_ctor_get(x_94, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_94);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_86);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_92);
if (x_106 == 0)
{
return x_92;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_92, 0);
x_108 = lean_ctor_get(x_92, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_92);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_85);
if (x_110 == 0)
{
return x_85;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_85, 0);
x_112 = lean_ctor_get(x_85, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_85);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_30, 0);
lean_inc(x_114);
lean_dec(x_30);
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_nat_dec_eq(x_114, x_115);
if (x_116 == 1)
{
lean_object* x_117; 
lean_dec(x_114);
lean_dec(x_65);
lean_free_object(x_37);
x_117 = l_Lean_Compiler_LCNF_Simp_simp(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
lean_ctor_set(x_21, 0, x_118);
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_21);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_free_object(x_21);
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_124 = x_117;
} else {
 lean_dec_ref(x_117);
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
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_sub(x_114, x_126);
lean_dec(x_114);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_131 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_129, x_130, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_135 = lean_array_get(x_134, x_65, x_115);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_ctor_get(x_132, 0);
lean_inc(x_137);
x_138 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_136, x_137, x_3, x_6, x_7, x_8, x_133);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
lean_inc(x_6);
x_140 = l_Lean_Compiler_LCNF_Simp_simp(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_65, x_6, x_142);
lean_dec(x_6);
lean_dec(x_65);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
lean_ctor_set(x_37, 1, x_141);
lean_ctor_set(x_37, 0, x_132);
lean_ctor_set(x_21, 0, x_37);
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_21);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_132);
lean_dec(x_65);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_6);
x_147 = lean_ctor_get(x_140, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_140, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_149 = x_140;
} else {
 lean_dec_ref(x_140);
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
lean_dec(x_132);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_151 = lean_ctor_get(x_138, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_138, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_153 = x_138;
} else {
 lean_dec_ref(x_138);
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
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = lean_ctor_get(x_131, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_131, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_157 = x_131;
} else {
 lean_dec_ref(x_131);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_159 = lean_ctor_get(x_37, 1);
lean_inc(x_159);
lean_dec(x_37);
x_160 = lean_ctor_get(x_33, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_33, 2);
lean_inc(x_161);
lean_dec(x_33);
x_162 = lean_ctor_get(x_30, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_163 = x_30;
} else {
 lean_dec_ref(x_30);
 x_163 = lean_box(0);
}
x_164 = lean_unsigned_to_nat(0u);
x_165 = lean_nat_dec_eq(x_162, x_164);
if (x_165 == 1)
{
lean_object* x_166; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_160);
x_166 = l_Lean_Compiler_LCNF_Simp_simp(x_161, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_159);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
lean_ctor_set(x_21, 0, x_167);
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_21);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_free_object(x_21);
x_171 = lean_ctor_get(x_166, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_166, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_173 = x_166;
} else {
 lean_dec_ref(x_166);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_sub(x_162, x_175);
lean_dec(x_162);
if (lean_is_scalar(x_163)) {
 x_177 = lean_alloc_ctor(0, 1, 0);
} else {
 x_177 = x_163;
 lean_ctor_set_tag(x_177, 0);
}
lean_ctor_set(x_177, 0, x_176);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_180 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_178, x_179, x_5, x_6, x_7, x_8, x_159);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_184 = lean_array_get(x_183, x_160, x_164);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_ctor_get(x_181, 0);
lean_inc(x_186);
x_187 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_185, x_186, x_3, x_6, x_7, x_8, x_182);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
lean_inc(x_6);
x_189 = l_Lean_Compiler_LCNF_Simp_simp(x_161, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_160, x_6, x_191);
lean_dec(x_6);
lean_dec(x_160);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_181);
lean_ctor_set(x_195, 1, x_190);
lean_ctor_set(x_21, 0, x_195);
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_21);
lean_ctor_set(x_196, 1, x_193);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_181);
lean_dec(x_160);
lean_free_object(x_21);
lean_dec(x_6);
x_197 = lean_ctor_get(x_189, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_189, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_199 = x_189;
} else {
 lean_dec_ref(x_189);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_181);
lean_dec(x_161);
lean_dec(x_160);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_201 = lean_ctor_get(x_187, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_187, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_203 = x_187;
} else {
 lean_dec_ref(x_187);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_161);
lean_dec(x_160);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_205 = lean_ctor_get(x_180, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_180, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_207 = x_180;
} else {
 lean_dec_ref(x_180);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_30);
x_209 = lean_ctor_get(x_37, 1);
lean_inc(x_209);
lean_dec(x_37);
x_210 = lean_ctor_get(x_33, 0);
lean_inc(x_210);
lean_dec(x_33);
x_211 = l_Lean_Compiler_LCNF_Simp_simp(x_210, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_209);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_211, 0);
lean_ctor_set(x_21, 0, x_213);
lean_ctor_set(x_211, 0, x_21);
return x_211;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_211, 0);
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_211);
lean_ctor_set(x_21, 0, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_21);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
else
{
uint8_t x_217; 
lean_free_object(x_21);
x_217 = !lean_is_exclusive(x_211);
if (x_217 == 0)
{
return x_211;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_211, 0);
x_219 = lean_ctor_get(x_211, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_211);
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
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_221 = lean_ctor_get(x_21, 0);
lean_inc(x_221);
lean_dec(x_21);
x_222 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_221);
x_223 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_222);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
lean_ctor_set_tag(x_17, 4);
lean_ctor_set(x_17, 0, x_225);
x_226 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_17, x_6, x_28);
lean_dec(x_17);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_228 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_227);
if (lean_obj_tag(x_224) == 0)
{
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; size_t x_237; size_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_229 = lean_ctor_get(x_221, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_ctor_get(x_224, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_224, 2);
lean_inc(x_232);
lean_dec(x_224);
x_233 = lean_ctor_get(x_221, 1);
lean_inc(x_233);
lean_dec(x_221);
x_234 = lean_ctor_get(x_229, 3);
lean_inc(x_234);
lean_dec(x_229);
x_235 = lean_array_get_size(x_233);
x_236 = l_Array_toSubarray___redArg(x_233, x_234, x_235);
x_237 = lean_array_size(x_231);
x_238 = 0;
x_239 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_231, x_237, x_238, x_236, x_3, x_230);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
lean_inc(x_6);
x_241 = l_Lean_Compiler_LCNF_Simp_simp(x_232, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_231, x_6, x_243);
lean_dec(x_6);
lean_dec(x_231);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_246 = x_244;
} else {
 lean_dec_ref(x_244);
 x_246 = lean_box(0);
}
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_242);
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_246;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_245);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_231);
lean_dec(x_6);
x_249 = lean_ctor_get(x_241, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_241, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_251 = x_241;
} else {
 lean_dec_ref(x_241);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_253 = lean_ctor_get(x_228, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_254 = x_228;
} else {
 lean_dec_ref(x_228);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_224, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_224, 2);
lean_inc(x_256);
lean_dec(x_224);
x_257 = lean_ctor_get(x_221, 0);
lean_inc(x_257);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_258 = x_221;
} else {
 lean_dec_ref(x_221);
 x_258 = lean_box(0);
}
x_259 = lean_unsigned_to_nat(0u);
x_260 = lean_nat_dec_eq(x_257, x_259);
if (x_260 == 1)
{
lean_object* x_261; 
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_254);
x_261 = l_Lean_Compiler_LCNF_Simp_simp(x_256, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_253);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
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
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_262);
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_263);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_261, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_261, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_269 = x_261;
} else {
 lean_dec_ref(x_261);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_271 = lean_unsigned_to_nat(1u);
x_272 = lean_nat_sub(x_257, x_271);
lean_dec(x_257);
if (lean_is_scalar(x_258)) {
 x_273 = lean_alloc_ctor(0, 1, 0);
} else {
 x_273 = x_258;
 lean_ctor_set_tag(x_273, 0);
}
lean_ctor_set(x_273, 0, x_272);
x_274 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_276 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_274, x_275, x_5, x_6, x_7, x_8, x_253);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_280 = lean_array_get(x_279, x_255, x_259);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec(x_280);
x_282 = lean_ctor_get(x_277, 0);
lean_inc(x_282);
x_283 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_281, x_282, x_3, x_6, x_7, x_8, x_278);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec(x_283);
lean_inc(x_6);
x_285 = l_Lean_Compiler_LCNF_Simp_simp(x_256, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_255, x_6, x_287);
lean_dec(x_6);
lean_dec(x_255);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_290 = x_288;
} else {
 lean_dec_ref(x_288);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_254;
}
lean_ctor_set(x_291, 0, x_277);
lean_ctor_set(x_291, 1, x_286);
x_292 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_292, 0, x_291);
if (lean_is_scalar(x_290)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_290;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_289);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_277);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_6);
x_294 = lean_ctor_get(x_285, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_285, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_296 = x_285;
} else {
 lean_dec_ref(x_285);
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
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_277);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_298 = lean_ctor_get(x_283, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_283, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_300 = x_283;
} else {
 lean_dec_ref(x_283);
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
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_302 = lean_ctor_get(x_276, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_276, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_304 = x_276;
} else {
 lean_dec_ref(x_276);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
return x_305;
}
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_221);
x_306 = lean_ctor_get(x_228, 1);
lean_inc(x_306);
lean_dec(x_228);
x_307 = lean_ctor_get(x_224, 0);
lean_inc(x_307);
lean_dec(x_224);
x_308 = l_Lean_Compiler_LCNF_Simp_simp(x_307, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_306);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_311 = x_308;
} else {
 lean_dec_ref(x_308);
 x_311 = lean_box(0);
}
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_309);
if (lean_is_scalar(x_311)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_311;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_310);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_314 = lean_ctor_get(x_308, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_308, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_316 = x_308;
} else {
 lean_dec_ref(x_308);
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
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_17, 0);
lean_inc(x_318);
lean_dec(x_17);
x_319 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_318, x_4, x_6, x_8, x_12);
lean_dec(x_318);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_322 = x_319;
} else {
 lean_dec_ref(x_319);
 x_322 = lean_box(0);
}
x_323 = lean_box(0);
if (lean_is_scalar(x_322)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_322;
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_321);
return x_324;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_325 = lean_ctor_get(x_319, 1);
lean_inc(x_325);
lean_dec(x_319);
x_326 = lean_ctor_get(x_320, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_327 = x_320;
} else {
 lean_dec_ref(x_320);
 x_327 = lean_box(0);
}
x_328 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_326);
x_329 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_1, x_328);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_332 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_332, 0, x_331);
x_333 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_332, x_6, x_325);
lean_dec(x_332);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
lean_dec(x_333);
x_335 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_334);
if (lean_obj_tag(x_330) == 0)
{
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; size_t x_344; size_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_336 = lean_ctor_get(x_326, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = lean_ctor_get(x_330, 1);
lean_inc(x_338);
x_339 = lean_ctor_get(x_330, 2);
lean_inc(x_339);
lean_dec(x_330);
x_340 = lean_ctor_get(x_326, 1);
lean_inc(x_340);
lean_dec(x_326);
x_341 = lean_ctor_get(x_336, 3);
lean_inc(x_341);
lean_dec(x_336);
x_342 = lean_array_get_size(x_340);
x_343 = l_Array_toSubarray___redArg(x_340, x_341, x_342);
x_344 = lean_array_size(x_338);
x_345 = 0;
x_346 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_338, x_344, x_345, x_343, x_3, x_337);
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
lean_dec(x_346);
lean_inc(x_6);
x_348 = l_Lean_Compiler_LCNF_Simp_simp(x_339, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_347);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_338, x_6, x_350);
lean_dec(x_6);
lean_dec(x_338);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_353 = x_351;
} else {
 lean_dec_ref(x_351);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_354 = lean_alloc_ctor(1, 1, 0);
} else {
 x_354 = x_327;
}
lean_ctor_set(x_354, 0, x_349);
if (lean_is_scalar(x_353)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_353;
}
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_352);
return x_355;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_338);
lean_dec(x_327);
lean_dec(x_6);
x_356 = lean_ctor_get(x_348, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_348, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_358 = x_348;
} else {
 lean_dec_ref(x_348);
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
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; 
x_360 = lean_ctor_get(x_335, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_361 = x_335;
} else {
 lean_dec_ref(x_335);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_330, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_330, 2);
lean_inc(x_363);
lean_dec(x_330);
x_364 = lean_ctor_get(x_326, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_365 = x_326;
} else {
 lean_dec_ref(x_326);
 x_365 = lean_box(0);
}
x_366 = lean_unsigned_to_nat(0u);
x_367 = lean_nat_dec_eq(x_364, x_366);
if (x_367 == 1)
{
lean_object* x_368; 
lean_dec(x_365);
lean_dec(x_364);
lean_dec(x_362);
lean_dec(x_361);
x_368 = l_Lean_Compiler_LCNF_Simp_simp(x_363, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_360);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_371 = x_368;
} else {
 lean_dec_ref(x_368);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_372 = lean_alloc_ctor(1, 1, 0);
} else {
 x_372 = x_327;
}
lean_ctor_set(x_372, 0, x_369);
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_370);
return x_373;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_327);
x_374 = lean_ctor_get(x_368, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_368, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_376 = x_368;
} else {
 lean_dec_ref(x_368);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(1, 2, 0);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_374);
lean_ctor_set(x_377, 1, x_375);
return x_377;
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_378 = lean_unsigned_to_nat(1u);
x_379 = lean_nat_sub(x_364, x_378);
lean_dec(x_364);
if (lean_is_scalar(x_365)) {
 x_380 = lean_alloc_ctor(0, 1, 0);
} else {
 x_380 = x_365;
 lean_ctor_set_tag(x_380, 0);
}
lean_ctor_set(x_380, 0, x_379);
x_381 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_381, 0, x_380);
x_382 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___redArg___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_383 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_381, x_382, x_5, x_6, x_7, x_8, x_360);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_387 = lean_array_get(x_386, x_362, x_366);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
lean_dec(x_387);
x_389 = lean_ctor_get(x_384, 0);
lean_inc(x_389);
x_390 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_388, x_389, x_3, x_6, x_7, x_8, x_385);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
lean_inc(x_6);
x_392 = l_Lean_Compiler_LCNF_Simp_simp(x_363, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_391);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_395 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_362, x_6, x_394);
lean_dec(x_6);
lean_dec(x_362);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_397 = x_395;
} else {
 lean_dec_ref(x_395);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_361;
}
lean_ctor_set(x_398, 0, x_384);
lean_ctor_set(x_398, 1, x_393);
if (lean_is_scalar(x_327)) {
 x_399 = lean_alloc_ctor(1, 1, 0);
} else {
 x_399 = x_327;
}
lean_ctor_set(x_399, 0, x_398);
if (lean_is_scalar(x_397)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_397;
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_396);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_384);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_327);
lean_dec(x_6);
x_401 = lean_ctor_get(x_392, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_392, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_403 = x_392;
} else {
 lean_dec_ref(x_392);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_401);
lean_ctor_set(x_404, 1, x_402);
return x_404;
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_384);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_327);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_405 = lean_ctor_get(x_390, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_390, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_407 = x_390;
} else {
 lean_dec_ref(x_390);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_406);
return x_408;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_327);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_409 = lean_ctor_get(x_383, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_383, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_411 = x_383;
} else {
 lean_dec_ref(x_383);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 2, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_410);
return x_412;
}
}
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_326);
x_413 = lean_ctor_get(x_335, 1);
lean_inc(x_413);
lean_dec(x_335);
x_414 = lean_ctor_get(x_330, 0);
lean_inc(x_414);
lean_dec(x_330);
x_415 = l_Lean_Compiler_LCNF_Simp_simp(x_414, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_413);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_418 = x_415;
} else {
 lean_dec_ref(x_415);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_419 = lean_alloc_ctor(1, 1, 0);
} else {
 x_419 = x_327;
}
lean_ctor_set(x_419, 0, x_416);
if (lean_is_scalar(x_418)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_418;
}
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_417);
return x_420;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_327);
x_421 = lean_ctor_get(x_415, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_415, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_423 = x_415;
} else {
 lean_dec_ref(x_415);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 2, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_421);
lean_ctor_set(x_424, 1, x_422);
return x_424;
}
}
}
}
}
else
{
lean_object* x_425; uint8_t x_426; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_425 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_426 = !lean_is_exclusive(x_425);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_425, 0);
x_428 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_425, 0, x_428);
return x_425;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_429 = lean_ctor_get(x_425, 0);
x_430 = lean_ctor_get(x_425, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_425);
x_431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_431, 0, x_429);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_430);
return x_432;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; uint8_t x_22; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
x_12 = lean_st_ref_get(x_4, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_15, x_1, x_11);
lean_dec(x_15);
lean_inc(x_10);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(x_10, x_16, x_5, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ptr_addr(x_10);
lean_dec(x_10);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_17, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_Simp_simp(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_unbox(x_16);
x_26 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_24, x_25, x_14);
lean_dec(x_24);
x_27 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_26, x_19, x_22, x_6, x_23);
lean_dec(x_6);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
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
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3_spec__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_simp_spec__5(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__6(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_15;
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
lean_dec(x_1);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
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
lean_dec(x_1);
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__0);
l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__1);
l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__2);
l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___lam__0___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
