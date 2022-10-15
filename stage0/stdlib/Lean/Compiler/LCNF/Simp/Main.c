// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Main
// Imports: Init Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.ElimDead Lean.Compiler.LCNF.AlphaEqv Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.Simp.FunDeclInfo Lean.Compiler.LCNF.Simp.InlineCandidate Lean.Compiler.LCNF.Simp.InlineProj Lean.Compiler.LCNF.Simp.Used Lean.Compiler.LCNF.Simp.DefaultAlt Lean.Compiler.LCNF.Simp.SimpValue Lean.Compiler.LCNF.Simp.ConstantFold
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
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCode;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_hasLocalInst(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_2 = l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg(x_1);
return x_2;
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
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_7);
x_11 = 0;
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_8);
lean_dec(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_14 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_15 = l___private_Init_Util_0__outOfBounds___rarg(x_14);
x_16 = l_Lean_Compiler_LCNF_AltCore_getCode(x_15);
lean_dec(x_15);
x_1 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_7, x_12);
lean_dec(x_7);
x_19 = l_Lean_Compiler_LCNF_AltCore_getCode(x_18);
lean_dec(x_18);
x_1 = x_19;
goto _start;
}
}
}
case 5:
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = 1;
return x_21;
}
default: 
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = 0;
return x_22;
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_array_uget(x_15, x_3);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
x_20 = 1;
lean_inc(x_18);
x_21 = l_Lean_Compiler_LCNF_replaceExprFVars(x_19, x_18, x_20, x_8, x_9, x_10, x_11, x_12);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
x_25 = l_Lean_Compiler_LCNF_mkAuxParam(x_22, x_24, x_8, x_9, x_10, x_11, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = lean_array_push(x_17, x_26);
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_Expr_fvar___override(x_30);
x_32 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_18, x_29, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_3 = x_35;
x_4 = x_33;
x_12 = x_27;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
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
x_1 = lean_mk_string_from_bytes("_f", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
x_13 = l_Array_toSubarray___rarg(x_10, x_12, x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_get_size(x_14);
x_18 = lean_usize_of_nat(x_17);
x_19 = 0;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(x_14, x_18, x_19, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_toSubarray___rarg(x_14, x_11, x_17);
x_26 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
lean_ctor_set(x_21, 0, x_26);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_25, x_28, x_30, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_Compiler_LCNF_Code_internalize(x_36, x_35, x_5, x_6, x_7, x_8, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_38);
x_41 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_38, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_44 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_34, x_38, x_43, x_5, x_6, x_7, x_8, x_42);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; lean_object* x_55; size_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_dec(x_21);
x_50 = l_Array_toSubarray___rarg(x_14, x_11, x_17);
x_51 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
x_53 = lean_ctor_get(x_50, 2);
lean_inc(x_53);
x_54 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
x_56 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_57 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_50, x_54, x_56, x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_50);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_dec(x_1);
x_63 = l_Lean_Compiler_LCNF_Code_internalize(x_62, x_61, x_5, x_6, x_7, x_8, x_59);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_64);
x_67 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_64, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_70 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_60, x_64, x_69, x_5, x_6, x_7, x_8, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
lean_dec(x_1);
x_16 = 0;
x_17 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_14, x_15, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_inc(x_20);
x_21 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_box(0);
x_32 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(x_20, x_2, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_x", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get_uint8(x_10, 0);
if (x_11 == 0)
{
lean_object* x_170; 
x_170 = lean_box(0);
x_12 = x_170;
x_13 = x_9;
goto block_169;
}
else
{
lean_object* x_171; 
x_171 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_12 = x_171;
x_13 = x_9;
goto block_169;
}
block_169:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = l_Lean_Expr_getAppFn(x_16);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_8, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_18);
x_24 = lean_environment_find(x_23, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = lean_box(0);
if (lean_is_scalar(x_22)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_22;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_ConstantInfo_type(x_27);
lean_dec(x_27);
x_29 = l_Lean_Compiler_LCNF_hasLocalInst(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_165; 
x_165 = 0;
x_30 = x_165;
goto block_164;
}
else
{
uint8_t x_166; 
x_166 = 1;
x_30 = x_166;
goto block_164;
}
block_164:
{
lean_object* x_31; lean_object* x_32; 
if (x_30 == 0)
{
lean_object* x_162; 
x_162 = lean_box(0);
x_31 = x_162;
x_32 = x_21;
goto block_161;
}
else
{
lean_object* x_163; 
x_163 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_31 = x_163;
x_32 = x_21;
goto block_161;
}
block_161:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = lean_box(0);
if (lean_is_scalar(x_22)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_22;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_158; 
lean_dec(x_31);
lean_dec(x_22);
lean_inc(x_18);
x_35 = l_Lean_Meta_isInstance(x_18, x_7, x_8, x_32);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_158 = lean_unbox(x_36);
lean_dec(x_36);
if (x_158 == 0)
{
uint8_t x_159; 
x_159 = 1;
x_39 = x_159;
goto block_157;
}
else
{
uint8_t x_160; 
x_160 = 0;
x_39 = x_160;
goto block_157;
}
block_157:
{
uint8_t x_40; 
if (x_39 == 0)
{
uint8_t x_155; 
x_155 = 0;
x_40 = x_155;
goto block_154;
}
else
{
uint8_t x_156; 
x_156 = 1;
x_40 = x_156;
goto block_154;
}
block_154:
{
lean_object* x_41; lean_object* x_42; 
if (x_40 == 0)
{
lean_object* x_152; 
x_152 = lean_box(0);
x_41 = x_152;
x_42 = x_37;
goto block_151;
}
else
{
lean_object* x_153; 
x_153 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_41 = x_153;
x_42 = x_37;
goto block_151;
}
block_151:
{
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_43 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_38;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
lean_dec(x_38);
x_45 = l_Lean_Compiler_LCNF_getDecl_x3f(x_18, x_5, x_6, x_7, x_8, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_54 = x_45;
} else {
 lean_dec_ref(x_45);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_46, 0);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_unsigned_to_nat(0u);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_16, x_56);
x_58 = l_Lean_Compiler_LCNF_Decl_getArity(x_55);
lean_dec(x_55);
x_59 = lean_nat_dec_lt(x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
x_60 = x_149;
x_61 = x_53;
goto block_148;
}
else
{
lean_object* x_150; 
x_150 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_60 = x_150;
x_61 = x_53;
goto block_148;
}
block_148:
{
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_62 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_54;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_54);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_60, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_1, 2);
lean_inc(x_66);
x_67 = l_Lean_Compiler_LCNF_mkNewParams(x_66, x_5, x_6, x_7, x_8, x_61);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_array_get_size(x_68);
x_71 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_72 = 0;
lean_inc(x_68);
x_73 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_71, x_72, x_68);
x_74 = l_Lean_mkAppN(x_16, x_73);
x_75 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_76 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_74, x_75, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_83 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_68, x_81, x_82, x_5, x_6, x_7, x_8, x_78);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
x_88 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_86, x_87, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_89);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
lean_ctor_set(x_60, 0, x_84);
lean_ctor_set(x_90, 0, x_60);
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
lean_ctor_set(x_60, 0, x_84);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_60);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_84);
lean_free_object(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_88);
if (x_95 == 0)
{
return x_88;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_88, 0);
x_97 = lean_ctor_get(x_88, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_88);
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
lean_free_object(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_83);
if (x_99 == 0)
{
return x_83;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_83, 0);
x_101 = lean_ctor_get(x_83, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_83);
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
lean_dec(x_68);
lean_free_object(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_76);
if (x_103 == 0)
{
return x_76;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_76, 0);
x_105 = lean_ctor_get(x_76, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_76);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_60);
x_107 = lean_ctor_get(x_1, 2);
lean_inc(x_107);
x_108 = l_Lean_Compiler_LCNF_mkNewParams(x_107, x_5, x_6, x_7, x_8, x_61);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_array_get_size(x_109);
x_112 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_113 = 0;
lean_inc(x_109);
x_114 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_112, x_113, x_109);
x_115 = l_Lean_mkAppN(x_16, x_114);
x_116 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_117 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_115, x_116, x_5, x_6, x_7, x_8, x_110);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_124 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_109, x_122, x_123, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_ctor_get(x_1, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
x_129 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_127, x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_126);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_130);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_125);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_125);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_136 = lean_ctor_get(x_129, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_129, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_138 = x_129;
} else {
 lean_dec_ref(x_129);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_140 = lean_ctor_get(x_124, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_124, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_142 = x_124;
} else {
 lean_dec_ref(x_124);
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
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_144 = lean_ctor_get(x_117, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_117, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_146 = x_117;
} else {
 lean_dec_ref(x_117);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_13);
return x_168;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_st_ref_get(x_9, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_4, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 0;
x_19 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_17, x_11, x_18);
x_20 = lean_name_eq(x_19, x_2);
lean_dec(x_19);
x_21 = lean_box(x_20);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 0;
x_26 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_24, x_11, x_25);
x_27 = lean_name_eq(x_26, x_2);
lean_dec(x_26);
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
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
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_Expr_fvar___override(x_3);
x_11 = lean_array_push(x_2, x_10);
lean_inc(x_9);
x_12 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_inc(x_9);
x_15 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_9, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_4);
x_18 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_6, x_9, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Compiler_LCNF_Simp_simp(x_7, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = l_Lean_Expr_fvar___override(x_9);
x_26 = lean_array_get_size(x_8);
x_27 = l_Array_toSubarray___rarg(x_8, x_4, x_26);
x_28 = l_Array_ofSubarray___rarg(x_27);
x_29 = l_Lean_mkAppN(x_25, x_28);
x_30 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_31 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_29, x_30, x_10, x_11, x_12, x_13, x_16);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_6, x_34, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_7);
x_38 = l_Lean_Compiler_LCNF_Simp_simp(x_37, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_36);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_jp", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_12 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_22 = x_13;
} else {
 lean_dec_ref(x_13);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_21, 3);
lean_inc(x_23);
x_24 = lean_array_get_size(x_23);
x_25 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_21);
x_28 = lean_nat_dec_lt(x_24, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_21, 2);
lean_inc(x_29);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_27);
lean_inc(x_23);
x_31 = l_Array_toSubarray___rarg(x_23, x_30, x_27);
x_32 = l_Array_ofSubarray___rarg(x_31);
lean_inc(x_32);
x_33 = l_Lean_mkAppN(x_29, x_32);
x_34 = l_Lean_Expr_getAppFn(x_11);
lean_dec(x_11);
switch (lean_obj_tag(x_34)) {
case 0:
{
lean_object* x_35; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_35 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_21, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_dec(x_21);
x_40 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_38, x_39, x_32, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_220; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_220 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_220 == 0)
{
lean_object* x_221; 
x_221 = lean_box(0);
x_44 = x_221;
goto block_219;
}
else
{
uint8_t x_222; 
x_222 = lean_nat_dec_eq(x_24, x_27);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_box(0);
x_44 = x_223;
goto block_219;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_224 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_43);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = l_Lean_Compiler_LCNF_Simp_simp(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_225);
if (lean_obj_tag(x_226) == 0)
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_226, 0);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_226, 0, x_229);
return x_226;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_226, 0);
x_231 = lean_ctor_get(x_226, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_226);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_230);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
else
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_226);
if (x_234 == 0)
{
return x_226;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_226, 0);
x_236 = lean_ctor_get(x_226, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_226);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
block_219:
{
lean_object* x_45; 
lean_dec(x_44);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = l_Lean_Compiler_LCNF_Simp_simp(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_47);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_36);
x_51 = l_Lean_Expr_headBeta(x_36);
x_52 = l_Lean_Expr_isForall(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_53 = l_Lean_Compiler_LCNF_mkAuxParam(x_36, x_40, x_6, x_7, x_8, x_9, x_50);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_57 == 0)
{
lean_object* x_86; 
lean_dec(x_27);
lean_dec(x_23);
x_86 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_55);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_88 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_58 = x_89;
x_59 = x_90;
goto block_85;
}
else
{
uint8_t x_91; 
lean_dec(x_54);
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
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
lean_dec(x_54);
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_86);
if (x_95 == 0)
{
return x_86;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_86, 0);
x_97 = lean_ctor_get(x_86, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_86);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = l_Lean_Expr_fvar___override(x_56);
x_100 = lean_array_get_size(x_23);
x_101 = l_Array_toSubarray___rarg(x_23, x_27, x_100);
x_102 = l_Array_ofSubarray___rarg(x_101);
x_103 = l_Lean_mkAppN(x_99, x_102);
x_104 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_105 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_103, x_104, x_6, x_7, x_8, x_9, x_55);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_112 = l_Lean_Compiler_LCNF_Simp_simp(x_111, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_58 = x_113;
x_59 = x_114;
goto block_85;
}
else
{
uint8_t x_115; 
lean_dec(x_54);
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_115 = !lean_is_exclusive(x_112);
if (x_115 == 0)
{
return x_112;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_112, 0);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_112);
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
lean_dec(x_106);
lean_dec(x_54);
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_109);
if (x_119 == 0)
{
return x_109;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_109, 0);
x_121 = lean_ctor_get(x_109, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_109);
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
lean_dec(x_54);
lean_dec(x_46);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
block_85:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_61 = lean_array_push(x_60, x_54);
x_62 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_63 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_61, x_58, x_62, x_6, x_7, x_8, x_9, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_64);
x_66 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_66, 0, x_64);
lean_closure_set(x_66, 1, x_60);
x_67 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_46, x_66, x_6, x_7, x_8, x_9, x_65);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_22)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_22;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_67, 0, x_71);
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_67, 0);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_67);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_72);
if (lean_is_scalar(x_22)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_22;
}
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_64);
lean_dec(x_22);
x_77 = !lean_is_exclusive(x_67);
if (x_77 == 0)
{
return x_67;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_67, 0);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_67);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_81 = !lean_is_exclusive(x_63);
if (x_81 == 0)
{
return x_63;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_63, 0);
x_83 = lean_ctor_get(x_63, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_63);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_36);
x_127 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_128 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_129 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_127, x_46, x_128, x_6, x_7, x_8, x_9, x_50);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_132 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_130, x_6, x_7, x_8, x_9, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_136 == 0)
{
lean_object* x_151; 
lean_dec(x_27);
lean_dec(x_23);
x_151 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_135, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_134);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_153 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_137 = x_154;
x_138 = x_155;
goto block_150;
}
else
{
uint8_t x_156; 
lean_dec(x_133);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_156 = !lean_is_exclusive(x_153);
if (x_156 == 0)
{
return x_153;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_153, 0);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_153);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_133);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_151);
if (x_160 == 0)
{
return x_151;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_151, 0);
x_162 = lean_ctor_get(x_151, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_151);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = l_Lean_Expr_fvar___override(x_135);
x_165 = lean_array_get_size(x_23);
x_166 = l_Array_toSubarray___rarg(x_23, x_27, x_165);
x_167 = l_Array_ofSubarray___rarg(x_166);
x_168 = l_Lean_mkAppN(x_164, x_167);
x_169 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_170 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_168, x_169, x_6, x_7, x_8, x_9, x_134);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_173, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_171);
lean_ctor_set(x_176, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_177 = l_Lean_Compiler_LCNF_Simp_simp(x_176, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_175);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_137 = x_178;
x_138 = x_179;
goto block_150;
}
else
{
uint8_t x_180; 
lean_dec(x_133);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_180 = !lean_is_exclusive(x_177);
if (x_180 == 0)
{
return x_177;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_177, 0);
x_182 = lean_ctor_get(x_177, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_177);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_171);
lean_dec(x_133);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_184 = !lean_is_exclusive(x_174);
if (x_184 == 0)
{
return x_174;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_174, 0);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_174);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_133);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_170);
if (x_188 == 0)
{
return x_170;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_170, 0);
x_190 = lean_ctor_get(x_170, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_170);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
block_150:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_133);
x_140 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_141 = lean_array_push(x_140, x_139);
x_142 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_141, x_137, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_138);
lean_dec(x_141);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_142, 0);
if (lean_is_scalar(x_22)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_22;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_142, 0, x_145);
return x_142;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_142, 0);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_142);
if (lean_is_scalar(x_22)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_22;
}
lean_ctor_set(x_148, 0, x_146);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_132);
if (x_192 == 0)
{
return x_132;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_132, 0);
x_194 = lean_ctor_get(x_132, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_132);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_196 = !lean_is_exclusive(x_129);
if (x_196 == 0)
{
return x_129;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_129, 0);
x_198 = lean_ctor_get(x_129, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_129);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_36);
x_200 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_47);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_202, 0, x_3);
lean_closure_set(x_202, 1, x_4);
lean_closure_set(x_202, 2, x_5);
lean_closure_set(x_202, 3, x_27);
lean_closure_set(x_202, 4, x_24);
lean_closure_set(x_202, 5, x_26);
lean_closure_set(x_202, 6, x_2);
lean_closure_set(x_202, 7, x_23);
x_203 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_46, x_202, x_6, x_7, x_8, x_9, x_201);
if (lean_obj_tag(x_203) == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_203, 0);
if (lean_is_scalar(x_22)) {
 x_206 = lean_alloc_ctor(1, 1, 0);
} else {
 x_206 = x_22;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_203, 0, x_206);
return x_203;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_203, 0);
x_208 = lean_ctor_get(x_203, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_203);
if (lean_is_scalar(x_22)) {
 x_209 = lean_alloc_ctor(1, 1, 0);
} else {
 x_209 = x_22;
}
lean_ctor_set(x_209, 0, x_207);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
uint8_t x_211; 
lean_dec(x_22);
x_211 = !lean_is_exclusive(x_203);
if (x_211 == 0)
{
return x_203;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_203, 0);
x_213 = lean_ctor_get(x_203, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_203);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_215 = !lean_is_exclusive(x_45);
if (x_215 == 0)
{
return x_45;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_45, 0);
x_217 = lean_ctor_get(x_45, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_45);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_238 = !lean_is_exclusive(x_41);
if (x_238 == 0)
{
return x_41;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_41, 0);
x_240 = lean_ctor_get(x_41, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_41);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_242 = !lean_is_exclusive(x_35);
if (x_242 == 0)
{
return x_35;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_35, 0);
x_244 = lean_ctor_get(x_35, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_35);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
case 1:
{
lean_object* x_246; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_246 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_ctor_get(x_21, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_21, 1);
lean_inc(x_250);
lean_dec(x_21);
x_251 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_252 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_249, x_250, x_32, x_251, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_248);
lean_dec(x_249);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_431; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_431 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_431 == 0)
{
lean_object* x_432; 
x_432 = lean_box(0);
x_255 = x_432;
goto block_430;
}
else
{
uint8_t x_433; 
x_433 = lean_nat_dec_eq(x_24, x_27);
if (x_433 == 0)
{
lean_object* x_434; 
x_434 = lean_box(0);
x_255 = x_434;
goto block_430;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_247);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_435 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_254);
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
lean_dec(x_435);
x_437 = l_Lean_Compiler_LCNF_Simp_simp(x_253, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_436);
if (lean_obj_tag(x_437) == 0)
{
uint8_t x_438; 
x_438 = !lean_is_exclusive(x_437);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_ctor_get(x_437, 0);
x_440 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_437, 0, x_440);
return x_437;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_441 = lean_ctor_get(x_437, 0);
x_442 = lean_ctor_get(x_437, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_437);
x_443 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_443, 0, x_441);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_442);
return x_444;
}
}
else
{
uint8_t x_445; 
x_445 = !lean_is_exclusive(x_437);
if (x_445 == 0)
{
return x_437;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_437, 0);
x_447 = lean_ctor_get(x_437, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_437);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
}
}
block_430:
{
lean_object* x_256; 
lean_dec(x_255);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_256 = l_Lean_Compiler_LCNF_Simp_simp(x_253, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_254);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
lean_inc(x_257);
x_259 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_257);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_260 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_258);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
lean_inc(x_247);
x_262 = l_Lean_Expr_headBeta(x_247);
x_263 = l_Lean_Expr_isForall(x_262);
lean_dec(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; 
x_264 = l_Lean_Compiler_LCNF_mkAuxParam(x_247, x_251, x_6, x_7, x_8, x_9, x_261);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_ctor_get(x_265, 0);
lean_inc(x_267);
x_268 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_268 == 0)
{
lean_object* x_297; 
lean_dec(x_27);
lean_dec(x_23);
x_297 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_267, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_266);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
lean_dec(x_297);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_299 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_298);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_269 = x_300;
x_270 = x_301;
goto block_296;
}
else
{
uint8_t x_302; 
lean_dec(x_265);
lean_dec(x_257);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_302 = !lean_is_exclusive(x_299);
if (x_302 == 0)
{
return x_299;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_299, 0);
x_304 = lean_ctor_get(x_299, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_299);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_265);
lean_dec(x_257);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_306 = !lean_is_exclusive(x_297);
if (x_306 == 0)
{
return x_297;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_297, 0);
x_308 = lean_ctor_get(x_297, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_297);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_310 = l_Lean_Expr_fvar___override(x_267);
x_311 = lean_array_get_size(x_23);
x_312 = l_Array_toSubarray___rarg(x_23, x_27, x_311);
x_313 = l_Array_ofSubarray___rarg(x_312);
x_314 = l_Lean_mkAppN(x_310, x_313);
x_315 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_316 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_314, x_315, x_6, x_7, x_8, x_9, x_266);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
x_320 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_319, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_317);
lean_ctor_set(x_322, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_323 = l_Lean_Compiler_LCNF_Simp_simp(x_322, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_321);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_269 = x_324;
x_270 = x_325;
goto block_296;
}
else
{
uint8_t x_326; 
lean_dec(x_265);
lean_dec(x_257);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_326 = !lean_is_exclusive(x_323);
if (x_326 == 0)
{
return x_323;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_323, 0);
x_328 = lean_ctor_get(x_323, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_323);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
else
{
uint8_t x_330; 
lean_dec(x_317);
lean_dec(x_265);
lean_dec(x_257);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_330 = !lean_is_exclusive(x_320);
if (x_330 == 0)
{
return x_320;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_320, 0);
x_332 = lean_ctor_get(x_320, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_320);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
else
{
uint8_t x_334; 
lean_dec(x_265);
lean_dec(x_257);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_334 = !lean_is_exclusive(x_316);
if (x_334 == 0)
{
return x_316;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_316, 0);
x_336 = lean_ctor_get(x_316, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_316);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
return x_337;
}
}
}
block_296:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_272 = lean_array_push(x_271, x_265);
x_273 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_274 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_272, x_269, x_273, x_6, x_7, x_8, x_9, x_270);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
lean_inc(x_275);
x_277 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_277, 0, x_275);
lean_closure_set(x_277, 1, x_271);
x_278 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_257, x_277, x_6, x_7, x_8, x_9, x_276);
if (lean_obj_tag(x_278) == 0)
{
uint8_t x_279; 
x_279 = !lean_is_exclusive(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_278, 0);
x_281 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_281, 0, x_275);
lean_ctor_set(x_281, 1, x_280);
if (lean_is_scalar(x_22)) {
 x_282 = lean_alloc_ctor(1, 1, 0);
} else {
 x_282 = x_22;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_278, 0, x_282);
return x_278;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_283 = lean_ctor_get(x_278, 0);
x_284 = lean_ctor_get(x_278, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_278);
x_285 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_285, 0, x_275);
lean_ctor_set(x_285, 1, x_283);
if (lean_is_scalar(x_22)) {
 x_286 = lean_alloc_ctor(1, 1, 0);
} else {
 x_286 = x_22;
}
lean_ctor_set(x_286, 0, x_285);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_284);
return x_287;
}
}
else
{
uint8_t x_288; 
lean_dec(x_275);
lean_dec(x_22);
x_288 = !lean_is_exclusive(x_278);
if (x_288 == 0)
{
return x_278;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_278, 0);
x_290 = lean_ctor_get(x_278, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_278);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_257);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_292 = !lean_is_exclusive(x_274);
if (x_292 == 0)
{
return x_274;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_274, 0);
x_294 = lean_ctor_get(x_274, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_274);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_247);
x_338 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_339 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_340 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_338, x_257, x_339, x_6, x_7, x_8, x_9, x_261);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_343 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_341, x_6, x_7, x_8, x_9, x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_ctor_get(x_344, 0);
lean_inc(x_346);
x_347 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_347 == 0)
{
lean_object* x_362; 
lean_dec(x_27);
lean_dec(x_23);
x_362 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_346, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_345);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
lean_dec(x_362);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_364 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_363);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_348 = x_365;
x_349 = x_366;
goto block_361;
}
else
{
uint8_t x_367; 
lean_dec(x_344);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_367 = !lean_is_exclusive(x_364);
if (x_367 == 0)
{
return x_364;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_364, 0);
x_369 = lean_ctor_get(x_364, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_364);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
else
{
uint8_t x_371; 
lean_dec(x_344);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_371 = !lean_is_exclusive(x_362);
if (x_371 == 0)
{
return x_362;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_362, 0);
x_373 = lean_ctor_get(x_362, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_362);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_375 = l_Lean_Expr_fvar___override(x_346);
x_376 = lean_array_get_size(x_23);
x_377 = l_Array_toSubarray___rarg(x_23, x_27, x_376);
x_378 = l_Array_ofSubarray___rarg(x_377);
x_379 = l_Lean_mkAppN(x_375, x_378);
x_380 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_381 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_379, x_380, x_6, x_7, x_8, x_9, x_345);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_384 = lean_ctor_get(x_382, 0);
lean_inc(x_384);
x_385 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_384, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_383);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
lean_dec(x_385);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_382);
lean_ctor_set(x_387, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_388 = l_Lean_Compiler_LCNF_Simp_simp(x_387, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_386);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_348 = x_389;
x_349 = x_390;
goto block_361;
}
else
{
uint8_t x_391; 
lean_dec(x_344);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_391 = !lean_is_exclusive(x_388);
if (x_391 == 0)
{
return x_388;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_388, 0);
x_393 = lean_ctor_get(x_388, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_388);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
return x_394;
}
}
}
else
{
uint8_t x_395; 
lean_dec(x_382);
lean_dec(x_344);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_395 = !lean_is_exclusive(x_385);
if (x_395 == 0)
{
return x_385;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_385, 0);
x_397 = lean_ctor_get(x_385, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_385);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
}
else
{
uint8_t x_399; 
lean_dec(x_344);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_399 = !lean_is_exclusive(x_381);
if (x_399 == 0)
{
return x_381;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_381, 0);
x_401 = lean_ctor_get(x_381, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_381);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
return x_402;
}
}
}
block_361:
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_344);
x_351 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_352 = lean_array_push(x_351, x_350);
x_353 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_352, x_348, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_349);
lean_dec(x_352);
x_354 = !lean_is_exclusive(x_353);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_353, 0);
if (lean_is_scalar(x_22)) {
 x_356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_356 = x_22;
}
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_353, 0, x_356);
return x_353;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_357 = lean_ctor_get(x_353, 0);
x_358 = lean_ctor_get(x_353, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_353);
if (lean_is_scalar(x_22)) {
 x_359 = lean_alloc_ctor(1, 1, 0);
} else {
 x_359 = x_22;
}
lean_ctor_set(x_359, 0, x_357);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
}
else
{
uint8_t x_403; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_403 = !lean_is_exclusive(x_343);
if (x_403 == 0)
{
return x_343;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_343, 0);
x_405 = lean_ctor_get(x_343, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_343);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
return x_406;
}
}
}
else
{
uint8_t x_407; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_407 = !lean_is_exclusive(x_340);
if (x_407 == 0)
{
return x_340;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_340, 0);
x_409 = lean_ctor_get(x_340, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_340);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_247);
x_411 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_258);
x_412 = lean_ctor_get(x_411, 1);
lean_inc(x_412);
lean_dec(x_411);
x_413 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_413, 0, x_3);
lean_closure_set(x_413, 1, x_4);
lean_closure_set(x_413, 2, x_5);
lean_closure_set(x_413, 3, x_27);
lean_closure_set(x_413, 4, x_24);
lean_closure_set(x_413, 5, x_26);
lean_closure_set(x_413, 6, x_2);
lean_closure_set(x_413, 7, x_23);
x_414 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_257, x_413, x_6, x_7, x_8, x_9, x_412);
if (lean_obj_tag(x_414) == 0)
{
uint8_t x_415; 
x_415 = !lean_is_exclusive(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; 
x_416 = lean_ctor_get(x_414, 0);
if (lean_is_scalar(x_22)) {
 x_417 = lean_alloc_ctor(1, 1, 0);
} else {
 x_417 = x_22;
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_414, 0, x_417);
return x_414;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_418 = lean_ctor_get(x_414, 0);
x_419 = lean_ctor_get(x_414, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_414);
if (lean_is_scalar(x_22)) {
 x_420 = lean_alloc_ctor(1, 1, 0);
} else {
 x_420 = x_22;
}
lean_ctor_set(x_420, 0, x_418);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
else
{
uint8_t x_422; 
lean_dec(x_22);
x_422 = !lean_is_exclusive(x_414);
if (x_422 == 0)
{
return x_414;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_414, 0);
x_424 = lean_ctor_get(x_414, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_414);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_247);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_426 = !lean_is_exclusive(x_256);
if (x_426 == 0)
{
return x_256;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_256, 0);
x_428 = lean_ctor_get(x_256, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_256);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
}
else
{
uint8_t x_449; 
lean_dec(x_247);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_449 = !lean_is_exclusive(x_252);
if (x_449 == 0)
{
return x_252;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_252, 0);
x_451 = lean_ctor_get(x_252, 1);
lean_inc(x_451);
lean_inc(x_450);
lean_dec(x_252);
x_452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_451);
return x_452;
}
}
}
else
{
uint8_t x_453; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_453 = !lean_is_exclusive(x_246);
if (x_453 == 0)
{
return x_246;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_246, 0);
x_455 = lean_ctor_get(x_246, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_246);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
case 2:
{
lean_object* x_457; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_457 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec(x_457);
x_460 = lean_ctor_get(x_21, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_21, 1);
lean_inc(x_461);
lean_dec(x_21);
x_462 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_463 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_460, x_461, x_32, x_462, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_459);
lean_dec(x_460);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_642; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
x_642 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_642 == 0)
{
lean_object* x_643; 
x_643 = lean_box(0);
x_466 = x_643;
goto block_641;
}
else
{
uint8_t x_644; 
x_644 = lean_nat_dec_eq(x_24, x_27);
if (x_644 == 0)
{
lean_object* x_645; 
x_645 = lean_box(0);
x_466 = x_645;
goto block_641;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec(x_458);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_646 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_465);
x_647 = lean_ctor_get(x_646, 1);
lean_inc(x_647);
lean_dec(x_646);
x_648 = l_Lean_Compiler_LCNF_Simp_simp(x_464, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_647);
if (lean_obj_tag(x_648) == 0)
{
uint8_t x_649; 
x_649 = !lean_is_exclusive(x_648);
if (x_649 == 0)
{
lean_object* x_650; lean_object* x_651; 
x_650 = lean_ctor_get(x_648, 0);
x_651 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_648, 0, x_651);
return x_648;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_652 = lean_ctor_get(x_648, 0);
x_653 = lean_ctor_get(x_648, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_648);
x_654 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_654, 0, x_652);
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_653);
return x_655;
}
}
else
{
uint8_t x_656; 
x_656 = !lean_is_exclusive(x_648);
if (x_656 == 0)
{
return x_648;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_648, 0);
x_658 = lean_ctor_get(x_648, 1);
lean_inc(x_658);
lean_inc(x_657);
lean_dec(x_648);
x_659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_659, 0, x_657);
lean_ctor_set(x_659, 1, x_658);
return x_659;
}
}
}
}
block_641:
{
lean_object* x_467; 
lean_dec(x_466);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_467 = l_Lean_Compiler_LCNF_Simp_simp(x_464, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_465);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; uint8_t x_470; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
lean_inc(x_468);
x_470 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_468);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; 
x_471 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_469);
x_472 = lean_ctor_get(x_471, 1);
lean_inc(x_472);
lean_dec(x_471);
lean_inc(x_458);
x_473 = l_Lean_Expr_headBeta(x_458);
x_474 = l_Lean_Expr_isForall(x_473);
lean_dec(x_473);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; 
x_475 = l_Lean_Compiler_LCNF_mkAuxParam(x_458, x_462, x_6, x_7, x_8, x_9, x_472);
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
x_478 = lean_ctor_get(x_476, 0);
lean_inc(x_478);
x_479 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_479 == 0)
{
lean_object* x_508; 
lean_dec(x_27);
lean_dec(x_23);
x_508 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_478, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_477);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; 
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
lean_dec(x_508);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_510 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_509);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_480 = x_511;
x_481 = x_512;
goto block_507;
}
else
{
uint8_t x_513; 
lean_dec(x_476);
lean_dec(x_468);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_513 = !lean_is_exclusive(x_510);
if (x_513 == 0)
{
return x_510;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_510, 0);
x_515 = lean_ctor_get(x_510, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_510);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
return x_516;
}
}
}
else
{
uint8_t x_517; 
lean_dec(x_476);
lean_dec(x_468);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_517 = !lean_is_exclusive(x_508);
if (x_517 == 0)
{
return x_508;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_508, 0);
x_519 = lean_ctor_get(x_508, 1);
lean_inc(x_519);
lean_inc(x_518);
lean_dec(x_508);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
return x_520;
}
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_521 = l_Lean_Expr_fvar___override(x_478);
x_522 = lean_array_get_size(x_23);
x_523 = l_Array_toSubarray___rarg(x_23, x_27, x_522);
x_524 = l_Array_ofSubarray___rarg(x_523);
x_525 = l_Lean_mkAppN(x_521, x_524);
x_526 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_527 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_525, x_526, x_6, x_7, x_8, x_9, x_477);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
x_530 = lean_ctor_get(x_528, 0);
lean_inc(x_530);
x_531 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_530, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_529);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_531, 1);
lean_inc(x_532);
lean_dec(x_531);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_528);
lean_ctor_set(x_533, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_534 = l_Lean_Compiler_LCNF_Simp_simp(x_533, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_532);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_480 = x_535;
x_481 = x_536;
goto block_507;
}
else
{
uint8_t x_537; 
lean_dec(x_476);
lean_dec(x_468);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_537 = !lean_is_exclusive(x_534);
if (x_537 == 0)
{
return x_534;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_538 = lean_ctor_get(x_534, 0);
x_539 = lean_ctor_get(x_534, 1);
lean_inc(x_539);
lean_inc(x_538);
lean_dec(x_534);
x_540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_540, 0, x_538);
lean_ctor_set(x_540, 1, x_539);
return x_540;
}
}
}
else
{
uint8_t x_541; 
lean_dec(x_528);
lean_dec(x_476);
lean_dec(x_468);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_541 = !lean_is_exclusive(x_531);
if (x_541 == 0)
{
return x_531;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_ctor_get(x_531, 0);
x_543 = lean_ctor_get(x_531, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_531);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
return x_544;
}
}
}
else
{
uint8_t x_545; 
lean_dec(x_476);
lean_dec(x_468);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_545 = !lean_is_exclusive(x_527);
if (x_545 == 0)
{
return x_527;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_527, 0);
x_547 = lean_ctor_get(x_527, 1);
lean_inc(x_547);
lean_inc(x_546);
lean_dec(x_527);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
return x_548;
}
}
}
block_507:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_482 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_483 = lean_array_push(x_482, x_476);
x_484 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_485 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_483, x_480, x_484, x_6, x_7, x_8, x_9, x_481);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
lean_inc(x_486);
x_488 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_488, 0, x_486);
lean_closure_set(x_488, 1, x_482);
x_489 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_468, x_488, x_6, x_7, x_8, x_9, x_487);
if (lean_obj_tag(x_489) == 0)
{
uint8_t x_490; 
x_490 = !lean_is_exclusive(x_489);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_489, 0);
x_492 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_492, 0, x_486);
lean_ctor_set(x_492, 1, x_491);
if (lean_is_scalar(x_22)) {
 x_493 = lean_alloc_ctor(1, 1, 0);
} else {
 x_493 = x_22;
}
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_489, 0, x_493);
return x_489;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_494 = lean_ctor_get(x_489, 0);
x_495 = lean_ctor_get(x_489, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_489);
x_496 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_496, 0, x_486);
lean_ctor_set(x_496, 1, x_494);
if (lean_is_scalar(x_22)) {
 x_497 = lean_alloc_ctor(1, 1, 0);
} else {
 x_497 = x_22;
}
lean_ctor_set(x_497, 0, x_496);
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_495);
return x_498;
}
}
else
{
uint8_t x_499; 
lean_dec(x_486);
lean_dec(x_22);
x_499 = !lean_is_exclusive(x_489);
if (x_499 == 0)
{
return x_489;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_489, 0);
x_501 = lean_ctor_get(x_489, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_489);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
}
else
{
uint8_t x_503; 
lean_dec(x_468);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_503 = !lean_is_exclusive(x_485);
if (x_503 == 0)
{
return x_485;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_485, 0);
x_505 = lean_ctor_get(x_485, 1);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_485);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
return x_506;
}
}
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_458);
x_549 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_550 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_551 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_549, x_468, x_550, x_6, x_7, x_8, x_9, x_472);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_554 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_552, x_6, x_7, x_8, x_9, x_553);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; uint8_t x_558; lean_object* x_559; lean_object* x_560; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = lean_ctor_get(x_555, 0);
lean_inc(x_557);
x_558 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_558 == 0)
{
lean_object* x_573; 
lean_dec(x_27);
lean_dec(x_23);
x_573 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_557, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_556);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_ctor_get(x_573, 1);
lean_inc(x_574);
lean_dec(x_573);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_575 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_574);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_575, 1);
lean_inc(x_577);
lean_dec(x_575);
x_559 = x_576;
x_560 = x_577;
goto block_572;
}
else
{
uint8_t x_578; 
lean_dec(x_555);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_578 = !lean_is_exclusive(x_575);
if (x_578 == 0)
{
return x_575;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_575, 0);
x_580 = lean_ctor_get(x_575, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_575);
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
return x_581;
}
}
}
else
{
uint8_t x_582; 
lean_dec(x_555);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_582 = !lean_is_exclusive(x_573);
if (x_582 == 0)
{
return x_573;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_573, 0);
x_584 = lean_ctor_get(x_573, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_573);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_586 = l_Lean_Expr_fvar___override(x_557);
x_587 = lean_array_get_size(x_23);
x_588 = l_Array_toSubarray___rarg(x_23, x_27, x_587);
x_589 = l_Array_ofSubarray___rarg(x_588);
x_590 = l_Lean_mkAppN(x_586, x_589);
x_591 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_592 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_590, x_591, x_6, x_7, x_8, x_9, x_556);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
lean_dec(x_592);
x_595 = lean_ctor_get(x_593, 0);
lean_inc(x_595);
x_596 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_595, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_594);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
lean_dec(x_596);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_593);
lean_ctor_set(x_598, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_599 = l_Lean_Compiler_LCNF_Simp_simp(x_598, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_597);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_559 = x_600;
x_560 = x_601;
goto block_572;
}
else
{
uint8_t x_602; 
lean_dec(x_555);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_602 = !lean_is_exclusive(x_599);
if (x_602 == 0)
{
return x_599;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_599, 0);
x_604 = lean_ctor_get(x_599, 1);
lean_inc(x_604);
lean_inc(x_603);
lean_dec(x_599);
x_605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_605, 0, x_603);
lean_ctor_set(x_605, 1, x_604);
return x_605;
}
}
}
else
{
uint8_t x_606; 
lean_dec(x_593);
lean_dec(x_555);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_606 = !lean_is_exclusive(x_596);
if (x_606 == 0)
{
return x_596;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_596, 0);
x_608 = lean_ctor_get(x_596, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_596);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
return x_609;
}
}
}
else
{
uint8_t x_610; 
lean_dec(x_555);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_610 = !lean_is_exclusive(x_592);
if (x_610 == 0)
{
return x_592;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_611 = lean_ctor_get(x_592, 0);
x_612 = lean_ctor_get(x_592, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_592);
x_613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_613, 0, x_611);
lean_ctor_set(x_613, 1, x_612);
return x_613;
}
}
}
block_572:
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; uint8_t x_565; 
x_561 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_561, 0, x_555);
x_562 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_563 = lean_array_push(x_562, x_561);
x_564 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_563, x_559, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_560);
lean_dec(x_563);
x_565 = !lean_is_exclusive(x_564);
if (x_565 == 0)
{
lean_object* x_566; lean_object* x_567; 
x_566 = lean_ctor_get(x_564, 0);
if (lean_is_scalar(x_22)) {
 x_567 = lean_alloc_ctor(1, 1, 0);
} else {
 x_567 = x_22;
}
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_564, 0, x_567);
return x_564;
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_568 = lean_ctor_get(x_564, 0);
x_569 = lean_ctor_get(x_564, 1);
lean_inc(x_569);
lean_inc(x_568);
lean_dec(x_564);
if (lean_is_scalar(x_22)) {
 x_570 = lean_alloc_ctor(1, 1, 0);
} else {
 x_570 = x_22;
}
lean_ctor_set(x_570, 0, x_568);
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_569);
return x_571;
}
}
}
else
{
uint8_t x_614; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_614 = !lean_is_exclusive(x_554);
if (x_614 == 0)
{
return x_554;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_554, 0);
x_616 = lean_ctor_get(x_554, 1);
lean_inc(x_616);
lean_inc(x_615);
lean_dec(x_554);
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set(x_617, 1, x_616);
return x_617;
}
}
}
else
{
uint8_t x_618; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_618 = !lean_is_exclusive(x_551);
if (x_618 == 0)
{
return x_551;
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_619 = lean_ctor_get(x_551, 0);
x_620 = lean_ctor_get(x_551, 1);
lean_inc(x_620);
lean_inc(x_619);
lean_dec(x_551);
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_619);
lean_ctor_set(x_621, 1, x_620);
return x_621;
}
}
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_458);
x_622 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_469);
x_623 = lean_ctor_get(x_622, 1);
lean_inc(x_623);
lean_dec(x_622);
x_624 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_624, 0, x_3);
lean_closure_set(x_624, 1, x_4);
lean_closure_set(x_624, 2, x_5);
lean_closure_set(x_624, 3, x_27);
lean_closure_set(x_624, 4, x_24);
lean_closure_set(x_624, 5, x_26);
lean_closure_set(x_624, 6, x_2);
lean_closure_set(x_624, 7, x_23);
x_625 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_468, x_624, x_6, x_7, x_8, x_9, x_623);
if (lean_obj_tag(x_625) == 0)
{
uint8_t x_626; 
x_626 = !lean_is_exclusive(x_625);
if (x_626 == 0)
{
lean_object* x_627; lean_object* x_628; 
x_627 = lean_ctor_get(x_625, 0);
if (lean_is_scalar(x_22)) {
 x_628 = lean_alloc_ctor(1, 1, 0);
} else {
 x_628 = x_22;
}
lean_ctor_set(x_628, 0, x_627);
lean_ctor_set(x_625, 0, x_628);
return x_625;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_629 = lean_ctor_get(x_625, 0);
x_630 = lean_ctor_get(x_625, 1);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_625);
if (lean_is_scalar(x_22)) {
 x_631 = lean_alloc_ctor(1, 1, 0);
} else {
 x_631 = x_22;
}
lean_ctor_set(x_631, 0, x_629);
x_632 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_630);
return x_632;
}
}
else
{
uint8_t x_633; 
lean_dec(x_22);
x_633 = !lean_is_exclusive(x_625);
if (x_633 == 0)
{
return x_625;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_634 = lean_ctor_get(x_625, 0);
x_635 = lean_ctor_get(x_625, 1);
lean_inc(x_635);
lean_inc(x_634);
lean_dec(x_625);
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set(x_636, 1, x_635);
return x_636;
}
}
}
}
else
{
uint8_t x_637; 
lean_dec(x_458);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_637 = !lean_is_exclusive(x_467);
if (x_637 == 0)
{
return x_467;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_467, 0);
x_639 = lean_ctor_get(x_467, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_467);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
return x_640;
}
}
}
}
else
{
uint8_t x_660; 
lean_dec(x_458);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_660 = !lean_is_exclusive(x_463);
if (x_660 == 0)
{
return x_463;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_661 = lean_ctor_get(x_463, 0);
x_662 = lean_ctor_get(x_463, 1);
lean_inc(x_662);
lean_inc(x_661);
lean_dec(x_463);
x_663 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_663, 0, x_661);
lean_ctor_set(x_663, 1, x_662);
return x_663;
}
}
}
else
{
uint8_t x_664; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_664 = !lean_is_exclusive(x_457);
if (x_664 == 0)
{
return x_457;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_457, 0);
x_666 = lean_ctor_get(x_457, 1);
lean_inc(x_666);
lean_inc(x_665);
lean_dec(x_457);
x_667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_667, 0, x_665);
lean_ctor_set(x_667, 1, x_666);
return x_667;
}
}
}
case 3:
{
lean_object* x_668; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_668 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; uint8_t x_673; lean_object* x_674; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
lean_dec(x_668);
x_671 = lean_ctor_get(x_21, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_21, 1);
lean_inc(x_672);
lean_dec(x_21);
x_673 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_674 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_671, x_672, x_32, x_673, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_670);
lean_dec(x_671);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; uint8_t x_853; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
x_853 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_853 == 0)
{
lean_object* x_854; 
x_854 = lean_box(0);
x_677 = x_854;
goto block_852;
}
else
{
uint8_t x_855; 
x_855 = lean_nat_dec_eq(x_24, x_27);
if (x_855 == 0)
{
lean_object* x_856; 
x_856 = lean_box(0);
x_677 = x_856;
goto block_852;
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; 
lean_dec(x_669);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_857 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_676);
x_858 = lean_ctor_get(x_857, 1);
lean_inc(x_858);
lean_dec(x_857);
x_859 = l_Lean_Compiler_LCNF_Simp_simp(x_675, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_858);
if (lean_obj_tag(x_859) == 0)
{
uint8_t x_860; 
x_860 = !lean_is_exclusive(x_859);
if (x_860 == 0)
{
lean_object* x_861; lean_object* x_862; 
x_861 = lean_ctor_get(x_859, 0);
x_862 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_859, 0, x_862);
return x_859;
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
x_863 = lean_ctor_get(x_859, 0);
x_864 = lean_ctor_get(x_859, 1);
lean_inc(x_864);
lean_inc(x_863);
lean_dec(x_859);
x_865 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_865, 0, x_863);
x_866 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_866, 0, x_865);
lean_ctor_set(x_866, 1, x_864);
return x_866;
}
}
else
{
uint8_t x_867; 
x_867 = !lean_is_exclusive(x_859);
if (x_867 == 0)
{
return x_859;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_859, 0);
x_869 = lean_ctor_get(x_859, 1);
lean_inc(x_869);
lean_inc(x_868);
lean_dec(x_859);
x_870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_870, 1, x_869);
return x_870;
}
}
}
}
block_852:
{
lean_object* x_678; 
lean_dec(x_677);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_678 = l_Lean_Compiler_LCNF_Simp_simp(x_675, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_676);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; uint8_t x_681; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 1);
lean_inc(x_680);
lean_dec(x_678);
lean_inc(x_679);
x_681 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_679);
if (x_681 == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; 
x_682 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_680);
x_683 = lean_ctor_get(x_682, 1);
lean_inc(x_683);
lean_dec(x_682);
lean_inc(x_669);
x_684 = l_Lean_Expr_headBeta(x_669);
x_685 = l_Lean_Expr_isForall(x_684);
lean_dec(x_684);
if (x_685 == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; uint8_t x_690; lean_object* x_691; lean_object* x_692; 
x_686 = l_Lean_Compiler_LCNF_mkAuxParam(x_669, x_673, x_6, x_7, x_8, x_9, x_683);
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
lean_dec(x_686);
x_689 = lean_ctor_get(x_687, 0);
lean_inc(x_689);
x_690 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_690 == 0)
{
lean_object* x_719; 
lean_dec(x_27);
lean_dec(x_23);
x_719 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_689, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_688);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; 
x_720 = lean_ctor_get(x_719, 1);
lean_inc(x_720);
lean_dec(x_719);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_721 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_720);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec(x_721);
x_691 = x_722;
x_692 = x_723;
goto block_718;
}
else
{
uint8_t x_724; 
lean_dec(x_687);
lean_dec(x_679);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_724 = !lean_is_exclusive(x_721);
if (x_724 == 0)
{
return x_721;
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_725 = lean_ctor_get(x_721, 0);
x_726 = lean_ctor_get(x_721, 1);
lean_inc(x_726);
lean_inc(x_725);
lean_dec(x_721);
x_727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_727, 0, x_725);
lean_ctor_set(x_727, 1, x_726);
return x_727;
}
}
}
else
{
uint8_t x_728; 
lean_dec(x_687);
lean_dec(x_679);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_728 = !lean_is_exclusive(x_719);
if (x_728 == 0)
{
return x_719;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_719, 0);
x_730 = lean_ctor_get(x_719, 1);
lean_inc(x_730);
lean_inc(x_729);
lean_dec(x_719);
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
return x_731;
}
}
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_732 = l_Lean_Expr_fvar___override(x_689);
x_733 = lean_array_get_size(x_23);
x_734 = l_Array_toSubarray___rarg(x_23, x_27, x_733);
x_735 = l_Array_ofSubarray___rarg(x_734);
x_736 = l_Lean_mkAppN(x_732, x_735);
x_737 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_738 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_736, x_737, x_6, x_7, x_8, x_9, x_688);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_738, 1);
lean_inc(x_740);
lean_dec(x_738);
x_741 = lean_ctor_get(x_739, 0);
lean_inc(x_741);
x_742 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_741, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_740);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_743 = lean_ctor_get(x_742, 1);
lean_inc(x_743);
lean_dec(x_742);
x_744 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_744, 0, x_739);
lean_ctor_set(x_744, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_745 = l_Lean_Compiler_LCNF_Simp_simp(x_744, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_743);
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_746; lean_object* x_747; 
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_745, 1);
lean_inc(x_747);
lean_dec(x_745);
x_691 = x_746;
x_692 = x_747;
goto block_718;
}
else
{
uint8_t x_748; 
lean_dec(x_687);
lean_dec(x_679);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_748 = !lean_is_exclusive(x_745);
if (x_748 == 0)
{
return x_745;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_749 = lean_ctor_get(x_745, 0);
x_750 = lean_ctor_get(x_745, 1);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_745);
x_751 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
return x_751;
}
}
}
else
{
uint8_t x_752; 
lean_dec(x_739);
lean_dec(x_687);
lean_dec(x_679);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_752 = !lean_is_exclusive(x_742);
if (x_752 == 0)
{
return x_742;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_ctor_get(x_742, 0);
x_754 = lean_ctor_get(x_742, 1);
lean_inc(x_754);
lean_inc(x_753);
lean_dec(x_742);
x_755 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_755, 0, x_753);
lean_ctor_set(x_755, 1, x_754);
return x_755;
}
}
}
else
{
uint8_t x_756; 
lean_dec(x_687);
lean_dec(x_679);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_756 = !lean_is_exclusive(x_738);
if (x_756 == 0)
{
return x_738;
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_757 = lean_ctor_get(x_738, 0);
x_758 = lean_ctor_get(x_738, 1);
lean_inc(x_758);
lean_inc(x_757);
lean_dec(x_738);
x_759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_759, 0, x_757);
lean_ctor_set(x_759, 1, x_758);
return x_759;
}
}
}
block_718:
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_693 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_694 = lean_array_push(x_693, x_687);
x_695 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_696 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_694, x_691, x_695, x_6, x_7, x_8, x_9, x_692);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
lean_inc(x_697);
x_699 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_699, 0, x_697);
lean_closure_set(x_699, 1, x_693);
x_700 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_679, x_699, x_6, x_7, x_8, x_9, x_698);
if (lean_obj_tag(x_700) == 0)
{
uint8_t x_701; 
x_701 = !lean_is_exclusive(x_700);
if (x_701 == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_702 = lean_ctor_get(x_700, 0);
x_703 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_703, 0, x_697);
lean_ctor_set(x_703, 1, x_702);
if (lean_is_scalar(x_22)) {
 x_704 = lean_alloc_ctor(1, 1, 0);
} else {
 x_704 = x_22;
}
lean_ctor_set(x_704, 0, x_703);
lean_ctor_set(x_700, 0, x_704);
return x_700;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_705 = lean_ctor_get(x_700, 0);
x_706 = lean_ctor_get(x_700, 1);
lean_inc(x_706);
lean_inc(x_705);
lean_dec(x_700);
x_707 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_707, 0, x_697);
lean_ctor_set(x_707, 1, x_705);
if (lean_is_scalar(x_22)) {
 x_708 = lean_alloc_ctor(1, 1, 0);
} else {
 x_708 = x_22;
}
lean_ctor_set(x_708, 0, x_707);
x_709 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_709, 0, x_708);
lean_ctor_set(x_709, 1, x_706);
return x_709;
}
}
else
{
uint8_t x_710; 
lean_dec(x_697);
lean_dec(x_22);
x_710 = !lean_is_exclusive(x_700);
if (x_710 == 0)
{
return x_700;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_711 = lean_ctor_get(x_700, 0);
x_712 = lean_ctor_get(x_700, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_700);
x_713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_713, 0, x_711);
lean_ctor_set(x_713, 1, x_712);
return x_713;
}
}
}
else
{
uint8_t x_714; 
lean_dec(x_679);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_714 = !lean_is_exclusive(x_696);
if (x_714 == 0)
{
return x_696;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_696, 0);
x_716 = lean_ctor_get(x_696, 1);
lean_inc(x_716);
lean_inc(x_715);
lean_dec(x_696);
x_717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
return x_717;
}
}
}
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; 
lean_dec(x_669);
x_760 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_761 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_762 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_760, x_679, x_761, x_6, x_7, x_8, x_9, x_683);
if (lean_obj_tag(x_762) == 0)
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_763 = lean_ctor_get(x_762, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_762, 1);
lean_inc(x_764);
lean_dec(x_762);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_765 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_763, x_6, x_7, x_8, x_9, x_764);
if (lean_obj_tag(x_765) == 0)
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; uint8_t x_769; lean_object* x_770; lean_object* x_771; 
x_766 = lean_ctor_get(x_765, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_765, 1);
lean_inc(x_767);
lean_dec(x_765);
x_768 = lean_ctor_get(x_766, 0);
lean_inc(x_768);
x_769 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_769 == 0)
{
lean_object* x_784; 
lean_dec(x_27);
lean_dec(x_23);
x_784 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_768, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_767);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; 
x_785 = lean_ctor_get(x_784, 1);
lean_inc(x_785);
lean_dec(x_784);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_786 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_785);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; lean_object* x_788; 
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec(x_786);
x_770 = x_787;
x_771 = x_788;
goto block_783;
}
else
{
uint8_t x_789; 
lean_dec(x_766);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_789 = !lean_is_exclusive(x_786);
if (x_789 == 0)
{
return x_786;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_786, 0);
x_791 = lean_ctor_get(x_786, 1);
lean_inc(x_791);
lean_inc(x_790);
lean_dec(x_786);
x_792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_792, 0, x_790);
lean_ctor_set(x_792, 1, x_791);
return x_792;
}
}
}
else
{
uint8_t x_793; 
lean_dec(x_766);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_793 = !lean_is_exclusive(x_784);
if (x_793 == 0)
{
return x_784;
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_794 = lean_ctor_get(x_784, 0);
x_795 = lean_ctor_get(x_784, 1);
lean_inc(x_795);
lean_inc(x_794);
lean_dec(x_784);
x_796 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_796, 0, x_794);
lean_ctor_set(x_796, 1, x_795);
return x_796;
}
}
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_797 = l_Lean_Expr_fvar___override(x_768);
x_798 = lean_array_get_size(x_23);
x_799 = l_Array_toSubarray___rarg(x_23, x_27, x_798);
x_800 = l_Array_ofSubarray___rarg(x_799);
x_801 = l_Lean_mkAppN(x_797, x_800);
x_802 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_803 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_801, x_802, x_6, x_7, x_8, x_9, x_767);
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
lean_dec(x_803);
x_806 = lean_ctor_get(x_804, 0);
lean_inc(x_806);
x_807 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_806, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_805);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_808 = lean_ctor_get(x_807, 1);
lean_inc(x_808);
lean_dec(x_807);
x_809 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_809, 0, x_804);
lean_ctor_set(x_809, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_810 = l_Lean_Compiler_LCNF_Simp_simp(x_809, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_808);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; 
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_810, 1);
lean_inc(x_812);
lean_dec(x_810);
x_770 = x_811;
x_771 = x_812;
goto block_783;
}
else
{
uint8_t x_813; 
lean_dec(x_766);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_813 = !lean_is_exclusive(x_810);
if (x_813 == 0)
{
return x_810;
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_814 = lean_ctor_get(x_810, 0);
x_815 = lean_ctor_get(x_810, 1);
lean_inc(x_815);
lean_inc(x_814);
lean_dec(x_810);
x_816 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_816, 0, x_814);
lean_ctor_set(x_816, 1, x_815);
return x_816;
}
}
}
else
{
uint8_t x_817; 
lean_dec(x_804);
lean_dec(x_766);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_817 = !lean_is_exclusive(x_807);
if (x_817 == 0)
{
return x_807;
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_818 = lean_ctor_get(x_807, 0);
x_819 = lean_ctor_get(x_807, 1);
lean_inc(x_819);
lean_inc(x_818);
lean_dec(x_807);
x_820 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_820, 0, x_818);
lean_ctor_set(x_820, 1, x_819);
return x_820;
}
}
}
else
{
uint8_t x_821; 
lean_dec(x_766);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_821 = !lean_is_exclusive(x_803);
if (x_821 == 0)
{
return x_803;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_803, 0);
x_823 = lean_ctor_get(x_803, 1);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_803);
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_822);
lean_ctor_set(x_824, 1, x_823);
return x_824;
}
}
}
block_783:
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; uint8_t x_776; 
x_772 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_772, 0, x_766);
x_773 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_774 = lean_array_push(x_773, x_772);
x_775 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_774, x_770, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_771);
lean_dec(x_774);
x_776 = !lean_is_exclusive(x_775);
if (x_776 == 0)
{
lean_object* x_777; lean_object* x_778; 
x_777 = lean_ctor_get(x_775, 0);
if (lean_is_scalar(x_22)) {
 x_778 = lean_alloc_ctor(1, 1, 0);
} else {
 x_778 = x_22;
}
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_775, 0, x_778);
return x_775;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_779 = lean_ctor_get(x_775, 0);
x_780 = lean_ctor_get(x_775, 1);
lean_inc(x_780);
lean_inc(x_779);
lean_dec(x_775);
if (lean_is_scalar(x_22)) {
 x_781 = lean_alloc_ctor(1, 1, 0);
} else {
 x_781 = x_22;
}
lean_ctor_set(x_781, 0, x_779);
x_782 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_780);
return x_782;
}
}
}
else
{
uint8_t x_825; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_825 = !lean_is_exclusive(x_765);
if (x_825 == 0)
{
return x_765;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_826 = lean_ctor_get(x_765, 0);
x_827 = lean_ctor_get(x_765, 1);
lean_inc(x_827);
lean_inc(x_826);
lean_dec(x_765);
x_828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_828, 0, x_826);
lean_ctor_set(x_828, 1, x_827);
return x_828;
}
}
}
else
{
uint8_t x_829; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_829 = !lean_is_exclusive(x_762);
if (x_829 == 0)
{
return x_762;
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_830 = lean_ctor_get(x_762, 0);
x_831 = lean_ctor_get(x_762, 1);
lean_inc(x_831);
lean_inc(x_830);
lean_dec(x_762);
x_832 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_832, 0, x_830);
lean_ctor_set(x_832, 1, x_831);
return x_832;
}
}
}
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
lean_dec(x_669);
x_833 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_680);
x_834 = lean_ctor_get(x_833, 1);
lean_inc(x_834);
lean_dec(x_833);
x_835 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_835, 0, x_3);
lean_closure_set(x_835, 1, x_4);
lean_closure_set(x_835, 2, x_5);
lean_closure_set(x_835, 3, x_27);
lean_closure_set(x_835, 4, x_24);
lean_closure_set(x_835, 5, x_26);
lean_closure_set(x_835, 6, x_2);
lean_closure_set(x_835, 7, x_23);
x_836 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_679, x_835, x_6, x_7, x_8, x_9, x_834);
if (lean_obj_tag(x_836) == 0)
{
uint8_t x_837; 
x_837 = !lean_is_exclusive(x_836);
if (x_837 == 0)
{
lean_object* x_838; lean_object* x_839; 
x_838 = lean_ctor_get(x_836, 0);
if (lean_is_scalar(x_22)) {
 x_839 = lean_alloc_ctor(1, 1, 0);
} else {
 x_839 = x_22;
}
lean_ctor_set(x_839, 0, x_838);
lean_ctor_set(x_836, 0, x_839);
return x_836;
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_840 = lean_ctor_get(x_836, 0);
x_841 = lean_ctor_get(x_836, 1);
lean_inc(x_841);
lean_inc(x_840);
lean_dec(x_836);
if (lean_is_scalar(x_22)) {
 x_842 = lean_alloc_ctor(1, 1, 0);
} else {
 x_842 = x_22;
}
lean_ctor_set(x_842, 0, x_840);
x_843 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_841);
return x_843;
}
}
else
{
uint8_t x_844; 
lean_dec(x_22);
x_844 = !lean_is_exclusive(x_836);
if (x_844 == 0)
{
return x_836;
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_845 = lean_ctor_get(x_836, 0);
x_846 = lean_ctor_get(x_836, 1);
lean_inc(x_846);
lean_inc(x_845);
lean_dec(x_836);
x_847 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_847, 0, x_845);
lean_ctor_set(x_847, 1, x_846);
return x_847;
}
}
}
}
else
{
uint8_t x_848; 
lean_dec(x_669);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_848 = !lean_is_exclusive(x_678);
if (x_848 == 0)
{
return x_678;
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_849 = lean_ctor_get(x_678, 0);
x_850 = lean_ctor_get(x_678, 1);
lean_inc(x_850);
lean_inc(x_849);
lean_dec(x_678);
x_851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_851, 0, x_849);
lean_ctor_set(x_851, 1, x_850);
return x_851;
}
}
}
}
else
{
uint8_t x_871; 
lean_dec(x_669);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_871 = !lean_is_exclusive(x_674);
if (x_871 == 0)
{
return x_674;
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_872 = lean_ctor_get(x_674, 0);
x_873 = lean_ctor_get(x_674, 1);
lean_inc(x_873);
lean_inc(x_872);
lean_dec(x_674);
x_874 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_874, 0, x_872);
lean_ctor_set(x_874, 1, x_873);
return x_874;
}
}
}
else
{
uint8_t x_875; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_875 = !lean_is_exclusive(x_668);
if (x_875 == 0)
{
return x_668;
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = lean_ctor_get(x_668, 0);
x_877 = lean_ctor_get(x_668, 1);
lean_inc(x_877);
lean_inc(x_876);
lean_dec(x_668);
x_878 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_878, 0, x_876);
lean_ctor_set(x_878, 1, x_877);
return x_878;
}
}
}
case 4:
{
lean_object* x_879; lean_object* x_880; 
x_879 = lean_ctor_get(x_34, 0);
lean_inc(x_879);
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_879);
x_880 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_879, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
lean_dec(x_880);
x_883 = lean_ctor_get(x_3, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_3, 1);
lean_inc(x_884);
x_885 = lean_ctor_get(x_3, 2);
lean_inc(x_885);
lean_inc(x_879);
x_886 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_886, 0, x_879);
lean_ctor_set(x_886, 1, x_885);
x_887 = lean_ctor_get(x_3, 3);
lean_inc(x_887);
lean_dec(x_3);
x_888 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_887, x_879, x_881);
x_889 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_889, 0, x_883);
lean_ctor_set(x_889, 1, x_884);
lean_ctor_set(x_889, 2, x_886);
lean_ctor_set(x_889, 3, x_888);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_890 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_882);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; uint8_t x_895; lean_object* x_896; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_890, 1);
lean_inc(x_892);
lean_dec(x_890);
x_893 = lean_ctor_get(x_21, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_21, 1);
lean_inc(x_894);
lean_dec(x_21);
x_895 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_896 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_893, x_894, x_32, x_895, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_892);
lean_dec(x_893);
if (lean_obj_tag(x_896) == 0)
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; uint8_t x_1075; 
x_897 = lean_ctor_get(x_896, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_896, 1);
lean_inc(x_898);
lean_dec(x_896);
x_1075 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1075 == 0)
{
lean_object* x_1076; 
x_1076 = lean_box(0);
x_899 = x_1076;
goto block_1074;
}
else
{
uint8_t x_1077; 
x_1077 = lean_nat_dec_eq(x_24, x_27);
if (x_1077 == 0)
{
lean_object* x_1078; 
x_1078 = lean_box(0);
x_899 = x_1078;
goto block_1074;
}
else
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
lean_dec(x_891);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_1079 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_898);
x_1080 = lean_ctor_get(x_1079, 1);
lean_inc(x_1080);
lean_dec(x_1079);
x_1081 = l_Lean_Compiler_LCNF_Simp_simp(x_897, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_1080);
if (lean_obj_tag(x_1081) == 0)
{
uint8_t x_1082; 
x_1082 = !lean_is_exclusive(x_1081);
if (x_1082 == 0)
{
lean_object* x_1083; lean_object* x_1084; 
x_1083 = lean_ctor_get(x_1081, 0);
x_1084 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1084, 0, x_1083);
lean_ctor_set(x_1081, 0, x_1084);
return x_1081;
}
else
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
x_1085 = lean_ctor_get(x_1081, 0);
x_1086 = lean_ctor_get(x_1081, 1);
lean_inc(x_1086);
lean_inc(x_1085);
lean_dec(x_1081);
x_1087 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1087, 0, x_1085);
x_1088 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1088, 0, x_1087);
lean_ctor_set(x_1088, 1, x_1086);
return x_1088;
}
}
else
{
uint8_t x_1089; 
x_1089 = !lean_is_exclusive(x_1081);
if (x_1089 == 0)
{
return x_1081;
}
else
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
x_1090 = lean_ctor_get(x_1081, 0);
x_1091 = lean_ctor_get(x_1081, 1);
lean_inc(x_1091);
lean_inc(x_1090);
lean_dec(x_1081);
x_1092 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1092, 0, x_1090);
lean_ctor_set(x_1092, 1, x_1091);
return x_1092;
}
}
}
}
block_1074:
{
lean_object* x_900; 
lean_dec(x_899);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_889);
x_900 = l_Lean_Compiler_LCNF_Simp_simp(x_897, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_898);
if (lean_obj_tag(x_900) == 0)
{
lean_object* x_901; lean_object* x_902; uint8_t x_903; 
x_901 = lean_ctor_get(x_900, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_900, 1);
lean_inc(x_902);
lean_dec(x_900);
lean_inc(x_901);
x_903 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_901);
if (x_903 == 0)
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; uint8_t x_907; 
x_904 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_902);
x_905 = lean_ctor_get(x_904, 1);
lean_inc(x_905);
lean_dec(x_904);
lean_inc(x_891);
x_906 = l_Lean_Expr_headBeta(x_891);
x_907 = l_Lean_Expr_isForall(x_906);
lean_dec(x_906);
if (x_907 == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; uint8_t x_912; lean_object* x_913; lean_object* x_914; 
x_908 = l_Lean_Compiler_LCNF_mkAuxParam(x_891, x_895, x_6, x_7, x_8, x_9, x_905);
x_909 = lean_ctor_get(x_908, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_908, 1);
lean_inc(x_910);
lean_dec(x_908);
x_911 = lean_ctor_get(x_909, 0);
lean_inc(x_911);
x_912 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_912 == 0)
{
lean_object* x_941; 
lean_dec(x_27);
lean_dec(x_23);
x_941 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_911, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_910);
if (lean_obj_tag(x_941) == 0)
{
lean_object* x_942; lean_object* x_943; 
x_942 = lean_ctor_get(x_941, 1);
lean_inc(x_942);
lean_dec(x_941);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_943 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_942);
if (lean_obj_tag(x_943) == 0)
{
lean_object* x_944; lean_object* x_945; 
x_944 = lean_ctor_get(x_943, 0);
lean_inc(x_944);
x_945 = lean_ctor_get(x_943, 1);
lean_inc(x_945);
lean_dec(x_943);
x_913 = x_944;
x_914 = x_945;
goto block_940;
}
else
{
uint8_t x_946; 
lean_dec(x_909);
lean_dec(x_901);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_946 = !lean_is_exclusive(x_943);
if (x_946 == 0)
{
return x_943;
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_947 = lean_ctor_get(x_943, 0);
x_948 = lean_ctor_get(x_943, 1);
lean_inc(x_948);
lean_inc(x_947);
lean_dec(x_943);
x_949 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_949, 0, x_947);
lean_ctor_set(x_949, 1, x_948);
return x_949;
}
}
}
else
{
uint8_t x_950; 
lean_dec(x_909);
lean_dec(x_901);
lean_dec(x_889);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_950 = !lean_is_exclusive(x_941);
if (x_950 == 0)
{
return x_941;
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; 
x_951 = lean_ctor_get(x_941, 0);
x_952 = lean_ctor_get(x_941, 1);
lean_inc(x_952);
lean_inc(x_951);
lean_dec(x_941);
x_953 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_953, 0, x_951);
lean_ctor_set(x_953, 1, x_952);
return x_953;
}
}
}
else
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_954 = l_Lean_Expr_fvar___override(x_911);
x_955 = lean_array_get_size(x_23);
x_956 = l_Array_toSubarray___rarg(x_23, x_27, x_955);
x_957 = l_Array_ofSubarray___rarg(x_956);
x_958 = l_Lean_mkAppN(x_954, x_957);
x_959 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_960 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_958, x_959, x_6, x_7, x_8, x_9, x_910);
if (lean_obj_tag(x_960) == 0)
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_961 = lean_ctor_get(x_960, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_960, 1);
lean_inc(x_962);
lean_dec(x_960);
x_963 = lean_ctor_get(x_961, 0);
lean_inc(x_963);
x_964 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_963, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_962);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; 
x_965 = lean_ctor_get(x_964, 1);
lean_inc(x_965);
lean_dec(x_964);
x_966 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_966, 0, x_961);
lean_ctor_set(x_966, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_967 = l_Lean_Compiler_LCNF_Simp_simp(x_966, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_965);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_968; lean_object* x_969; 
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_967, 1);
lean_inc(x_969);
lean_dec(x_967);
x_913 = x_968;
x_914 = x_969;
goto block_940;
}
else
{
uint8_t x_970; 
lean_dec(x_909);
lean_dec(x_901);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_970 = !lean_is_exclusive(x_967);
if (x_970 == 0)
{
return x_967;
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_971 = lean_ctor_get(x_967, 0);
x_972 = lean_ctor_get(x_967, 1);
lean_inc(x_972);
lean_inc(x_971);
lean_dec(x_967);
x_973 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_973, 0, x_971);
lean_ctor_set(x_973, 1, x_972);
return x_973;
}
}
}
else
{
uint8_t x_974; 
lean_dec(x_961);
lean_dec(x_909);
lean_dec(x_901);
lean_dec(x_889);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_974 = !lean_is_exclusive(x_964);
if (x_974 == 0)
{
return x_964;
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; 
x_975 = lean_ctor_get(x_964, 0);
x_976 = lean_ctor_get(x_964, 1);
lean_inc(x_976);
lean_inc(x_975);
lean_dec(x_964);
x_977 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_977, 0, x_975);
lean_ctor_set(x_977, 1, x_976);
return x_977;
}
}
}
else
{
uint8_t x_978; 
lean_dec(x_909);
lean_dec(x_901);
lean_dec(x_889);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_978 = !lean_is_exclusive(x_960);
if (x_978 == 0)
{
return x_960;
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; 
x_979 = lean_ctor_get(x_960, 0);
x_980 = lean_ctor_get(x_960, 1);
lean_inc(x_980);
lean_inc(x_979);
lean_dec(x_960);
x_981 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_981, 0, x_979);
lean_ctor_set(x_981, 1, x_980);
return x_981;
}
}
}
block_940:
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_915 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_916 = lean_array_push(x_915, x_909);
x_917 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_918 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_916, x_913, x_917, x_6, x_7, x_8, x_9, x_914);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_918, 1);
lean_inc(x_920);
lean_dec(x_918);
lean_inc(x_919);
x_921 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_921, 0, x_919);
lean_closure_set(x_921, 1, x_915);
x_922 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_901, x_921, x_6, x_7, x_8, x_9, x_920);
if (lean_obj_tag(x_922) == 0)
{
uint8_t x_923; 
x_923 = !lean_is_exclusive(x_922);
if (x_923 == 0)
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_924 = lean_ctor_get(x_922, 0);
x_925 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_925, 0, x_919);
lean_ctor_set(x_925, 1, x_924);
if (lean_is_scalar(x_22)) {
 x_926 = lean_alloc_ctor(1, 1, 0);
} else {
 x_926 = x_22;
}
lean_ctor_set(x_926, 0, x_925);
lean_ctor_set(x_922, 0, x_926);
return x_922;
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; 
x_927 = lean_ctor_get(x_922, 0);
x_928 = lean_ctor_get(x_922, 1);
lean_inc(x_928);
lean_inc(x_927);
lean_dec(x_922);
x_929 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_929, 0, x_919);
lean_ctor_set(x_929, 1, x_927);
if (lean_is_scalar(x_22)) {
 x_930 = lean_alloc_ctor(1, 1, 0);
} else {
 x_930 = x_22;
}
lean_ctor_set(x_930, 0, x_929);
x_931 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_931, 0, x_930);
lean_ctor_set(x_931, 1, x_928);
return x_931;
}
}
else
{
uint8_t x_932; 
lean_dec(x_919);
lean_dec(x_22);
x_932 = !lean_is_exclusive(x_922);
if (x_932 == 0)
{
return x_922;
}
else
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_933 = lean_ctor_get(x_922, 0);
x_934 = lean_ctor_get(x_922, 1);
lean_inc(x_934);
lean_inc(x_933);
lean_dec(x_922);
x_935 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_935, 0, x_933);
lean_ctor_set(x_935, 1, x_934);
return x_935;
}
}
}
else
{
uint8_t x_936; 
lean_dec(x_901);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_936 = !lean_is_exclusive(x_918);
if (x_936 == 0)
{
return x_918;
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; 
x_937 = lean_ctor_get(x_918, 0);
x_938 = lean_ctor_get(x_918, 1);
lean_inc(x_938);
lean_inc(x_937);
lean_dec(x_918);
x_939 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_939, 0, x_937);
lean_ctor_set(x_939, 1, x_938);
return x_939;
}
}
}
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_dec(x_891);
x_982 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_983 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_984 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_982, x_901, x_983, x_6, x_7, x_8, x_9, x_905);
if (lean_obj_tag(x_984) == 0)
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_985 = lean_ctor_get(x_984, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_984, 1);
lean_inc(x_986);
lean_dec(x_984);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_987 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_985, x_6, x_7, x_8, x_9, x_986);
if (lean_obj_tag(x_987) == 0)
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; uint8_t x_991; lean_object* x_992; lean_object* x_993; 
x_988 = lean_ctor_get(x_987, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_987, 1);
lean_inc(x_989);
lean_dec(x_987);
x_990 = lean_ctor_get(x_988, 0);
lean_inc(x_990);
x_991 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_991 == 0)
{
lean_object* x_1006; 
lean_dec(x_27);
lean_dec(x_23);
x_1006 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_990, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_989);
if (lean_obj_tag(x_1006) == 0)
{
lean_object* x_1007; lean_object* x_1008; 
x_1007 = lean_ctor_get(x_1006, 1);
lean_inc(x_1007);
lean_dec(x_1006);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_889);
x_1008 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_1007);
if (lean_obj_tag(x_1008) == 0)
{
lean_object* x_1009; lean_object* x_1010; 
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_1008, 1);
lean_inc(x_1010);
lean_dec(x_1008);
x_992 = x_1009;
x_993 = x_1010;
goto block_1005;
}
else
{
uint8_t x_1011; 
lean_dec(x_988);
lean_dec(x_889);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1011 = !lean_is_exclusive(x_1008);
if (x_1011 == 0)
{
return x_1008;
}
else
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
x_1012 = lean_ctor_get(x_1008, 0);
x_1013 = lean_ctor_get(x_1008, 1);
lean_inc(x_1013);
lean_inc(x_1012);
lean_dec(x_1008);
x_1014 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1014, 0, x_1012);
lean_ctor_set(x_1014, 1, x_1013);
return x_1014;
}
}
}
else
{
uint8_t x_1015; 
lean_dec(x_988);
lean_dec(x_889);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1015 = !lean_is_exclusive(x_1006);
if (x_1015 == 0)
{
return x_1006;
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
x_1016 = lean_ctor_get(x_1006, 0);
x_1017 = lean_ctor_get(x_1006, 1);
lean_inc(x_1017);
lean_inc(x_1016);
lean_dec(x_1006);
x_1018 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1018, 0, x_1016);
lean_ctor_set(x_1018, 1, x_1017);
return x_1018;
}
}
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1019 = l_Lean_Expr_fvar___override(x_990);
x_1020 = lean_array_get_size(x_23);
x_1021 = l_Array_toSubarray___rarg(x_23, x_27, x_1020);
x_1022 = l_Array_ofSubarray___rarg(x_1021);
x_1023 = l_Lean_mkAppN(x_1019, x_1022);
x_1024 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1025 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1023, x_1024, x_6, x_7, x_8, x_9, x_989);
if (lean_obj_tag(x_1025) == 0)
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1025, 1);
lean_inc(x_1027);
lean_dec(x_1025);
x_1028 = lean_ctor_get(x_1026, 0);
lean_inc(x_1028);
x_1029 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1028, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_1027);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1030 = lean_ctor_get(x_1029, 1);
lean_inc(x_1030);
lean_dec(x_1029);
x_1031 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1031, 0, x_1026);
lean_ctor_set(x_1031, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_889);
x_1032 = l_Lean_Compiler_LCNF_Simp_simp(x_1031, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_1030);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; 
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec(x_1032);
x_992 = x_1033;
x_993 = x_1034;
goto block_1005;
}
else
{
uint8_t x_1035; 
lean_dec(x_988);
lean_dec(x_889);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1035 = !lean_is_exclusive(x_1032);
if (x_1035 == 0)
{
return x_1032;
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1036 = lean_ctor_get(x_1032, 0);
x_1037 = lean_ctor_get(x_1032, 1);
lean_inc(x_1037);
lean_inc(x_1036);
lean_dec(x_1032);
x_1038 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1038, 0, x_1036);
lean_ctor_set(x_1038, 1, x_1037);
return x_1038;
}
}
}
else
{
uint8_t x_1039; 
lean_dec(x_1026);
lean_dec(x_988);
lean_dec(x_889);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1039 = !lean_is_exclusive(x_1029);
if (x_1039 == 0)
{
return x_1029;
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1040 = lean_ctor_get(x_1029, 0);
x_1041 = lean_ctor_get(x_1029, 1);
lean_inc(x_1041);
lean_inc(x_1040);
lean_dec(x_1029);
x_1042 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1042, 0, x_1040);
lean_ctor_set(x_1042, 1, x_1041);
return x_1042;
}
}
}
else
{
uint8_t x_1043; 
lean_dec(x_988);
lean_dec(x_889);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1043 = !lean_is_exclusive(x_1025);
if (x_1043 == 0)
{
return x_1025;
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
x_1044 = lean_ctor_get(x_1025, 0);
x_1045 = lean_ctor_get(x_1025, 1);
lean_inc(x_1045);
lean_inc(x_1044);
lean_dec(x_1025);
x_1046 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1046, 0, x_1044);
lean_ctor_set(x_1046, 1, x_1045);
return x_1046;
}
}
}
block_1005:
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; uint8_t x_998; 
x_994 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_994, 0, x_988);
x_995 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_996 = lean_array_push(x_995, x_994);
x_997 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_996, x_992, x_889, x_4, x_5, x_6, x_7, x_8, x_9, x_993);
lean_dec(x_996);
x_998 = !lean_is_exclusive(x_997);
if (x_998 == 0)
{
lean_object* x_999; lean_object* x_1000; 
x_999 = lean_ctor_get(x_997, 0);
if (lean_is_scalar(x_22)) {
 x_1000 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1000 = x_22;
}
lean_ctor_set(x_1000, 0, x_999);
lean_ctor_set(x_997, 0, x_1000);
return x_997;
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_1001 = lean_ctor_get(x_997, 0);
x_1002 = lean_ctor_get(x_997, 1);
lean_inc(x_1002);
lean_inc(x_1001);
lean_dec(x_997);
if (lean_is_scalar(x_22)) {
 x_1003 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1003 = x_22;
}
lean_ctor_set(x_1003, 0, x_1001);
x_1004 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1004, 0, x_1003);
lean_ctor_set(x_1004, 1, x_1002);
return x_1004;
}
}
}
else
{
uint8_t x_1047; 
lean_dec(x_889);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1047 = !lean_is_exclusive(x_987);
if (x_1047 == 0)
{
return x_987;
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
x_1048 = lean_ctor_get(x_987, 0);
x_1049 = lean_ctor_get(x_987, 1);
lean_inc(x_1049);
lean_inc(x_1048);
lean_dec(x_987);
x_1050 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1050, 0, x_1048);
lean_ctor_set(x_1050, 1, x_1049);
return x_1050;
}
}
}
else
{
uint8_t x_1051; 
lean_dec(x_889);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1051 = !lean_is_exclusive(x_984);
if (x_1051 == 0)
{
return x_984;
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
x_1052 = lean_ctor_get(x_984, 0);
x_1053 = lean_ctor_get(x_984, 1);
lean_inc(x_1053);
lean_inc(x_1052);
lean_dec(x_984);
x_1054 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1054, 0, x_1052);
lean_ctor_set(x_1054, 1, x_1053);
return x_1054;
}
}
}
}
else
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
lean_dec(x_891);
x_1055 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_902);
x_1056 = lean_ctor_get(x_1055, 1);
lean_inc(x_1056);
lean_dec(x_1055);
x_1057 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_1057, 0, x_889);
lean_closure_set(x_1057, 1, x_4);
lean_closure_set(x_1057, 2, x_5);
lean_closure_set(x_1057, 3, x_27);
lean_closure_set(x_1057, 4, x_24);
lean_closure_set(x_1057, 5, x_26);
lean_closure_set(x_1057, 6, x_2);
lean_closure_set(x_1057, 7, x_23);
x_1058 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_901, x_1057, x_6, x_7, x_8, x_9, x_1056);
if (lean_obj_tag(x_1058) == 0)
{
uint8_t x_1059; 
x_1059 = !lean_is_exclusive(x_1058);
if (x_1059 == 0)
{
lean_object* x_1060; lean_object* x_1061; 
x_1060 = lean_ctor_get(x_1058, 0);
if (lean_is_scalar(x_22)) {
 x_1061 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1061 = x_22;
}
lean_ctor_set(x_1061, 0, x_1060);
lean_ctor_set(x_1058, 0, x_1061);
return x_1058;
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1062 = lean_ctor_get(x_1058, 0);
x_1063 = lean_ctor_get(x_1058, 1);
lean_inc(x_1063);
lean_inc(x_1062);
lean_dec(x_1058);
if (lean_is_scalar(x_22)) {
 x_1064 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1064 = x_22;
}
lean_ctor_set(x_1064, 0, x_1062);
x_1065 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1065, 0, x_1064);
lean_ctor_set(x_1065, 1, x_1063);
return x_1065;
}
}
else
{
uint8_t x_1066; 
lean_dec(x_22);
x_1066 = !lean_is_exclusive(x_1058);
if (x_1066 == 0)
{
return x_1058;
}
else
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
x_1067 = lean_ctor_get(x_1058, 0);
x_1068 = lean_ctor_get(x_1058, 1);
lean_inc(x_1068);
lean_inc(x_1067);
lean_dec(x_1058);
x_1069 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1069, 0, x_1067);
lean_ctor_set(x_1069, 1, x_1068);
return x_1069;
}
}
}
}
else
{
uint8_t x_1070; 
lean_dec(x_891);
lean_dec(x_889);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1070 = !lean_is_exclusive(x_900);
if (x_1070 == 0)
{
return x_900;
}
else
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; 
x_1071 = lean_ctor_get(x_900, 0);
x_1072 = lean_ctor_get(x_900, 1);
lean_inc(x_1072);
lean_inc(x_1071);
lean_dec(x_900);
x_1073 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1073, 0, x_1071);
lean_ctor_set(x_1073, 1, x_1072);
return x_1073;
}
}
}
}
else
{
uint8_t x_1093; 
lean_dec(x_891);
lean_dec(x_889);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1093 = !lean_is_exclusive(x_896);
if (x_1093 == 0)
{
return x_896;
}
else
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1094 = lean_ctor_get(x_896, 0);
x_1095 = lean_ctor_get(x_896, 1);
lean_inc(x_1095);
lean_inc(x_1094);
lean_dec(x_896);
x_1096 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1096, 0, x_1094);
lean_ctor_set(x_1096, 1, x_1095);
return x_1096;
}
}
}
else
{
uint8_t x_1097; 
lean_dec(x_889);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1097 = !lean_is_exclusive(x_890);
if (x_1097 == 0)
{
return x_890;
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1098 = lean_ctor_get(x_890, 0);
x_1099 = lean_ctor_get(x_890, 1);
lean_inc(x_1099);
lean_inc(x_1098);
lean_dec(x_890);
x_1100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1100, 0, x_1098);
lean_ctor_set(x_1100, 1, x_1099);
return x_1100;
}
}
}
else
{
uint8_t x_1101; 
lean_dec(x_879);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1101 = !lean_is_exclusive(x_880);
if (x_1101 == 0)
{
return x_880;
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
x_1102 = lean_ctor_get(x_880, 0);
x_1103 = lean_ctor_get(x_880, 1);
lean_inc(x_1103);
lean_inc(x_1102);
lean_dec(x_880);
x_1104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1104, 0, x_1102);
lean_ctor_set(x_1104, 1, x_1103);
return x_1104;
}
}
}
case 5:
{
lean_object* x_1105; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1105 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1105) == 0)
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; uint8_t x_1110; lean_object* x_1111; 
x_1106 = lean_ctor_get(x_1105, 0);
lean_inc(x_1106);
x_1107 = lean_ctor_get(x_1105, 1);
lean_inc(x_1107);
lean_dec(x_1105);
x_1108 = lean_ctor_get(x_21, 0);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_21, 1);
lean_inc(x_1109);
lean_dec(x_21);
x_1110 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1111 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1108, x_1109, x_32, x_1110, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1107);
lean_dec(x_1108);
if (lean_obj_tag(x_1111) == 0)
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; uint8_t x_1290; 
x_1112 = lean_ctor_get(x_1111, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1111, 1);
lean_inc(x_1113);
lean_dec(x_1111);
x_1290 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1290 == 0)
{
lean_object* x_1291; 
x_1291 = lean_box(0);
x_1114 = x_1291;
goto block_1289;
}
else
{
uint8_t x_1292; 
x_1292 = lean_nat_dec_eq(x_24, x_27);
if (x_1292 == 0)
{
lean_object* x_1293; 
x_1293 = lean_box(0);
x_1114 = x_1293;
goto block_1289;
}
else
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
lean_dec(x_1106);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_1294 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1113);
x_1295 = lean_ctor_get(x_1294, 1);
lean_inc(x_1295);
lean_dec(x_1294);
x_1296 = l_Lean_Compiler_LCNF_Simp_simp(x_1112, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1295);
if (lean_obj_tag(x_1296) == 0)
{
uint8_t x_1297; 
x_1297 = !lean_is_exclusive(x_1296);
if (x_1297 == 0)
{
lean_object* x_1298; lean_object* x_1299; 
x_1298 = lean_ctor_get(x_1296, 0);
x_1299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1299, 0, x_1298);
lean_ctor_set(x_1296, 0, x_1299);
return x_1296;
}
else
{
lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1300 = lean_ctor_get(x_1296, 0);
x_1301 = lean_ctor_get(x_1296, 1);
lean_inc(x_1301);
lean_inc(x_1300);
lean_dec(x_1296);
x_1302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1302, 0, x_1300);
x_1303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1303, 0, x_1302);
lean_ctor_set(x_1303, 1, x_1301);
return x_1303;
}
}
else
{
uint8_t x_1304; 
x_1304 = !lean_is_exclusive(x_1296);
if (x_1304 == 0)
{
return x_1296;
}
else
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; 
x_1305 = lean_ctor_get(x_1296, 0);
x_1306 = lean_ctor_get(x_1296, 1);
lean_inc(x_1306);
lean_inc(x_1305);
lean_dec(x_1296);
x_1307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1307, 0, x_1305);
lean_ctor_set(x_1307, 1, x_1306);
return x_1307;
}
}
}
}
block_1289:
{
lean_object* x_1115; 
lean_dec(x_1114);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1115 = l_Lean_Compiler_LCNF_Simp_simp(x_1112, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1113);
if (lean_obj_tag(x_1115) == 0)
{
lean_object* x_1116; lean_object* x_1117; uint8_t x_1118; 
x_1116 = lean_ctor_get(x_1115, 0);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1115, 1);
lean_inc(x_1117);
lean_dec(x_1115);
lean_inc(x_1116);
x_1118 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1116);
if (x_1118 == 0)
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; uint8_t x_1122; 
x_1119 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1117);
x_1120 = lean_ctor_get(x_1119, 1);
lean_inc(x_1120);
lean_dec(x_1119);
lean_inc(x_1106);
x_1121 = l_Lean_Expr_headBeta(x_1106);
x_1122 = l_Lean_Expr_isForall(x_1121);
lean_dec(x_1121);
if (x_1122 == 0)
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; uint8_t x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1123 = l_Lean_Compiler_LCNF_mkAuxParam(x_1106, x_1110, x_6, x_7, x_8, x_9, x_1120);
x_1124 = lean_ctor_get(x_1123, 0);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1123, 1);
lean_inc(x_1125);
lean_dec(x_1123);
x_1126 = lean_ctor_get(x_1124, 0);
lean_inc(x_1126);
x_1127 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1127 == 0)
{
lean_object* x_1156; 
lean_dec(x_27);
lean_dec(x_23);
x_1156 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1126, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1125);
if (lean_obj_tag(x_1156) == 0)
{
lean_object* x_1157; lean_object* x_1158; 
x_1157 = lean_ctor_get(x_1156, 1);
lean_inc(x_1157);
lean_dec(x_1156);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1158 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1157);
if (lean_obj_tag(x_1158) == 0)
{
lean_object* x_1159; lean_object* x_1160; 
x_1159 = lean_ctor_get(x_1158, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1158, 1);
lean_inc(x_1160);
lean_dec(x_1158);
x_1128 = x_1159;
x_1129 = x_1160;
goto block_1155;
}
else
{
uint8_t x_1161; 
lean_dec(x_1124);
lean_dec(x_1116);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1161 = !lean_is_exclusive(x_1158);
if (x_1161 == 0)
{
return x_1158;
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1162 = lean_ctor_get(x_1158, 0);
x_1163 = lean_ctor_get(x_1158, 1);
lean_inc(x_1163);
lean_inc(x_1162);
lean_dec(x_1158);
x_1164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1164, 0, x_1162);
lean_ctor_set(x_1164, 1, x_1163);
return x_1164;
}
}
}
else
{
uint8_t x_1165; 
lean_dec(x_1124);
lean_dec(x_1116);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1165 = !lean_is_exclusive(x_1156);
if (x_1165 == 0)
{
return x_1156;
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1166 = lean_ctor_get(x_1156, 0);
x_1167 = lean_ctor_get(x_1156, 1);
lean_inc(x_1167);
lean_inc(x_1166);
lean_dec(x_1156);
x_1168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1168, 0, x_1166);
lean_ctor_set(x_1168, 1, x_1167);
return x_1168;
}
}
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
x_1169 = l_Lean_Expr_fvar___override(x_1126);
x_1170 = lean_array_get_size(x_23);
x_1171 = l_Array_toSubarray___rarg(x_23, x_27, x_1170);
x_1172 = l_Array_ofSubarray___rarg(x_1171);
x_1173 = l_Lean_mkAppN(x_1169, x_1172);
x_1174 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1175 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1173, x_1174, x_6, x_7, x_8, x_9, x_1125);
if (lean_obj_tag(x_1175) == 0)
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
x_1176 = lean_ctor_get(x_1175, 0);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1175, 1);
lean_inc(x_1177);
lean_dec(x_1175);
x_1178 = lean_ctor_get(x_1176, 0);
lean_inc(x_1178);
x_1179 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1178, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1177);
if (lean_obj_tag(x_1179) == 0)
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1180 = lean_ctor_get(x_1179, 1);
lean_inc(x_1180);
lean_dec(x_1179);
x_1181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1181, 0, x_1176);
lean_ctor_set(x_1181, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1182 = l_Lean_Compiler_LCNF_Simp_simp(x_1181, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1180);
if (lean_obj_tag(x_1182) == 0)
{
lean_object* x_1183; lean_object* x_1184; 
x_1183 = lean_ctor_get(x_1182, 0);
lean_inc(x_1183);
x_1184 = lean_ctor_get(x_1182, 1);
lean_inc(x_1184);
lean_dec(x_1182);
x_1128 = x_1183;
x_1129 = x_1184;
goto block_1155;
}
else
{
uint8_t x_1185; 
lean_dec(x_1124);
lean_dec(x_1116);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1185 = !lean_is_exclusive(x_1182);
if (x_1185 == 0)
{
return x_1182;
}
else
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; 
x_1186 = lean_ctor_get(x_1182, 0);
x_1187 = lean_ctor_get(x_1182, 1);
lean_inc(x_1187);
lean_inc(x_1186);
lean_dec(x_1182);
x_1188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1188, 0, x_1186);
lean_ctor_set(x_1188, 1, x_1187);
return x_1188;
}
}
}
else
{
uint8_t x_1189; 
lean_dec(x_1176);
lean_dec(x_1124);
lean_dec(x_1116);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1189 = !lean_is_exclusive(x_1179);
if (x_1189 == 0)
{
return x_1179;
}
else
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1190 = lean_ctor_get(x_1179, 0);
x_1191 = lean_ctor_get(x_1179, 1);
lean_inc(x_1191);
lean_inc(x_1190);
lean_dec(x_1179);
x_1192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1192, 0, x_1190);
lean_ctor_set(x_1192, 1, x_1191);
return x_1192;
}
}
}
else
{
uint8_t x_1193; 
lean_dec(x_1124);
lean_dec(x_1116);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1193 = !lean_is_exclusive(x_1175);
if (x_1193 == 0)
{
return x_1175;
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
x_1194 = lean_ctor_get(x_1175, 0);
x_1195 = lean_ctor_get(x_1175, 1);
lean_inc(x_1195);
lean_inc(x_1194);
lean_dec(x_1175);
x_1196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1196, 0, x_1194);
lean_ctor_set(x_1196, 1, x_1195);
return x_1196;
}
}
}
block_1155:
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; 
x_1130 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1131 = lean_array_push(x_1130, x_1124);
x_1132 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1133 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1131, x_1128, x_1132, x_6, x_7, x_8, x_9, x_1129);
if (lean_obj_tag(x_1133) == 0)
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
x_1135 = lean_ctor_get(x_1133, 1);
lean_inc(x_1135);
lean_dec(x_1133);
lean_inc(x_1134);
x_1136 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1136, 0, x_1134);
lean_closure_set(x_1136, 1, x_1130);
x_1137 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1116, x_1136, x_6, x_7, x_8, x_9, x_1135);
if (lean_obj_tag(x_1137) == 0)
{
uint8_t x_1138; 
x_1138 = !lean_is_exclusive(x_1137);
if (x_1138 == 0)
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; 
x_1139 = lean_ctor_get(x_1137, 0);
x_1140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1140, 0, x_1134);
lean_ctor_set(x_1140, 1, x_1139);
if (lean_is_scalar(x_22)) {
 x_1141 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1141 = x_22;
}
lean_ctor_set(x_1141, 0, x_1140);
lean_ctor_set(x_1137, 0, x_1141);
return x_1137;
}
else
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
x_1142 = lean_ctor_get(x_1137, 0);
x_1143 = lean_ctor_get(x_1137, 1);
lean_inc(x_1143);
lean_inc(x_1142);
lean_dec(x_1137);
x_1144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1144, 0, x_1134);
lean_ctor_set(x_1144, 1, x_1142);
if (lean_is_scalar(x_22)) {
 x_1145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1145 = x_22;
}
lean_ctor_set(x_1145, 0, x_1144);
x_1146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1146, 0, x_1145);
lean_ctor_set(x_1146, 1, x_1143);
return x_1146;
}
}
else
{
uint8_t x_1147; 
lean_dec(x_1134);
lean_dec(x_22);
x_1147 = !lean_is_exclusive(x_1137);
if (x_1147 == 0)
{
return x_1137;
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1148 = lean_ctor_get(x_1137, 0);
x_1149 = lean_ctor_get(x_1137, 1);
lean_inc(x_1149);
lean_inc(x_1148);
lean_dec(x_1137);
x_1150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1150, 0, x_1148);
lean_ctor_set(x_1150, 1, x_1149);
return x_1150;
}
}
}
else
{
uint8_t x_1151; 
lean_dec(x_1116);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1151 = !lean_is_exclusive(x_1133);
if (x_1151 == 0)
{
return x_1133;
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
x_1152 = lean_ctor_get(x_1133, 0);
x_1153 = lean_ctor_get(x_1133, 1);
lean_inc(x_1153);
lean_inc(x_1152);
lean_dec(x_1133);
x_1154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1154, 0, x_1152);
lean_ctor_set(x_1154, 1, x_1153);
return x_1154;
}
}
}
}
else
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
lean_dec(x_1106);
x_1197 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1198 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1199 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1197, x_1116, x_1198, x_6, x_7, x_8, x_9, x_1120);
if (lean_obj_tag(x_1199) == 0)
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1200 = lean_ctor_get(x_1199, 0);
lean_inc(x_1200);
x_1201 = lean_ctor_get(x_1199, 1);
lean_inc(x_1201);
lean_dec(x_1199);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1202 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1200, x_6, x_7, x_8, x_9, x_1201);
if (lean_obj_tag(x_1202) == 0)
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; uint8_t x_1206; lean_object* x_1207; lean_object* x_1208; 
x_1203 = lean_ctor_get(x_1202, 0);
lean_inc(x_1203);
x_1204 = lean_ctor_get(x_1202, 1);
lean_inc(x_1204);
lean_dec(x_1202);
x_1205 = lean_ctor_get(x_1203, 0);
lean_inc(x_1205);
x_1206 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1206 == 0)
{
lean_object* x_1221; 
lean_dec(x_27);
lean_dec(x_23);
x_1221 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1205, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1204);
if (lean_obj_tag(x_1221) == 0)
{
lean_object* x_1222; lean_object* x_1223; 
x_1222 = lean_ctor_get(x_1221, 1);
lean_inc(x_1222);
lean_dec(x_1221);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1223 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1222);
if (lean_obj_tag(x_1223) == 0)
{
lean_object* x_1224; lean_object* x_1225; 
x_1224 = lean_ctor_get(x_1223, 0);
lean_inc(x_1224);
x_1225 = lean_ctor_get(x_1223, 1);
lean_inc(x_1225);
lean_dec(x_1223);
x_1207 = x_1224;
x_1208 = x_1225;
goto block_1220;
}
else
{
uint8_t x_1226; 
lean_dec(x_1203);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1226 = !lean_is_exclusive(x_1223);
if (x_1226 == 0)
{
return x_1223;
}
else
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; 
x_1227 = lean_ctor_get(x_1223, 0);
x_1228 = lean_ctor_get(x_1223, 1);
lean_inc(x_1228);
lean_inc(x_1227);
lean_dec(x_1223);
x_1229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1229, 0, x_1227);
lean_ctor_set(x_1229, 1, x_1228);
return x_1229;
}
}
}
else
{
uint8_t x_1230; 
lean_dec(x_1203);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1230 = !lean_is_exclusive(x_1221);
if (x_1230 == 0)
{
return x_1221;
}
else
{
lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
x_1231 = lean_ctor_get(x_1221, 0);
x_1232 = lean_ctor_get(x_1221, 1);
lean_inc(x_1232);
lean_inc(x_1231);
lean_dec(x_1221);
x_1233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1233, 0, x_1231);
lean_ctor_set(x_1233, 1, x_1232);
return x_1233;
}
}
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
x_1234 = l_Lean_Expr_fvar___override(x_1205);
x_1235 = lean_array_get_size(x_23);
x_1236 = l_Array_toSubarray___rarg(x_23, x_27, x_1235);
x_1237 = l_Array_ofSubarray___rarg(x_1236);
x_1238 = l_Lean_mkAppN(x_1234, x_1237);
x_1239 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1240 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1238, x_1239, x_6, x_7, x_8, x_9, x_1204);
if (lean_obj_tag(x_1240) == 0)
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
x_1241 = lean_ctor_get(x_1240, 0);
lean_inc(x_1241);
x_1242 = lean_ctor_get(x_1240, 1);
lean_inc(x_1242);
lean_dec(x_1240);
x_1243 = lean_ctor_get(x_1241, 0);
lean_inc(x_1243);
x_1244 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1243, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1242);
if (lean_obj_tag(x_1244) == 0)
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
x_1245 = lean_ctor_get(x_1244, 1);
lean_inc(x_1245);
lean_dec(x_1244);
x_1246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1246, 0, x_1241);
lean_ctor_set(x_1246, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1247 = l_Lean_Compiler_LCNF_Simp_simp(x_1246, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1245);
if (lean_obj_tag(x_1247) == 0)
{
lean_object* x_1248; lean_object* x_1249; 
x_1248 = lean_ctor_get(x_1247, 0);
lean_inc(x_1248);
x_1249 = lean_ctor_get(x_1247, 1);
lean_inc(x_1249);
lean_dec(x_1247);
x_1207 = x_1248;
x_1208 = x_1249;
goto block_1220;
}
else
{
uint8_t x_1250; 
lean_dec(x_1203);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1250 = !lean_is_exclusive(x_1247);
if (x_1250 == 0)
{
return x_1247;
}
else
{
lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; 
x_1251 = lean_ctor_get(x_1247, 0);
x_1252 = lean_ctor_get(x_1247, 1);
lean_inc(x_1252);
lean_inc(x_1251);
lean_dec(x_1247);
x_1253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1253, 0, x_1251);
lean_ctor_set(x_1253, 1, x_1252);
return x_1253;
}
}
}
else
{
uint8_t x_1254; 
lean_dec(x_1241);
lean_dec(x_1203);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1254 = !lean_is_exclusive(x_1244);
if (x_1254 == 0)
{
return x_1244;
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
x_1255 = lean_ctor_get(x_1244, 0);
x_1256 = lean_ctor_get(x_1244, 1);
lean_inc(x_1256);
lean_inc(x_1255);
lean_dec(x_1244);
x_1257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1257, 0, x_1255);
lean_ctor_set(x_1257, 1, x_1256);
return x_1257;
}
}
}
else
{
uint8_t x_1258; 
lean_dec(x_1203);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1258 = !lean_is_exclusive(x_1240);
if (x_1258 == 0)
{
return x_1240;
}
else
{
lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1259 = lean_ctor_get(x_1240, 0);
x_1260 = lean_ctor_get(x_1240, 1);
lean_inc(x_1260);
lean_inc(x_1259);
lean_dec(x_1240);
x_1261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1261, 0, x_1259);
lean_ctor_set(x_1261, 1, x_1260);
return x_1261;
}
}
}
block_1220:
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; uint8_t x_1213; 
x_1209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1209, 0, x_1203);
x_1210 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1211 = lean_array_push(x_1210, x_1209);
x_1212 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1211, x_1207, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1208);
lean_dec(x_1211);
x_1213 = !lean_is_exclusive(x_1212);
if (x_1213 == 0)
{
lean_object* x_1214; lean_object* x_1215; 
x_1214 = lean_ctor_get(x_1212, 0);
if (lean_is_scalar(x_22)) {
 x_1215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1215 = x_22;
}
lean_ctor_set(x_1215, 0, x_1214);
lean_ctor_set(x_1212, 0, x_1215);
return x_1212;
}
else
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; 
x_1216 = lean_ctor_get(x_1212, 0);
x_1217 = lean_ctor_get(x_1212, 1);
lean_inc(x_1217);
lean_inc(x_1216);
lean_dec(x_1212);
if (lean_is_scalar(x_22)) {
 x_1218 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1218 = x_22;
}
lean_ctor_set(x_1218, 0, x_1216);
x_1219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1219, 0, x_1218);
lean_ctor_set(x_1219, 1, x_1217);
return x_1219;
}
}
}
else
{
uint8_t x_1262; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1262 = !lean_is_exclusive(x_1202);
if (x_1262 == 0)
{
return x_1202;
}
else
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; 
x_1263 = lean_ctor_get(x_1202, 0);
x_1264 = lean_ctor_get(x_1202, 1);
lean_inc(x_1264);
lean_inc(x_1263);
lean_dec(x_1202);
x_1265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1265, 0, x_1263);
lean_ctor_set(x_1265, 1, x_1264);
return x_1265;
}
}
}
else
{
uint8_t x_1266; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1266 = !lean_is_exclusive(x_1199);
if (x_1266 == 0)
{
return x_1199;
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1199, 0);
x_1268 = lean_ctor_get(x_1199, 1);
lean_inc(x_1268);
lean_inc(x_1267);
lean_dec(x_1199);
x_1269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1269, 0, x_1267);
lean_ctor_set(x_1269, 1, x_1268);
return x_1269;
}
}
}
}
else
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; 
lean_dec(x_1106);
x_1270 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1117);
x_1271 = lean_ctor_get(x_1270, 1);
lean_inc(x_1271);
lean_dec(x_1270);
x_1272 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_1272, 0, x_3);
lean_closure_set(x_1272, 1, x_4);
lean_closure_set(x_1272, 2, x_5);
lean_closure_set(x_1272, 3, x_27);
lean_closure_set(x_1272, 4, x_24);
lean_closure_set(x_1272, 5, x_26);
lean_closure_set(x_1272, 6, x_2);
lean_closure_set(x_1272, 7, x_23);
x_1273 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1116, x_1272, x_6, x_7, x_8, x_9, x_1271);
if (lean_obj_tag(x_1273) == 0)
{
uint8_t x_1274; 
x_1274 = !lean_is_exclusive(x_1273);
if (x_1274 == 0)
{
lean_object* x_1275; lean_object* x_1276; 
x_1275 = lean_ctor_get(x_1273, 0);
if (lean_is_scalar(x_22)) {
 x_1276 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1276 = x_22;
}
lean_ctor_set(x_1276, 0, x_1275);
lean_ctor_set(x_1273, 0, x_1276);
return x_1273;
}
else
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
x_1277 = lean_ctor_get(x_1273, 0);
x_1278 = lean_ctor_get(x_1273, 1);
lean_inc(x_1278);
lean_inc(x_1277);
lean_dec(x_1273);
if (lean_is_scalar(x_22)) {
 x_1279 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1279 = x_22;
}
lean_ctor_set(x_1279, 0, x_1277);
x_1280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1280, 0, x_1279);
lean_ctor_set(x_1280, 1, x_1278);
return x_1280;
}
}
else
{
uint8_t x_1281; 
lean_dec(x_22);
x_1281 = !lean_is_exclusive(x_1273);
if (x_1281 == 0)
{
return x_1273;
}
else
{
lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; 
x_1282 = lean_ctor_get(x_1273, 0);
x_1283 = lean_ctor_get(x_1273, 1);
lean_inc(x_1283);
lean_inc(x_1282);
lean_dec(x_1273);
x_1284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1284, 0, x_1282);
lean_ctor_set(x_1284, 1, x_1283);
return x_1284;
}
}
}
}
else
{
uint8_t x_1285; 
lean_dec(x_1106);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1285 = !lean_is_exclusive(x_1115);
if (x_1285 == 0)
{
return x_1115;
}
else
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
x_1286 = lean_ctor_get(x_1115, 0);
x_1287 = lean_ctor_get(x_1115, 1);
lean_inc(x_1287);
lean_inc(x_1286);
lean_dec(x_1115);
x_1288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1288, 0, x_1286);
lean_ctor_set(x_1288, 1, x_1287);
return x_1288;
}
}
}
}
else
{
uint8_t x_1308; 
lean_dec(x_1106);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1308 = !lean_is_exclusive(x_1111);
if (x_1308 == 0)
{
return x_1111;
}
else
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
x_1309 = lean_ctor_get(x_1111, 0);
x_1310 = lean_ctor_get(x_1111, 1);
lean_inc(x_1310);
lean_inc(x_1309);
lean_dec(x_1111);
x_1311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1311, 0, x_1309);
lean_ctor_set(x_1311, 1, x_1310);
return x_1311;
}
}
}
else
{
uint8_t x_1312; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1312 = !lean_is_exclusive(x_1105);
if (x_1312 == 0)
{
return x_1105;
}
else
{
lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
x_1313 = lean_ctor_get(x_1105, 0);
x_1314 = lean_ctor_get(x_1105, 1);
lean_inc(x_1314);
lean_inc(x_1313);
lean_dec(x_1105);
x_1315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1315, 0, x_1313);
lean_ctor_set(x_1315, 1, x_1314);
return x_1315;
}
}
}
case 6:
{
lean_object* x_1316; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1316 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1316) == 0)
{
lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; uint8_t x_1321; lean_object* x_1322; 
x_1317 = lean_ctor_get(x_1316, 0);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1316, 1);
lean_inc(x_1318);
lean_dec(x_1316);
x_1319 = lean_ctor_get(x_21, 0);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_21, 1);
lean_inc(x_1320);
lean_dec(x_21);
x_1321 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1322 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1319, x_1320, x_32, x_1321, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1318);
lean_dec(x_1319);
if (lean_obj_tag(x_1322) == 0)
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; uint8_t x_1501; 
x_1323 = lean_ctor_get(x_1322, 0);
lean_inc(x_1323);
x_1324 = lean_ctor_get(x_1322, 1);
lean_inc(x_1324);
lean_dec(x_1322);
x_1501 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1501 == 0)
{
lean_object* x_1502; 
x_1502 = lean_box(0);
x_1325 = x_1502;
goto block_1500;
}
else
{
uint8_t x_1503; 
x_1503 = lean_nat_dec_eq(x_24, x_27);
if (x_1503 == 0)
{
lean_object* x_1504; 
x_1504 = lean_box(0);
x_1325 = x_1504;
goto block_1500;
}
else
{
lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; 
lean_dec(x_1317);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_1505 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1324);
x_1506 = lean_ctor_get(x_1505, 1);
lean_inc(x_1506);
lean_dec(x_1505);
x_1507 = l_Lean_Compiler_LCNF_Simp_simp(x_1323, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1506);
if (lean_obj_tag(x_1507) == 0)
{
uint8_t x_1508; 
x_1508 = !lean_is_exclusive(x_1507);
if (x_1508 == 0)
{
lean_object* x_1509; lean_object* x_1510; 
x_1509 = lean_ctor_get(x_1507, 0);
x_1510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1510, 0, x_1509);
lean_ctor_set(x_1507, 0, x_1510);
return x_1507;
}
else
{
lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; 
x_1511 = lean_ctor_get(x_1507, 0);
x_1512 = lean_ctor_get(x_1507, 1);
lean_inc(x_1512);
lean_inc(x_1511);
lean_dec(x_1507);
x_1513 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1513, 0, x_1511);
x_1514 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1514, 0, x_1513);
lean_ctor_set(x_1514, 1, x_1512);
return x_1514;
}
}
else
{
uint8_t x_1515; 
x_1515 = !lean_is_exclusive(x_1507);
if (x_1515 == 0)
{
return x_1507;
}
else
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; 
x_1516 = lean_ctor_get(x_1507, 0);
x_1517 = lean_ctor_get(x_1507, 1);
lean_inc(x_1517);
lean_inc(x_1516);
lean_dec(x_1507);
x_1518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1518, 0, x_1516);
lean_ctor_set(x_1518, 1, x_1517);
return x_1518;
}
}
}
}
block_1500:
{
lean_object* x_1326; 
lean_dec(x_1325);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1326 = l_Lean_Compiler_LCNF_Simp_simp(x_1323, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1324);
if (lean_obj_tag(x_1326) == 0)
{
lean_object* x_1327; lean_object* x_1328; uint8_t x_1329; 
x_1327 = lean_ctor_get(x_1326, 0);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_1326, 1);
lean_inc(x_1328);
lean_dec(x_1326);
lean_inc(x_1327);
x_1329 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1327);
if (x_1329 == 0)
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; uint8_t x_1333; 
x_1330 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1328);
x_1331 = lean_ctor_get(x_1330, 1);
lean_inc(x_1331);
lean_dec(x_1330);
lean_inc(x_1317);
x_1332 = l_Lean_Expr_headBeta(x_1317);
x_1333 = l_Lean_Expr_isForall(x_1332);
lean_dec(x_1332);
if (x_1333 == 0)
{
lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; uint8_t x_1338; lean_object* x_1339; lean_object* x_1340; 
x_1334 = l_Lean_Compiler_LCNF_mkAuxParam(x_1317, x_1321, x_6, x_7, x_8, x_9, x_1331);
x_1335 = lean_ctor_get(x_1334, 0);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_1334, 1);
lean_inc(x_1336);
lean_dec(x_1334);
x_1337 = lean_ctor_get(x_1335, 0);
lean_inc(x_1337);
x_1338 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1338 == 0)
{
lean_object* x_1367; 
lean_dec(x_27);
lean_dec(x_23);
x_1367 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1337, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1336);
if (lean_obj_tag(x_1367) == 0)
{
lean_object* x_1368; lean_object* x_1369; 
x_1368 = lean_ctor_get(x_1367, 1);
lean_inc(x_1368);
lean_dec(x_1367);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1369 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1368);
if (lean_obj_tag(x_1369) == 0)
{
lean_object* x_1370; lean_object* x_1371; 
x_1370 = lean_ctor_get(x_1369, 0);
lean_inc(x_1370);
x_1371 = lean_ctor_get(x_1369, 1);
lean_inc(x_1371);
lean_dec(x_1369);
x_1339 = x_1370;
x_1340 = x_1371;
goto block_1366;
}
else
{
uint8_t x_1372; 
lean_dec(x_1335);
lean_dec(x_1327);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1372 = !lean_is_exclusive(x_1369);
if (x_1372 == 0)
{
return x_1369;
}
else
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
x_1373 = lean_ctor_get(x_1369, 0);
x_1374 = lean_ctor_get(x_1369, 1);
lean_inc(x_1374);
lean_inc(x_1373);
lean_dec(x_1369);
x_1375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1375, 0, x_1373);
lean_ctor_set(x_1375, 1, x_1374);
return x_1375;
}
}
}
else
{
uint8_t x_1376; 
lean_dec(x_1335);
lean_dec(x_1327);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1376 = !lean_is_exclusive(x_1367);
if (x_1376 == 0)
{
return x_1367;
}
else
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
x_1377 = lean_ctor_get(x_1367, 0);
x_1378 = lean_ctor_get(x_1367, 1);
lean_inc(x_1378);
lean_inc(x_1377);
lean_dec(x_1367);
x_1379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1379, 0, x_1377);
lean_ctor_set(x_1379, 1, x_1378);
return x_1379;
}
}
}
else
{
lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1380 = l_Lean_Expr_fvar___override(x_1337);
x_1381 = lean_array_get_size(x_23);
x_1382 = l_Array_toSubarray___rarg(x_23, x_27, x_1381);
x_1383 = l_Array_ofSubarray___rarg(x_1382);
x_1384 = l_Lean_mkAppN(x_1380, x_1383);
x_1385 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1386 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1384, x_1385, x_6, x_7, x_8, x_9, x_1336);
if (lean_obj_tag(x_1386) == 0)
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; 
x_1387 = lean_ctor_get(x_1386, 0);
lean_inc(x_1387);
x_1388 = lean_ctor_get(x_1386, 1);
lean_inc(x_1388);
lean_dec(x_1386);
x_1389 = lean_ctor_get(x_1387, 0);
lean_inc(x_1389);
x_1390 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1389, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1388);
if (lean_obj_tag(x_1390) == 0)
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
x_1391 = lean_ctor_get(x_1390, 1);
lean_inc(x_1391);
lean_dec(x_1390);
x_1392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1392, 0, x_1387);
lean_ctor_set(x_1392, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1393 = l_Lean_Compiler_LCNF_Simp_simp(x_1392, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1391);
if (lean_obj_tag(x_1393) == 0)
{
lean_object* x_1394; lean_object* x_1395; 
x_1394 = lean_ctor_get(x_1393, 0);
lean_inc(x_1394);
x_1395 = lean_ctor_get(x_1393, 1);
lean_inc(x_1395);
lean_dec(x_1393);
x_1339 = x_1394;
x_1340 = x_1395;
goto block_1366;
}
else
{
uint8_t x_1396; 
lean_dec(x_1335);
lean_dec(x_1327);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1396 = !lean_is_exclusive(x_1393);
if (x_1396 == 0)
{
return x_1393;
}
else
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
x_1397 = lean_ctor_get(x_1393, 0);
x_1398 = lean_ctor_get(x_1393, 1);
lean_inc(x_1398);
lean_inc(x_1397);
lean_dec(x_1393);
x_1399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1399, 0, x_1397);
lean_ctor_set(x_1399, 1, x_1398);
return x_1399;
}
}
}
else
{
uint8_t x_1400; 
lean_dec(x_1387);
lean_dec(x_1335);
lean_dec(x_1327);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1400 = !lean_is_exclusive(x_1390);
if (x_1400 == 0)
{
return x_1390;
}
else
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1401 = lean_ctor_get(x_1390, 0);
x_1402 = lean_ctor_get(x_1390, 1);
lean_inc(x_1402);
lean_inc(x_1401);
lean_dec(x_1390);
x_1403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1403, 0, x_1401);
lean_ctor_set(x_1403, 1, x_1402);
return x_1403;
}
}
}
else
{
uint8_t x_1404; 
lean_dec(x_1335);
lean_dec(x_1327);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1404 = !lean_is_exclusive(x_1386);
if (x_1404 == 0)
{
return x_1386;
}
else
{
lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; 
x_1405 = lean_ctor_get(x_1386, 0);
x_1406 = lean_ctor_get(x_1386, 1);
lean_inc(x_1406);
lean_inc(x_1405);
lean_dec(x_1386);
x_1407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1407, 0, x_1405);
lean_ctor_set(x_1407, 1, x_1406);
return x_1407;
}
}
}
block_1366:
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
x_1341 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1342 = lean_array_push(x_1341, x_1335);
x_1343 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1344 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1342, x_1339, x_1343, x_6, x_7, x_8, x_9, x_1340);
if (lean_obj_tag(x_1344) == 0)
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; 
x_1345 = lean_ctor_get(x_1344, 0);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_1344, 1);
lean_inc(x_1346);
lean_dec(x_1344);
lean_inc(x_1345);
x_1347 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1347, 0, x_1345);
lean_closure_set(x_1347, 1, x_1341);
x_1348 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1327, x_1347, x_6, x_7, x_8, x_9, x_1346);
if (lean_obj_tag(x_1348) == 0)
{
uint8_t x_1349; 
x_1349 = !lean_is_exclusive(x_1348);
if (x_1349 == 0)
{
lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
x_1350 = lean_ctor_get(x_1348, 0);
x_1351 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1351, 0, x_1345);
lean_ctor_set(x_1351, 1, x_1350);
if (lean_is_scalar(x_22)) {
 x_1352 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1352 = x_22;
}
lean_ctor_set(x_1352, 0, x_1351);
lean_ctor_set(x_1348, 0, x_1352);
return x_1348;
}
else
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; 
x_1353 = lean_ctor_get(x_1348, 0);
x_1354 = lean_ctor_get(x_1348, 1);
lean_inc(x_1354);
lean_inc(x_1353);
lean_dec(x_1348);
x_1355 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1355, 0, x_1345);
lean_ctor_set(x_1355, 1, x_1353);
if (lean_is_scalar(x_22)) {
 x_1356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1356 = x_22;
}
lean_ctor_set(x_1356, 0, x_1355);
x_1357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1357, 0, x_1356);
lean_ctor_set(x_1357, 1, x_1354);
return x_1357;
}
}
else
{
uint8_t x_1358; 
lean_dec(x_1345);
lean_dec(x_22);
x_1358 = !lean_is_exclusive(x_1348);
if (x_1358 == 0)
{
return x_1348;
}
else
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
x_1359 = lean_ctor_get(x_1348, 0);
x_1360 = lean_ctor_get(x_1348, 1);
lean_inc(x_1360);
lean_inc(x_1359);
lean_dec(x_1348);
x_1361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1361, 0, x_1359);
lean_ctor_set(x_1361, 1, x_1360);
return x_1361;
}
}
}
else
{
uint8_t x_1362; 
lean_dec(x_1327);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1362 = !lean_is_exclusive(x_1344);
if (x_1362 == 0)
{
return x_1344;
}
else
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
x_1363 = lean_ctor_get(x_1344, 0);
x_1364 = lean_ctor_get(x_1344, 1);
lean_inc(x_1364);
lean_inc(x_1363);
lean_dec(x_1344);
x_1365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1365, 0, x_1363);
lean_ctor_set(x_1365, 1, x_1364);
return x_1365;
}
}
}
}
else
{
lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; 
lean_dec(x_1317);
x_1408 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1409 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1410 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1408, x_1327, x_1409, x_6, x_7, x_8, x_9, x_1331);
if (lean_obj_tag(x_1410) == 0)
{
lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; 
x_1411 = lean_ctor_get(x_1410, 0);
lean_inc(x_1411);
x_1412 = lean_ctor_get(x_1410, 1);
lean_inc(x_1412);
lean_dec(x_1410);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1413 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1411, x_6, x_7, x_8, x_9, x_1412);
if (lean_obj_tag(x_1413) == 0)
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; uint8_t x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1414 = lean_ctor_get(x_1413, 0);
lean_inc(x_1414);
x_1415 = lean_ctor_get(x_1413, 1);
lean_inc(x_1415);
lean_dec(x_1413);
x_1416 = lean_ctor_get(x_1414, 0);
lean_inc(x_1416);
x_1417 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1417 == 0)
{
lean_object* x_1432; 
lean_dec(x_27);
lean_dec(x_23);
x_1432 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1416, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1415);
if (lean_obj_tag(x_1432) == 0)
{
lean_object* x_1433; lean_object* x_1434; 
x_1433 = lean_ctor_get(x_1432, 1);
lean_inc(x_1433);
lean_dec(x_1432);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1434 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1433);
if (lean_obj_tag(x_1434) == 0)
{
lean_object* x_1435; lean_object* x_1436; 
x_1435 = lean_ctor_get(x_1434, 0);
lean_inc(x_1435);
x_1436 = lean_ctor_get(x_1434, 1);
lean_inc(x_1436);
lean_dec(x_1434);
x_1418 = x_1435;
x_1419 = x_1436;
goto block_1431;
}
else
{
uint8_t x_1437; 
lean_dec(x_1414);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1437 = !lean_is_exclusive(x_1434);
if (x_1437 == 0)
{
return x_1434;
}
else
{
lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
x_1438 = lean_ctor_get(x_1434, 0);
x_1439 = lean_ctor_get(x_1434, 1);
lean_inc(x_1439);
lean_inc(x_1438);
lean_dec(x_1434);
x_1440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1440, 0, x_1438);
lean_ctor_set(x_1440, 1, x_1439);
return x_1440;
}
}
}
else
{
uint8_t x_1441; 
lean_dec(x_1414);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1441 = !lean_is_exclusive(x_1432);
if (x_1441 == 0)
{
return x_1432;
}
else
{
lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; 
x_1442 = lean_ctor_get(x_1432, 0);
x_1443 = lean_ctor_get(x_1432, 1);
lean_inc(x_1443);
lean_inc(x_1442);
lean_dec(x_1432);
x_1444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1444, 0, x_1442);
lean_ctor_set(x_1444, 1, x_1443);
return x_1444;
}
}
}
else
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
x_1445 = l_Lean_Expr_fvar___override(x_1416);
x_1446 = lean_array_get_size(x_23);
x_1447 = l_Array_toSubarray___rarg(x_23, x_27, x_1446);
x_1448 = l_Array_ofSubarray___rarg(x_1447);
x_1449 = l_Lean_mkAppN(x_1445, x_1448);
x_1450 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1451 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1449, x_1450, x_6, x_7, x_8, x_9, x_1415);
if (lean_obj_tag(x_1451) == 0)
{
lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; 
x_1452 = lean_ctor_get(x_1451, 0);
lean_inc(x_1452);
x_1453 = lean_ctor_get(x_1451, 1);
lean_inc(x_1453);
lean_dec(x_1451);
x_1454 = lean_ctor_get(x_1452, 0);
lean_inc(x_1454);
x_1455 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1454, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1453);
if (lean_obj_tag(x_1455) == 0)
{
lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
x_1456 = lean_ctor_get(x_1455, 1);
lean_inc(x_1456);
lean_dec(x_1455);
x_1457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1457, 0, x_1452);
lean_ctor_set(x_1457, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1458 = l_Lean_Compiler_LCNF_Simp_simp(x_1457, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1456);
if (lean_obj_tag(x_1458) == 0)
{
lean_object* x_1459; lean_object* x_1460; 
x_1459 = lean_ctor_get(x_1458, 0);
lean_inc(x_1459);
x_1460 = lean_ctor_get(x_1458, 1);
lean_inc(x_1460);
lean_dec(x_1458);
x_1418 = x_1459;
x_1419 = x_1460;
goto block_1431;
}
else
{
uint8_t x_1461; 
lean_dec(x_1414);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1461 = !lean_is_exclusive(x_1458);
if (x_1461 == 0)
{
return x_1458;
}
else
{
lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; 
x_1462 = lean_ctor_get(x_1458, 0);
x_1463 = lean_ctor_get(x_1458, 1);
lean_inc(x_1463);
lean_inc(x_1462);
lean_dec(x_1458);
x_1464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1464, 0, x_1462);
lean_ctor_set(x_1464, 1, x_1463);
return x_1464;
}
}
}
else
{
uint8_t x_1465; 
lean_dec(x_1452);
lean_dec(x_1414);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1465 = !lean_is_exclusive(x_1455);
if (x_1465 == 0)
{
return x_1455;
}
else
{
lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; 
x_1466 = lean_ctor_get(x_1455, 0);
x_1467 = lean_ctor_get(x_1455, 1);
lean_inc(x_1467);
lean_inc(x_1466);
lean_dec(x_1455);
x_1468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1468, 0, x_1466);
lean_ctor_set(x_1468, 1, x_1467);
return x_1468;
}
}
}
else
{
uint8_t x_1469; 
lean_dec(x_1414);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1469 = !lean_is_exclusive(x_1451);
if (x_1469 == 0)
{
return x_1451;
}
else
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; 
x_1470 = lean_ctor_get(x_1451, 0);
x_1471 = lean_ctor_get(x_1451, 1);
lean_inc(x_1471);
lean_inc(x_1470);
lean_dec(x_1451);
x_1472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1472, 0, x_1470);
lean_ctor_set(x_1472, 1, x_1471);
return x_1472;
}
}
}
block_1431:
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; uint8_t x_1424; 
x_1420 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1420, 0, x_1414);
x_1421 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1422 = lean_array_push(x_1421, x_1420);
x_1423 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1422, x_1418, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1419);
lean_dec(x_1422);
x_1424 = !lean_is_exclusive(x_1423);
if (x_1424 == 0)
{
lean_object* x_1425; lean_object* x_1426; 
x_1425 = lean_ctor_get(x_1423, 0);
if (lean_is_scalar(x_22)) {
 x_1426 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1426 = x_22;
}
lean_ctor_set(x_1426, 0, x_1425);
lean_ctor_set(x_1423, 0, x_1426);
return x_1423;
}
else
{
lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
x_1427 = lean_ctor_get(x_1423, 0);
x_1428 = lean_ctor_get(x_1423, 1);
lean_inc(x_1428);
lean_inc(x_1427);
lean_dec(x_1423);
if (lean_is_scalar(x_22)) {
 x_1429 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1429 = x_22;
}
lean_ctor_set(x_1429, 0, x_1427);
x_1430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1430, 0, x_1429);
lean_ctor_set(x_1430, 1, x_1428);
return x_1430;
}
}
}
else
{
uint8_t x_1473; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1473 = !lean_is_exclusive(x_1413);
if (x_1473 == 0)
{
return x_1413;
}
else
{
lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; 
x_1474 = lean_ctor_get(x_1413, 0);
x_1475 = lean_ctor_get(x_1413, 1);
lean_inc(x_1475);
lean_inc(x_1474);
lean_dec(x_1413);
x_1476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1476, 0, x_1474);
lean_ctor_set(x_1476, 1, x_1475);
return x_1476;
}
}
}
else
{
uint8_t x_1477; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1477 = !lean_is_exclusive(x_1410);
if (x_1477 == 0)
{
return x_1410;
}
else
{
lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; 
x_1478 = lean_ctor_get(x_1410, 0);
x_1479 = lean_ctor_get(x_1410, 1);
lean_inc(x_1479);
lean_inc(x_1478);
lean_dec(x_1410);
x_1480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1480, 0, x_1478);
lean_ctor_set(x_1480, 1, x_1479);
return x_1480;
}
}
}
}
else
{
lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; 
lean_dec(x_1317);
x_1481 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1328);
x_1482 = lean_ctor_get(x_1481, 1);
lean_inc(x_1482);
lean_dec(x_1481);
x_1483 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_1483, 0, x_3);
lean_closure_set(x_1483, 1, x_4);
lean_closure_set(x_1483, 2, x_5);
lean_closure_set(x_1483, 3, x_27);
lean_closure_set(x_1483, 4, x_24);
lean_closure_set(x_1483, 5, x_26);
lean_closure_set(x_1483, 6, x_2);
lean_closure_set(x_1483, 7, x_23);
x_1484 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1327, x_1483, x_6, x_7, x_8, x_9, x_1482);
if (lean_obj_tag(x_1484) == 0)
{
uint8_t x_1485; 
x_1485 = !lean_is_exclusive(x_1484);
if (x_1485 == 0)
{
lean_object* x_1486; lean_object* x_1487; 
x_1486 = lean_ctor_get(x_1484, 0);
if (lean_is_scalar(x_22)) {
 x_1487 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1487 = x_22;
}
lean_ctor_set(x_1487, 0, x_1486);
lean_ctor_set(x_1484, 0, x_1487);
return x_1484;
}
else
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
x_1488 = lean_ctor_get(x_1484, 0);
x_1489 = lean_ctor_get(x_1484, 1);
lean_inc(x_1489);
lean_inc(x_1488);
lean_dec(x_1484);
if (lean_is_scalar(x_22)) {
 x_1490 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1490 = x_22;
}
lean_ctor_set(x_1490, 0, x_1488);
x_1491 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1491, 0, x_1490);
lean_ctor_set(x_1491, 1, x_1489);
return x_1491;
}
}
else
{
uint8_t x_1492; 
lean_dec(x_22);
x_1492 = !lean_is_exclusive(x_1484);
if (x_1492 == 0)
{
return x_1484;
}
else
{
lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; 
x_1493 = lean_ctor_get(x_1484, 0);
x_1494 = lean_ctor_get(x_1484, 1);
lean_inc(x_1494);
lean_inc(x_1493);
lean_dec(x_1484);
x_1495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1495, 0, x_1493);
lean_ctor_set(x_1495, 1, x_1494);
return x_1495;
}
}
}
}
else
{
uint8_t x_1496; 
lean_dec(x_1317);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1496 = !lean_is_exclusive(x_1326);
if (x_1496 == 0)
{
return x_1326;
}
else
{
lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
x_1497 = lean_ctor_get(x_1326, 0);
x_1498 = lean_ctor_get(x_1326, 1);
lean_inc(x_1498);
lean_inc(x_1497);
lean_dec(x_1326);
x_1499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1499, 0, x_1497);
lean_ctor_set(x_1499, 1, x_1498);
return x_1499;
}
}
}
}
else
{
uint8_t x_1519; 
lean_dec(x_1317);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1519 = !lean_is_exclusive(x_1322);
if (x_1519 == 0)
{
return x_1322;
}
else
{
lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; 
x_1520 = lean_ctor_get(x_1322, 0);
x_1521 = lean_ctor_get(x_1322, 1);
lean_inc(x_1521);
lean_inc(x_1520);
lean_dec(x_1322);
x_1522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1522, 0, x_1520);
lean_ctor_set(x_1522, 1, x_1521);
return x_1522;
}
}
}
else
{
uint8_t x_1523; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1523 = !lean_is_exclusive(x_1316);
if (x_1523 == 0)
{
return x_1316;
}
else
{
lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; 
x_1524 = lean_ctor_get(x_1316, 0);
x_1525 = lean_ctor_get(x_1316, 1);
lean_inc(x_1525);
lean_inc(x_1524);
lean_dec(x_1316);
x_1526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1526, 0, x_1524);
lean_ctor_set(x_1526, 1, x_1525);
return x_1526;
}
}
}
case 7:
{
lean_object* x_1527; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1527 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1527) == 0)
{
lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; uint8_t x_1532; lean_object* x_1533; 
x_1528 = lean_ctor_get(x_1527, 0);
lean_inc(x_1528);
x_1529 = lean_ctor_get(x_1527, 1);
lean_inc(x_1529);
lean_dec(x_1527);
x_1530 = lean_ctor_get(x_21, 0);
lean_inc(x_1530);
x_1531 = lean_ctor_get(x_21, 1);
lean_inc(x_1531);
lean_dec(x_21);
x_1532 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1533 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1530, x_1531, x_32, x_1532, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1529);
lean_dec(x_1530);
if (lean_obj_tag(x_1533) == 0)
{
lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; uint8_t x_1712; 
x_1534 = lean_ctor_get(x_1533, 0);
lean_inc(x_1534);
x_1535 = lean_ctor_get(x_1533, 1);
lean_inc(x_1535);
lean_dec(x_1533);
x_1712 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1712 == 0)
{
lean_object* x_1713; 
x_1713 = lean_box(0);
x_1536 = x_1713;
goto block_1711;
}
else
{
uint8_t x_1714; 
x_1714 = lean_nat_dec_eq(x_24, x_27);
if (x_1714 == 0)
{
lean_object* x_1715; 
x_1715 = lean_box(0);
x_1536 = x_1715;
goto block_1711;
}
else
{
lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; 
lean_dec(x_1528);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_1716 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1535);
x_1717 = lean_ctor_get(x_1716, 1);
lean_inc(x_1717);
lean_dec(x_1716);
x_1718 = l_Lean_Compiler_LCNF_Simp_simp(x_1534, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1717);
if (lean_obj_tag(x_1718) == 0)
{
uint8_t x_1719; 
x_1719 = !lean_is_exclusive(x_1718);
if (x_1719 == 0)
{
lean_object* x_1720; lean_object* x_1721; 
x_1720 = lean_ctor_get(x_1718, 0);
x_1721 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1721, 0, x_1720);
lean_ctor_set(x_1718, 0, x_1721);
return x_1718;
}
else
{
lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; 
x_1722 = lean_ctor_get(x_1718, 0);
x_1723 = lean_ctor_get(x_1718, 1);
lean_inc(x_1723);
lean_inc(x_1722);
lean_dec(x_1718);
x_1724 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1724, 0, x_1722);
x_1725 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1725, 0, x_1724);
lean_ctor_set(x_1725, 1, x_1723);
return x_1725;
}
}
else
{
uint8_t x_1726; 
x_1726 = !lean_is_exclusive(x_1718);
if (x_1726 == 0)
{
return x_1718;
}
else
{
lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; 
x_1727 = lean_ctor_get(x_1718, 0);
x_1728 = lean_ctor_get(x_1718, 1);
lean_inc(x_1728);
lean_inc(x_1727);
lean_dec(x_1718);
x_1729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1729, 0, x_1727);
lean_ctor_set(x_1729, 1, x_1728);
return x_1729;
}
}
}
}
block_1711:
{
lean_object* x_1537; 
lean_dec(x_1536);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1537 = l_Lean_Compiler_LCNF_Simp_simp(x_1534, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1535);
if (lean_obj_tag(x_1537) == 0)
{
lean_object* x_1538; lean_object* x_1539; uint8_t x_1540; 
x_1538 = lean_ctor_get(x_1537, 0);
lean_inc(x_1538);
x_1539 = lean_ctor_get(x_1537, 1);
lean_inc(x_1539);
lean_dec(x_1537);
lean_inc(x_1538);
x_1540 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1538);
if (x_1540 == 0)
{
lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; uint8_t x_1544; 
x_1541 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1539);
x_1542 = lean_ctor_get(x_1541, 1);
lean_inc(x_1542);
lean_dec(x_1541);
lean_inc(x_1528);
x_1543 = l_Lean_Expr_headBeta(x_1528);
x_1544 = l_Lean_Expr_isForall(x_1543);
lean_dec(x_1543);
if (x_1544 == 0)
{
lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; uint8_t x_1549; lean_object* x_1550; lean_object* x_1551; 
x_1545 = l_Lean_Compiler_LCNF_mkAuxParam(x_1528, x_1532, x_6, x_7, x_8, x_9, x_1542);
x_1546 = lean_ctor_get(x_1545, 0);
lean_inc(x_1546);
x_1547 = lean_ctor_get(x_1545, 1);
lean_inc(x_1547);
lean_dec(x_1545);
x_1548 = lean_ctor_get(x_1546, 0);
lean_inc(x_1548);
x_1549 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1549 == 0)
{
lean_object* x_1578; 
lean_dec(x_27);
lean_dec(x_23);
x_1578 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1548, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1547);
if (lean_obj_tag(x_1578) == 0)
{
lean_object* x_1579; lean_object* x_1580; 
x_1579 = lean_ctor_get(x_1578, 1);
lean_inc(x_1579);
lean_dec(x_1578);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1580 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1579);
if (lean_obj_tag(x_1580) == 0)
{
lean_object* x_1581; lean_object* x_1582; 
x_1581 = lean_ctor_get(x_1580, 0);
lean_inc(x_1581);
x_1582 = lean_ctor_get(x_1580, 1);
lean_inc(x_1582);
lean_dec(x_1580);
x_1550 = x_1581;
x_1551 = x_1582;
goto block_1577;
}
else
{
uint8_t x_1583; 
lean_dec(x_1546);
lean_dec(x_1538);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1583 = !lean_is_exclusive(x_1580);
if (x_1583 == 0)
{
return x_1580;
}
else
{
lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; 
x_1584 = lean_ctor_get(x_1580, 0);
x_1585 = lean_ctor_get(x_1580, 1);
lean_inc(x_1585);
lean_inc(x_1584);
lean_dec(x_1580);
x_1586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1586, 0, x_1584);
lean_ctor_set(x_1586, 1, x_1585);
return x_1586;
}
}
}
else
{
uint8_t x_1587; 
lean_dec(x_1546);
lean_dec(x_1538);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1587 = !lean_is_exclusive(x_1578);
if (x_1587 == 0)
{
return x_1578;
}
else
{
lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; 
x_1588 = lean_ctor_get(x_1578, 0);
x_1589 = lean_ctor_get(x_1578, 1);
lean_inc(x_1589);
lean_inc(x_1588);
lean_dec(x_1578);
x_1590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1590, 0, x_1588);
lean_ctor_set(x_1590, 1, x_1589);
return x_1590;
}
}
}
else
{
lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; 
x_1591 = l_Lean_Expr_fvar___override(x_1548);
x_1592 = lean_array_get_size(x_23);
x_1593 = l_Array_toSubarray___rarg(x_23, x_27, x_1592);
x_1594 = l_Array_ofSubarray___rarg(x_1593);
x_1595 = l_Lean_mkAppN(x_1591, x_1594);
x_1596 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1597 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1595, x_1596, x_6, x_7, x_8, x_9, x_1547);
if (lean_obj_tag(x_1597) == 0)
{
lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; 
x_1598 = lean_ctor_get(x_1597, 0);
lean_inc(x_1598);
x_1599 = lean_ctor_get(x_1597, 1);
lean_inc(x_1599);
lean_dec(x_1597);
x_1600 = lean_ctor_get(x_1598, 0);
lean_inc(x_1600);
x_1601 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1600, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1599);
if (lean_obj_tag(x_1601) == 0)
{
lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; 
x_1602 = lean_ctor_get(x_1601, 1);
lean_inc(x_1602);
lean_dec(x_1601);
x_1603 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1603, 0, x_1598);
lean_ctor_set(x_1603, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1604 = l_Lean_Compiler_LCNF_Simp_simp(x_1603, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1602);
if (lean_obj_tag(x_1604) == 0)
{
lean_object* x_1605; lean_object* x_1606; 
x_1605 = lean_ctor_get(x_1604, 0);
lean_inc(x_1605);
x_1606 = lean_ctor_get(x_1604, 1);
lean_inc(x_1606);
lean_dec(x_1604);
x_1550 = x_1605;
x_1551 = x_1606;
goto block_1577;
}
else
{
uint8_t x_1607; 
lean_dec(x_1546);
lean_dec(x_1538);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1607 = !lean_is_exclusive(x_1604);
if (x_1607 == 0)
{
return x_1604;
}
else
{
lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; 
x_1608 = lean_ctor_get(x_1604, 0);
x_1609 = lean_ctor_get(x_1604, 1);
lean_inc(x_1609);
lean_inc(x_1608);
lean_dec(x_1604);
x_1610 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1610, 0, x_1608);
lean_ctor_set(x_1610, 1, x_1609);
return x_1610;
}
}
}
else
{
uint8_t x_1611; 
lean_dec(x_1598);
lean_dec(x_1546);
lean_dec(x_1538);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1611 = !lean_is_exclusive(x_1601);
if (x_1611 == 0)
{
return x_1601;
}
else
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; 
x_1612 = lean_ctor_get(x_1601, 0);
x_1613 = lean_ctor_get(x_1601, 1);
lean_inc(x_1613);
lean_inc(x_1612);
lean_dec(x_1601);
x_1614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1614, 0, x_1612);
lean_ctor_set(x_1614, 1, x_1613);
return x_1614;
}
}
}
else
{
uint8_t x_1615; 
lean_dec(x_1546);
lean_dec(x_1538);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1615 = !lean_is_exclusive(x_1597);
if (x_1615 == 0)
{
return x_1597;
}
else
{
lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; 
x_1616 = lean_ctor_get(x_1597, 0);
x_1617 = lean_ctor_get(x_1597, 1);
lean_inc(x_1617);
lean_inc(x_1616);
lean_dec(x_1597);
x_1618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1618, 0, x_1616);
lean_ctor_set(x_1618, 1, x_1617);
return x_1618;
}
}
}
block_1577:
{
lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; 
x_1552 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1553 = lean_array_push(x_1552, x_1546);
x_1554 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1555 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1553, x_1550, x_1554, x_6, x_7, x_8, x_9, x_1551);
if (lean_obj_tag(x_1555) == 0)
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; 
x_1556 = lean_ctor_get(x_1555, 0);
lean_inc(x_1556);
x_1557 = lean_ctor_get(x_1555, 1);
lean_inc(x_1557);
lean_dec(x_1555);
lean_inc(x_1556);
x_1558 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1558, 0, x_1556);
lean_closure_set(x_1558, 1, x_1552);
x_1559 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1538, x_1558, x_6, x_7, x_8, x_9, x_1557);
if (lean_obj_tag(x_1559) == 0)
{
uint8_t x_1560; 
x_1560 = !lean_is_exclusive(x_1559);
if (x_1560 == 0)
{
lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; 
x_1561 = lean_ctor_get(x_1559, 0);
x_1562 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1562, 0, x_1556);
lean_ctor_set(x_1562, 1, x_1561);
if (lean_is_scalar(x_22)) {
 x_1563 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1563 = x_22;
}
lean_ctor_set(x_1563, 0, x_1562);
lean_ctor_set(x_1559, 0, x_1563);
return x_1559;
}
else
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; 
x_1564 = lean_ctor_get(x_1559, 0);
x_1565 = lean_ctor_get(x_1559, 1);
lean_inc(x_1565);
lean_inc(x_1564);
lean_dec(x_1559);
x_1566 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1566, 0, x_1556);
lean_ctor_set(x_1566, 1, x_1564);
if (lean_is_scalar(x_22)) {
 x_1567 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1567 = x_22;
}
lean_ctor_set(x_1567, 0, x_1566);
x_1568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1568, 0, x_1567);
lean_ctor_set(x_1568, 1, x_1565);
return x_1568;
}
}
else
{
uint8_t x_1569; 
lean_dec(x_1556);
lean_dec(x_22);
x_1569 = !lean_is_exclusive(x_1559);
if (x_1569 == 0)
{
return x_1559;
}
else
{
lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; 
x_1570 = lean_ctor_get(x_1559, 0);
x_1571 = lean_ctor_get(x_1559, 1);
lean_inc(x_1571);
lean_inc(x_1570);
lean_dec(x_1559);
x_1572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1572, 0, x_1570);
lean_ctor_set(x_1572, 1, x_1571);
return x_1572;
}
}
}
else
{
uint8_t x_1573; 
lean_dec(x_1538);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1573 = !lean_is_exclusive(x_1555);
if (x_1573 == 0)
{
return x_1555;
}
else
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; 
x_1574 = lean_ctor_get(x_1555, 0);
x_1575 = lean_ctor_get(x_1555, 1);
lean_inc(x_1575);
lean_inc(x_1574);
lean_dec(x_1555);
x_1576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1576, 0, x_1574);
lean_ctor_set(x_1576, 1, x_1575);
return x_1576;
}
}
}
}
else
{
lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; 
lean_dec(x_1528);
x_1619 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1620 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1621 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1619, x_1538, x_1620, x_6, x_7, x_8, x_9, x_1542);
if (lean_obj_tag(x_1621) == 0)
{
lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; 
x_1622 = lean_ctor_get(x_1621, 0);
lean_inc(x_1622);
x_1623 = lean_ctor_get(x_1621, 1);
lean_inc(x_1623);
lean_dec(x_1621);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1624 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1622, x_6, x_7, x_8, x_9, x_1623);
if (lean_obj_tag(x_1624) == 0)
{
lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; uint8_t x_1628; lean_object* x_1629; lean_object* x_1630; 
x_1625 = lean_ctor_get(x_1624, 0);
lean_inc(x_1625);
x_1626 = lean_ctor_get(x_1624, 1);
lean_inc(x_1626);
lean_dec(x_1624);
x_1627 = lean_ctor_get(x_1625, 0);
lean_inc(x_1627);
x_1628 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1628 == 0)
{
lean_object* x_1643; 
lean_dec(x_27);
lean_dec(x_23);
x_1643 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1627, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1626);
if (lean_obj_tag(x_1643) == 0)
{
lean_object* x_1644; lean_object* x_1645; 
x_1644 = lean_ctor_get(x_1643, 1);
lean_inc(x_1644);
lean_dec(x_1643);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1645 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1644);
if (lean_obj_tag(x_1645) == 0)
{
lean_object* x_1646; lean_object* x_1647; 
x_1646 = lean_ctor_get(x_1645, 0);
lean_inc(x_1646);
x_1647 = lean_ctor_get(x_1645, 1);
lean_inc(x_1647);
lean_dec(x_1645);
x_1629 = x_1646;
x_1630 = x_1647;
goto block_1642;
}
else
{
uint8_t x_1648; 
lean_dec(x_1625);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1648 = !lean_is_exclusive(x_1645);
if (x_1648 == 0)
{
return x_1645;
}
else
{
lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; 
x_1649 = lean_ctor_get(x_1645, 0);
x_1650 = lean_ctor_get(x_1645, 1);
lean_inc(x_1650);
lean_inc(x_1649);
lean_dec(x_1645);
x_1651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1651, 0, x_1649);
lean_ctor_set(x_1651, 1, x_1650);
return x_1651;
}
}
}
else
{
uint8_t x_1652; 
lean_dec(x_1625);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1652 = !lean_is_exclusive(x_1643);
if (x_1652 == 0)
{
return x_1643;
}
else
{
lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; 
x_1653 = lean_ctor_get(x_1643, 0);
x_1654 = lean_ctor_get(x_1643, 1);
lean_inc(x_1654);
lean_inc(x_1653);
lean_dec(x_1643);
x_1655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1655, 0, x_1653);
lean_ctor_set(x_1655, 1, x_1654);
return x_1655;
}
}
}
else
{
lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; 
x_1656 = l_Lean_Expr_fvar___override(x_1627);
x_1657 = lean_array_get_size(x_23);
x_1658 = l_Array_toSubarray___rarg(x_23, x_27, x_1657);
x_1659 = l_Array_ofSubarray___rarg(x_1658);
x_1660 = l_Lean_mkAppN(x_1656, x_1659);
x_1661 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1662 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1660, x_1661, x_6, x_7, x_8, x_9, x_1626);
if (lean_obj_tag(x_1662) == 0)
{
lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; 
x_1663 = lean_ctor_get(x_1662, 0);
lean_inc(x_1663);
x_1664 = lean_ctor_get(x_1662, 1);
lean_inc(x_1664);
lean_dec(x_1662);
x_1665 = lean_ctor_get(x_1663, 0);
lean_inc(x_1665);
x_1666 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1665, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1664);
if (lean_obj_tag(x_1666) == 0)
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; 
x_1667 = lean_ctor_get(x_1666, 1);
lean_inc(x_1667);
lean_dec(x_1666);
x_1668 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1668, 0, x_1663);
lean_ctor_set(x_1668, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1669 = l_Lean_Compiler_LCNF_Simp_simp(x_1668, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1667);
if (lean_obj_tag(x_1669) == 0)
{
lean_object* x_1670; lean_object* x_1671; 
x_1670 = lean_ctor_get(x_1669, 0);
lean_inc(x_1670);
x_1671 = lean_ctor_get(x_1669, 1);
lean_inc(x_1671);
lean_dec(x_1669);
x_1629 = x_1670;
x_1630 = x_1671;
goto block_1642;
}
else
{
uint8_t x_1672; 
lean_dec(x_1625);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1672 = !lean_is_exclusive(x_1669);
if (x_1672 == 0)
{
return x_1669;
}
else
{
lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; 
x_1673 = lean_ctor_get(x_1669, 0);
x_1674 = lean_ctor_get(x_1669, 1);
lean_inc(x_1674);
lean_inc(x_1673);
lean_dec(x_1669);
x_1675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1675, 0, x_1673);
lean_ctor_set(x_1675, 1, x_1674);
return x_1675;
}
}
}
else
{
uint8_t x_1676; 
lean_dec(x_1663);
lean_dec(x_1625);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1676 = !lean_is_exclusive(x_1666);
if (x_1676 == 0)
{
return x_1666;
}
else
{
lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; 
x_1677 = lean_ctor_get(x_1666, 0);
x_1678 = lean_ctor_get(x_1666, 1);
lean_inc(x_1678);
lean_inc(x_1677);
lean_dec(x_1666);
x_1679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1679, 0, x_1677);
lean_ctor_set(x_1679, 1, x_1678);
return x_1679;
}
}
}
else
{
uint8_t x_1680; 
lean_dec(x_1625);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1680 = !lean_is_exclusive(x_1662);
if (x_1680 == 0)
{
return x_1662;
}
else
{
lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; 
x_1681 = lean_ctor_get(x_1662, 0);
x_1682 = lean_ctor_get(x_1662, 1);
lean_inc(x_1682);
lean_inc(x_1681);
lean_dec(x_1662);
x_1683 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1683, 0, x_1681);
lean_ctor_set(x_1683, 1, x_1682);
return x_1683;
}
}
}
block_1642:
{
lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; uint8_t x_1635; 
x_1631 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1631, 0, x_1625);
x_1632 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1633 = lean_array_push(x_1632, x_1631);
x_1634 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1633, x_1629, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1630);
lean_dec(x_1633);
x_1635 = !lean_is_exclusive(x_1634);
if (x_1635 == 0)
{
lean_object* x_1636; lean_object* x_1637; 
x_1636 = lean_ctor_get(x_1634, 0);
if (lean_is_scalar(x_22)) {
 x_1637 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1637 = x_22;
}
lean_ctor_set(x_1637, 0, x_1636);
lean_ctor_set(x_1634, 0, x_1637);
return x_1634;
}
else
{
lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; 
x_1638 = lean_ctor_get(x_1634, 0);
x_1639 = lean_ctor_get(x_1634, 1);
lean_inc(x_1639);
lean_inc(x_1638);
lean_dec(x_1634);
if (lean_is_scalar(x_22)) {
 x_1640 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1640 = x_22;
}
lean_ctor_set(x_1640, 0, x_1638);
x_1641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1641, 0, x_1640);
lean_ctor_set(x_1641, 1, x_1639);
return x_1641;
}
}
}
else
{
uint8_t x_1684; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1684 = !lean_is_exclusive(x_1624);
if (x_1684 == 0)
{
return x_1624;
}
else
{
lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; 
x_1685 = lean_ctor_get(x_1624, 0);
x_1686 = lean_ctor_get(x_1624, 1);
lean_inc(x_1686);
lean_inc(x_1685);
lean_dec(x_1624);
x_1687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1687, 0, x_1685);
lean_ctor_set(x_1687, 1, x_1686);
return x_1687;
}
}
}
else
{
uint8_t x_1688; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1688 = !lean_is_exclusive(x_1621);
if (x_1688 == 0)
{
return x_1621;
}
else
{
lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; 
x_1689 = lean_ctor_get(x_1621, 0);
x_1690 = lean_ctor_get(x_1621, 1);
lean_inc(x_1690);
lean_inc(x_1689);
lean_dec(x_1621);
x_1691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1691, 0, x_1689);
lean_ctor_set(x_1691, 1, x_1690);
return x_1691;
}
}
}
}
else
{
lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; 
lean_dec(x_1528);
x_1692 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1539);
x_1693 = lean_ctor_get(x_1692, 1);
lean_inc(x_1693);
lean_dec(x_1692);
x_1694 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_1694, 0, x_3);
lean_closure_set(x_1694, 1, x_4);
lean_closure_set(x_1694, 2, x_5);
lean_closure_set(x_1694, 3, x_27);
lean_closure_set(x_1694, 4, x_24);
lean_closure_set(x_1694, 5, x_26);
lean_closure_set(x_1694, 6, x_2);
lean_closure_set(x_1694, 7, x_23);
x_1695 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1538, x_1694, x_6, x_7, x_8, x_9, x_1693);
if (lean_obj_tag(x_1695) == 0)
{
uint8_t x_1696; 
x_1696 = !lean_is_exclusive(x_1695);
if (x_1696 == 0)
{
lean_object* x_1697; lean_object* x_1698; 
x_1697 = lean_ctor_get(x_1695, 0);
if (lean_is_scalar(x_22)) {
 x_1698 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1698 = x_22;
}
lean_ctor_set(x_1698, 0, x_1697);
lean_ctor_set(x_1695, 0, x_1698);
return x_1695;
}
else
{
lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; 
x_1699 = lean_ctor_get(x_1695, 0);
x_1700 = lean_ctor_get(x_1695, 1);
lean_inc(x_1700);
lean_inc(x_1699);
lean_dec(x_1695);
if (lean_is_scalar(x_22)) {
 x_1701 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1701 = x_22;
}
lean_ctor_set(x_1701, 0, x_1699);
x_1702 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1702, 0, x_1701);
lean_ctor_set(x_1702, 1, x_1700);
return x_1702;
}
}
else
{
uint8_t x_1703; 
lean_dec(x_22);
x_1703 = !lean_is_exclusive(x_1695);
if (x_1703 == 0)
{
return x_1695;
}
else
{
lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; 
x_1704 = lean_ctor_get(x_1695, 0);
x_1705 = lean_ctor_get(x_1695, 1);
lean_inc(x_1705);
lean_inc(x_1704);
lean_dec(x_1695);
x_1706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1706, 0, x_1704);
lean_ctor_set(x_1706, 1, x_1705);
return x_1706;
}
}
}
}
else
{
uint8_t x_1707; 
lean_dec(x_1528);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1707 = !lean_is_exclusive(x_1537);
if (x_1707 == 0)
{
return x_1537;
}
else
{
lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; 
x_1708 = lean_ctor_get(x_1537, 0);
x_1709 = lean_ctor_get(x_1537, 1);
lean_inc(x_1709);
lean_inc(x_1708);
lean_dec(x_1537);
x_1710 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1710, 0, x_1708);
lean_ctor_set(x_1710, 1, x_1709);
return x_1710;
}
}
}
}
else
{
uint8_t x_1730; 
lean_dec(x_1528);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1730 = !lean_is_exclusive(x_1533);
if (x_1730 == 0)
{
return x_1533;
}
else
{
lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; 
x_1731 = lean_ctor_get(x_1533, 0);
x_1732 = lean_ctor_get(x_1533, 1);
lean_inc(x_1732);
lean_inc(x_1731);
lean_dec(x_1533);
x_1733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1733, 0, x_1731);
lean_ctor_set(x_1733, 1, x_1732);
return x_1733;
}
}
}
else
{
uint8_t x_1734; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1734 = !lean_is_exclusive(x_1527);
if (x_1734 == 0)
{
return x_1527;
}
else
{
lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; 
x_1735 = lean_ctor_get(x_1527, 0);
x_1736 = lean_ctor_get(x_1527, 1);
lean_inc(x_1736);
lean_inc(x_1735);
lean_dec(x_1527);
x_1737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1737, 0, x_1735);
lean_ctor_set(x_1737, 1, x_1736);
return x_1737;
}
}
}
case 8:
{
lean_object* x_1738; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1738 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1738) == 0)
{
lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; uint8_t x_1743; lean_object* x_1744; 
x_1739 = lean_ctor_get(x_1738, 0);
lean_inc(x_1739);
x_1740 = lean_ctor_get(x_1738, 1);
lean_inc(x_1740);
lean_dec(x_1738);
x_1741 = lean_ctor_get(x_21, 0);
lean_inc(x_1741);
x_1742 = lean_ctor_get(x_21, 1);
lean_inc(x_1742);
lean_dec(x_21);
x_1743 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1744 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1741, x_1742, x_32, x_1743, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1740);
lean_dec(x_1741);
if (lean_obj_tag(x_1744) == 0)
{
lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; uint8_t x_1923; 
x_1745 = lean_ctor_get(x_1744, 0);
lean_inc(x_1745);
x_1746 = lean_ctor_get(x_1744, 1);
lean_inc(x_1746);
lean_dec(x_1744);
x_1923 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1923 == 0)
{
lean_object* x_1924; 
x_1924 = lean_box(0);
x_1747 = x_1924;
goto block_1922;
}
else
{
uint8_t x_1925; 
x_1925 = lean_nat_dec_eq(x_24, x_27);
if (x_1925 == 0)
{
lean_object* x_1926; 
x_1926 = lean_box(0);
x_1747 = x_1926;
goto block_1922;
}
else
{
lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; 
lean_dec(x_1739);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_1927 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1746);
x_1928 = lean_ctor_get(x_1927, 1);
lean_inc(x_1928);
lean_dec(x_1927);
x_1929 = l_Lean_Compiler_LCNF_Simp_simp(x_1745, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1928);
if (lean_obj_tag(x_1929) == 0)
{
uint8_t x_1930; 
x_1930 = !lean_is_exclusive(x_1929);
if (x_1930 == 0)
{
lean_object* x_1931; lean_object* x_1932; 
x_1931 = lean_ctor_get(x_1929, 0);
x_1932 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1932, 0, x_1931);
lean_ctor_set(x_1929, 0, x_1932);
return x_1929;
}
else
{
lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; 
x_1933 = lean_ctor_get(x_1929, 0);
x_1934 = lean_ctor_get(x_1929, 1);
lean_inc(x_1934);
lean_inc(x_1933);
lean_dec(x_1929);
x_1935 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1935, 0, x_1933);
x_1936 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1936, 0, x_1935);
lean_ctor_set(x_1936, 1, x_1934);
return x_1936;
}
}
else
{
uint8_t x_1937; 
x_1937 = !lean_is_exclusive(x_1929);
if (x_1937 == 0)
{
return x_1929;
}
else
{
lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; 
x_1938 = lean_ctor_get(x_1929, 0);
x_1939 = lean_ctor_get(x_1929, 1);
lean_inc(x_1939);
lean_inc(x_1938);
lean_dec(x_1929);
x_1940 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1940, 0, x_1938);
lean_ctor_set(x_1940, 1, x_1939);
return x_1940;
}
}
}
}
block_1922:
{
lean_object* x_1748; 
lean_dec(x_1747);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1748 = l_Lean_Compiler_LCNF_Simp_simp(x_1745, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1746);
if (lean_obj_tag(x_1748) == 0)
{
lean_object* x_1749; lean_object* x_1750; uint8_t x_1751; 
x_1749 = lean_ctor_get(x_1748, 0);
lean_inc(x_1749);
x_1750 = lean_ctor_get(x_1748, 1);
lean_inc(x_1750);
lean_dec(x_1748);
lean_inc(x_1749);
x_1751 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1749);
if (x_1751 == 0)
{
lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; uint8_t x_1755; 
x_1752 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1750);
x_1753 = lean_ctor_get(x_1752, 1);
lean_inc(x_1753);
lean_dec(x_1752);
lean_inc(x_1739);
x_1754 = l_Lean_Expr_headBeta(x_1739);
x_1755 = l_Lean_Expr_isForall(x_1754);
lean_dec(x_1754);
if (x_1755 == 0)
{
lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; uint8_t x_1760; lean_object* x_1761; lean_object* x_1762; 
x_1756 = l_Lean_Compiler_LCNF_mkAuxParam(x_1739, x_1743, x_6, x_7, x_8, x_9, x_1753);
x_1757 = lean_ctor_get(x_1756, 0);
lean_inc(x_1757);
x_1758 = lean_ctor_get(x_1756, 1);
lean_inc(x_1758);
lean_dec(x_1756);
x_1759 = lean_ctor_get(x_1757, 0);
lean_inc(x_1759);
x_1760 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1760 == 0)
{
lean_object* x_1789; 
lean_dec(x_27);
lean_dec(x_23);
x_1789 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1759, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1758);
if (lean_obj_tag(x_1789) == 0)
{
lean_object* x_1790; lean_object* x_1791; 
x_1790 = lean_ctor_get(x_1789, 1);
lean_inc(x_1790);
lean_dec(x_1789);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1791 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1790);
if (lean_obj_tag(x_1791) == 0)
{
lean_object* x_1792; lean_object* x_1793; 
x_1792 = lean_ctor_get(x_1791, 0);
lean_inc(x_1792);
x_1793 = lean_ctor_get(x_1791, 1);
lean_inc(x_1793);
lean_dec(x_1791);
x_1761 = x_1792;
x_1762 = x_1793;
goto block_1788;
}
else
{
uint8_t x_1794; 
lean_dec(x_1757);
lean_dec(x_1749);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1794 = !lean_is_exclusive(x_1791);
if (x_1794 == 0)
{
return x_1791;
}
else
{
lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; 
x_1795 = lean_ctor_get(x_1791, 0);
x_1796 = lean_ctor_get(x_1791, 1);
lean_inc(x_1796);
lean_inc(x_1795);
lean_dec(x_1791);
x_1797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1797, 0, x_1795);
lean_ctor_set(x_1797, 1, x_1796);
return x_1797;
}
}
}
else
{
uint8_t x_1798; 
lean_dec(x_1757);
lean_dec(x_1749);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1798 = !lean_is_exclusive(x_1789);
if (x_1798 == 0)
{
return x_1789;
}
else
{
lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; 
x_1799 = lean_ctor_get(x_1789, 0);
x_1800 = lean_ctor_get(x_1789, 1);
lean_inc(x_1800);
lean_inc(x_1799);
lean_dec(x_1789);
x_1801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1801, 0, x_1799);
lean_ctor_set(x_1801, 1, x_1800);
return x_1801;
}
}
}
else
{
lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; 
x_1802 = l_Lean_Expr_fvar___override(x_1759);
x_1803 = lean_array_get_size(x_23);
x_1804 = l_Array_toSubarray___rarg(x_23, x_27, x_1803);
x_1805 = l_Array_ofSubarray___rarg(x_1804);
x_1806 = l_Lean_mkAppN(x_1802, x_1805);
x_1807 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1808 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1806, x_1807, x_6, x_7, x_8, x_9, x_1758);
if (lean_obj_tag(x_1808) == 0)
{
lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; 
x_1809 = lean_ctor_get(x_1808, 0);
lean_inc(x_1809);
x_1810 = lean_ctor_get(x_1808, 1);
lean_inc(x_1810);
lean_dec(x_1808);
x_1811 = lean_ctor_get(x_1809, 0);
lean_inc(x_1811);
x_1812 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1811, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1810);
if (lean_obj_tag(x_1812) == 0)
{
lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; 
x_1813 = lean_ctor_get(x_1812, 1);
lean_inc(x_1813);
lean_dec(x_1812);
x_1814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1814, 0, x_1809);
lean_ctor_set(x_1814, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1815 = l_Lean_Compiler_LCNF_Simp_simp(x_1814, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1813);
if (lean_obj_tag(x_1815) == 0)
{
lean_object* x_1816; lean_object* x_1817; 
x_1816 = lean_ctor_get(x_1815, 0);
lean_inc(x_1816);
x_1817 = lean_ctor_get(x_1815, 1);
lean_inc(x_1817);
lean_dec(x_1815);
x_1761 = x_1816;
x_1762 = x_1817;
goto block_1788;
}
else
{
uint8_t x_1818; 
lean_dec(x_1757);
lean_dec(x_1749);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1818 = !lean_is_exclusive(x_1815);
if (x_1818 == 0)
{
return x_1815;
}
else
{
lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; 
x_1819 = lean_ctor_get(x_1815, 0);
x_1820 = lean_ctor_get(x_1815, 1);
lean_inc(x_1820);
lean_inc(x_1819);
lean_dec(x_1815);
x_1821 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1821, 0, x_1819);
lean_ctor_set(x_1821, 1, x_1820);
return x_1821;
}
}
}
else
{
uint8_t x_1822; 
lean_dec(x_1809);
lean_dec(x_1757);
lean_dec(x_1749);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1822 = !lean_is_exclusive(x_1812);
if (x_1822 == 0)
{
return x_1812;
}
else
{
lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; 
x_1823 = lean_ctor_get(x_1812, 0);
x_1824 = lean_ctor_get(x_1812, 1);
lean_inc(x_1824);
lean_inc(x_1823);
lean_dec(x_1812);
x_1825 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1825, 0, x_1823);
lean_ctor_set(x_1825, 1, x_1824);
return x_1825;
}
}
}
else
{
uint8_t x_1826; 
lean_dec(x_1757);
lean_dec(x_1749);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1826 = !lean_is_exclusive(x_1808);
if (x_1826 == 0)
{
return x_1808;
}
else
{
lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; 
x_1827 = lean_ctor_get(x_1808, 0);
x_1828 = lean_ctor_get(x_1808, 1);
lean_inc(x_1828);
lean_inc(x_1827);
lean_dec(x_1808);
x_1829 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1829, 0, x_1827);
lean_ctor_set(x_1829, 1, x_1828);
return x_1829;
}
}
}
block_1788:
{
lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; 
x_1763 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1764 = lean_array_push(x_1763, x_1757);
x_1765 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1766 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1764, x_1761, x_1765, x_6, x_7, x_8, x_9, x_1762);
if (lean_obj_tag(x_1766) == 0)
{
lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; 
x_1767 = lean_ctor_get(x_1766, 0);
lean_inc(x_1767);
x_1768 = lean_ctor_get(x_1766, 1);
lean_inc(x_1768);
lean_dec(x_1766);
lean_inc(x_1767);
x_1769 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1769, 0, x_1767);
lean_closure_set(x_1769, 1, x_1763);
x_1770 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1749, x_1769, x_6, x_7, x_8, x_9, x_1768);
if (lean_obj_tag(x_1770) == 0)
{
uint8_t x_1771; 
x_1771 = !lean_is_exclusive(x_1770);
if (x_1771 == 0)
{
lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; 
x_1772 = lean_ctor_get(x_1770, 0);
x_1773 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1773, 0, x_1767);
lean_ctor_set(x_1773, 1, x_1772);
if (lean_is_scalar(x_22)) {
 x_1774 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1774 = x_22;
}
lean_ctor_set(x_1774, 0, x_1773);
lean_ctor_set(x_1770, 0, x_1774);
return x_1770;
}
else
{
lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; 
x_1775 = lean_ctor_get(x_1770, 0);
x_1776 = lean_ctor_get(x_1770, 1);
lean_inc(x_1776);
lean_inc(x_1775);
lean_dec(x_1770);
x_1777 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1777, 0, x_1767);
lean_ctor_set(x_1777, 1, x_1775);
if (lean_is_scalar(x_22)) {
 x_1778 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1778 = x_22;
}
lean_ctor_set(x_1778, 0, x_1777);
x_1779 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1779, 0, x_1778);
lean_ctor_set(x_1779, 1, x_1776);
return x_1779;
}
}
else
{
uint8_t x_1780; 
lean_dec(x_1767);
lean_dec(x_22);
x_1780 = !lean_is_exclusive(x_1770);
if (x_1780 == 0)
{
return x_1770;
}
else
{
lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; 
x_1781 = lean_ctor_get(x_1770, 0);
x_1782 = lean_ctor_get(x_1770, 1);
lean_inc(x_1782);
lean_inc(x_1781);
lean_dec(x_1770);
x_1783 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1783, 0, x_1781);
lean_ctor_set(x_1783, 1, x_1782);
return x_1783;
}
}
}
else
{
uint8_t x_1784; 
lean_dec(x_1749);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1784 = !lean_is_exclusive(x_1766);
if (x_1784 == 0)
{
return x_1766;
}
else
{
lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; 
x_1785 = lean_ctor_get(x_1766, 0);
x_1786 = lean_ctor_get(x_1766, 1);
lean_inc(x_1786);
lean_inc(x_1785);
lean_dec(x_1766);
x_1787 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1787, 0, x_1785);
lean_ctor_set(x_1787, 1, x_1786);
return x_1787;
}
}
}
}
else
{
lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; 
lean_dec(x_1739);
x_1830 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1831 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1832 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1830, x_1749, x_1831, x_6, x_7, x_8, x_9, x_1753);
if (lean_obj_tag(x_1832) == 0)
{
lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; 
x_1833 = lean_ctor_get(x_1832, 0);
lean_inc(x_1833);
x_1834 = lean_ctor_get(x_1832, 1);
lean_inc(x_1834);
lean_dec(x_1832);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1835 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1833, x_6, x_7, x_8, x_9, x_1834);
if (lean_obj_tag(x_1835) == 0)
{
lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; uint8_t x_1839; lean_object* x_1840; lean_object* x_1841; 
x_1836 = lean_ctor_get(x_1835, 0);
lean_inc(x_1836);
x_1837 = lean_ctor_get(x_1835, 1);
lean_inc(x_1837);
lean_dec(x_1835);
x_1838 = lean_ctor_get(x_1836, 0);
lean_inc(x_1838);
x_1839 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1839 == 0)
{
lean_object* x_1854; 
lean_dec(x_27);
lean_dec(x_23);
x_1854 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1838, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1837);
if (lean_obj_tag(x_1854) == 0)
{
lean_object* x_1855; lean_object* x_1856; 
x_1855 = lean_ctor_get(x_1854, 1);
lean_inc(x_1855);
lean_dec(x_1854);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1856 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1855);
if (lean_obj_tag(x_1856) == 0)
{
lean_object* x_1857; lean_object* x_1858; 
x_1857 = lean_ctor_get(x_1856, 0);
lean_inc(x_1857);
x_1858 = lean_ctor_get(x_1856, 1);
lean_inc(x_1858);
lean_dec(x_1856);
x_1840 = x_1857;
x_1841 = x_1858;
goto block_1853;
}
else
{
uint8_t x_1859; 
lean_dec(x_1836);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1859 = !lean_is_exclusive(x_1856);
if (x_1859 == 0)
{
return x_1856;
}
else
{
lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; 
x_1860 = lean_ctor_get(x_1856, 0);
x_1861 = lean_ctor_get(x_1856, 1);
lean_inc(x_1861);
lean_inc(x_1860);
lean_dec(x_1856);
x_1862 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1862, 0, x_1860);
lean_ctor_set(x_1862, 1, x_1861);
return x_1862;
}
}
}
else
{
uint8_t x_1863; 
lean_dec(x_1836);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1863 = !lean_is_exclusive(x_1854);
if (x_1863 == 0)
{
return x_1854;
}
else
{
lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; 
x_1864 = lean_ctor_get(x_1854, 0);
x_1865 = lean_ctor_get(x_1854, 1);
lean_inc(x_1865);
lean_inc(x_1864);
lean_dec(x_1854);
x_1866 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1866, 0, x_1864);
lean_ctor_set(x_1866, 1, x_1865);
return x_1866;
}
}
}
else
{
lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; 
x_1867 = l_Lean_Expr_fvar___override(x_1838);
x_1868 = lean_array_get_size(x_23);
x_1869 = l_Array_toSubarray___rarg(x_23, x_27, x_1868);
x_1870 = l_Array_ofSubarray___rarg(x_1869);
x_1871 = l_Lean_mkAppN(x_1867, x_1870);
x_1872 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1873 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1871, x_1872, x_6, x_7, x_8, x_9, x_1837);
if (lean_obj_tag(x_1873) == 0)
{
lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; 
x_1874 = lean_ctor_get(x_1873, 0);
lean_inc(x_1874);
x_1875 = lean_ctor_get(x_1873, 1);
lean_inc(x_1875);
lean_dec(x_1873);
x_1876 = lean_ctor_get(x_1874, 0);
lean_inc(x_1876);
x_1877 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1876, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1875);
if (lean_obj_tag(x_1877) == 0)
{
lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; 
x_1878 = lean_ctor_get(x_1877, 1);
lean_inc(x_1878);
lean_dec(x_1877);
x_1879 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1879, 0, x_1874);
lean_ctor_set(x_1879, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1880 = l_Lean_Compiler_LCNF_Simp_simp(x_1879, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1878);
if (lean_obj_tag(x_1880) == 0)
{
lean_object* x_1881; lean_object* x_1882; 
x_1881 = lean_ctor_get(x_1880, 0);
lean_inc(x_1881);
x_1882 = lean_ctor_get(x_1880, 1);
lean_inc(x_1882);
lean_dec(x_1880);
x_1840 = x_1881;
x_1841 = x_1882;
goto block_1853;
}
else
{
uint8_t x_1883; 
lean_dec(x_1836);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1883 = !lean_is_exclusive(x_1880);
if (x_1883 == 0)
{
return x_1880;
}
else
{
lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; 
x_1884 = lean_ctor_get(x_1880, 0);
x_1885 = lean_ctor_get(x_1880, 1);
lean_inc(x_1885);
lean_inc(x_1884);
lean_dec(x_1880);
x_1886 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1886, 0, x_1884);
lean_ctor_set(x_1886, 1, x_1885);
return x_1886;
}
}
}
else
{
uint8_t x_1887; 
lean_dec(x_1874);
lean_dec(x_1836);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1887 = !lean_is_exclusive(x_1877);
if (x_1887 == 0)
{
return x_1877;
}
else
{
lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; 
x_1888 = lean_ctor_get(x_1877, 0);
x_1889 = lean_ctor_get(x_1877, 1);
lean_inc(x_1889);
lean_inc(x_1888);
lean_dec(x_1877);
x_1890 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1890, 0, x_1888);
lean_ctor_set(x_1890, 1, x_1889);
return x_1890;
}
}
}
else
{
uint8_t x_1891; 
lean_dec(x_1836);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1891 = !lean_is_exclusive(x_1873);
if (x_1891 == 0)
{
return x_1873;
}
else
{
lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; 
x_1892 = lean_ctor_get(x_1873, 0);
x_1893 = lean_ctor_get(x_1873, 1);
lean_inc(x_1893);
lean_inc(x_1892);
lean_dec(x_1873);
x_1894 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1894, 0, x_1892);
lean_ctor_set(x_1894, 1, x_1893);
return x_1894;
}
}
}
block_1853:
{
lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; uint8_t x_1846; 
x_1842 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1842, 0, x_1836);
x_1843 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1844 = lean_array_push(x_1843, x_1842);
x_1845 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1844, x_1840, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1841);
lean_dec(x_1844);
x_1846 = !lean_is_exclusive(x_1845);
if (x_1846 == 0)
{
lean_object* x_1847; lean_object* x_1848; 
x_1847 = lean_ctor_get(x_1845, 0);
if (lean_is_scalar(x_22)) {
 x_1848 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1848 = x_22;
}
lean_ctor_set(x_1848, 0, x_1847);
lean_ctor_set(x_1845, 0, x_1848);
return x_1845;
}
else
{
lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; 
x_1849 = lean_ctor_get(x_1845, 0);
x_1850 = lean_ctor_get(x_1845, 1);
lean_inc(x_1850);
lean_inc(x_1849);
lean_dec(x_1845);
if (lean_is_scalar(x_22)) {
 x_1851 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1851 = x_22;
}
lean_ctor_set(x_1851, 0, x_1849);
x_1852 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1852, 0, x_1851);
lean_ctor_set(x_1852, 1, x_1850);
return x_1852;
}
}
}
else
{
uint8_t x_1895; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1895 = !lean_is_exclusive(x_1835);
if (x_1895 == 0)
{
return x_1835;
}
else
{
lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; 
x_1896 = lean_ctor_get(x_1835, 0);
x_1897 = lean_ctor_get(x_1835, 1);
lean_inc(x_1897);
lean_inc(x_1896);
lean_dec(x_1835);
x_1898 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1898, 0, x_1896);
lean_ctor_set(x_1898, 1, x_1897);
return x_1898;
}
}
}
else
{
uint8_t x_1899; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1899 = !lean_is_exclusive(x_1832);
if (x_1899 == 0)
{
return x_1832;
}
else
{
lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; 
x_1900 = lean_ctor_get(x_1832, 0);
x_1901 = lean_ctor_get(x_1832, 1);
lean_inc(x_1901);
lean_inc(x_1900);
lean_dec(x_1832);
x_1902 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1902, 0, x_1900);
lean_ctor_set(x_1902, 1, x_1901);
return x_1902;
}
}
}
}
else
{
lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; 
lean_dec(x_1739);
x_1903 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1750);
x_1904 = lean_ctor_get(x_1903, 1);
lean_inc(x_1904);
lean_dec(x_1903);
x_1905 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_1905, 0, x_3);
lean_closure_set(x_1905, 1, x_4);
lean_closure_set(x_1905, 2, x_5);
lean_closure_set(x_1905, 3, x_27);
lean_closure_set(x_1905, 4, x_24);
lean_closure_set(x_1905, 5, x_26);
lean_closure_set(x_1905, 6, x_2);
lean_closure_set(x_1905, 7, x_23);
x_1906 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1749, x_1905, x_6, x_7, x_8, x_9, x_1904);
if (lean_obj_tag(x_1906) == 0)
{
uint8_t x_1907; 
x_1907 = !lean_is_exclusive(x_1906);
if (x_1907 == 0)
{
lean_object* x_1908; lean_object* x_1909; 
x_1908 = lean_ctor_get(x_1906, 0);
if (lean_is_scalar(x_22)) {
 x_1909 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1909 = x_22;
}
lean_ctor_set(x_1909, 0, x_1908);
lean_ctor_set(x_1906, 0, x_1909);
return x_1906;
}
else
{
lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; 
x_1910 = lean_ctor_get(x_1906, 0);
x_1911 = lean_ctor_get(x_1906, 1);
lean_inc(x_1911);
lean_inc(x_1910);
lean_dec(x_1906);
if (lean_is_scalar(x_22)) {
 x_1912 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1912 = x_22;
}
lean_ctor_set(x_1912, 0, x_1910);
x_1913 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1913, 0, x_1912);
lean_ctor_set(x_1913, 1, x_1911);
return x_1913;
}
}
else
{
uint8_t x_1914; 
lean_dec(x_22);
x_1914 = !lean_is_exclusive(x_1906);
if (x_1914 == 0)
{
return x_1906;
}
else
{
lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; 
x_1915 = lean_ctor_get(x_1906, 0);
x_1916 = lean_ctor_get(x_1906, 1);
lean_inc(x_1916);
lean_inc(x_1915);
lean_dec(x_1906);
x_1917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1917, 0, x_1915);
lean_ctor_set(x_1917, 1, x_1916);
return x_1917;
}
}
}
}
else
{
uint8_t x_1918; 
lean_dec(x_1739);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1918 = !lean_is_exclusive(x_1748);
if (x_1918 == 0)
{
return x_1748;
}
else
{
lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; 
x_1919 = lean_ctor_get(x_1748, 0);
x_1920 = lean_ctor_get(x_1748, 1);
lean_inc(x_1920);
lean_inc(x_1919);
lean_dec(x_1748);
x_1921 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1921, 0, x_1919);
lean_ctor_set(x_1921, 1, x_1920);
return x_1921;
}
}
}
}
else
{
uint8_t x_1941; 
lean_dec(x_1739);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1941 = !lean_is_exclusive(x_1744);
if (x_1941 == 0)
{
return x_1744;
}
else
{
lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; 
x_1942 = lean_ctor_get(x_1744, 0);
x_1943 = lean_ctor_get(x_1744, 1);
lean_inc(x_1943);
lean_inc(x_1942);
lean_dec(x_1744);
x_1944 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1944, 0, x_1942);
lean_ctor_set(x_1944, 1, x_1943);
return x_1944;
}
}
}
else
{
uint8_t x_1945; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1945 = !lean_is_exclusive(x_1738);
if (x_1945 == 0)
{
return x_1738;
}
else
{
lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; 
x_1946 = lean_ctor_get(x_1738, 0);
x_1947 = lean_ctor_get(x_1738, 1);
lean_inc(x_1947);
lean_inc(x_1946);
lean_dec(x_1738);
x_1948 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1948, 0, x_1946);
lean_ctor_set(x_1948, 1, x_1947);
return x_1948;
}
}
}
case 9:
{
lean_object* x_1949; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1949 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1949) == 0)
{
lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; uint8_t x_1954; lean_object* x_1955; 
x_1950 = lean_ctor_get(x_1949, 0);
lean_inc(x_1950);
x_1951 = lean_ctor_get(x_1949, 1);
lean_inc(x_1951);
lean_dec(x_1949);
x_1952 = lean_ctor_get(x_21, 0);
lean_inc(x_1952);
x_1953 = lean_ctor_get(x_21, 1);
lean_inc(x_1953);
lean_dec(x_21);
x_1954 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1955 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1952, x_1953, x_32, x_1954, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1951);
lean_dec(x_1952);
if (lean_obj_tag(x_1955) == 0)
{
lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; uint8_t x_2134; 
x_1956 = lean_ctor_get(x_1955, 0);
lean_inc(x_1956);
x_1957 = lean_ctor_get(x_1955, 1);
lean_inc(x_1957);
lean_dec(x_1955);
x_2134 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_2134 == 0)
{
lean_object* x_2135; 
x_2135 = lean_box(0);
x_1958 = x_2135;
goto block_2133;
}
else
{
uint8_t x_2136; 
x_2136 = lean_nat_dec_eq(x_24, x_27);
if (x_2136 == 0)
{
lean_object* x_2137; 
x_2137 = lean_box(0);
x_1958 = x_2137;
goto block_2133;
}
else
{
lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; 
lean_dec(x_1950);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_2138 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1957);
x_2139 = lean_ctor_get(x_2138, 1);
lean_inc(x_2139);
lean_dec(x_2138);
x_2140 = l_Lean_Compiler_LCNF_Simp_simp(x_1956, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2139);
if (lean_obj_tag(x_2140) == 0)
{
uint8_t x_2141; 
x_2141 = !lean_is_exclusive(x_2140);
if (x_2141 == 0)
{
lean_object* x_2142; lean_object* x_2143; 
x_2142 = lean_ctor_get(x_2140, 0);
x_2143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2143, 0, x_2142);
lean_ctor_set(x_2140, 0, x_2143);
return x_2140;
}
else
{
lean_object* x_2144; lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; 
x_2144 = lean_ctor_get(x_2140, 0);
x_2145 = lean_ctor_get(x_2140, 1);
lean_inc(x_2145);
lean_inc(x_2144);
lean_dec(x_2140);
x_2146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2146, 0, x_2144);
x_2147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2147, 0, x_2146);
lean_ctor_set(x_2147, 1, x_2145);
return x_2147;
}
}
else
{
uint8_t x_2148; 
x_2148 = !lean_is_exclusive(x_2140);
if (x_2148 == 0)
{
return x_2140;
}
else
{
lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; 
x_2149 = lean_ctor_get(x_2140, 0);
x_2150 = lean_ctor_get(x_2140, 1);
lean_inc(x_2150);
lean_inc(x_2149);
lean_dec(x_2140);
x_2151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2151, 0, x_2149);
lean_ctor_set(x_2151, 1, x_2150);
return x_2151;
}
}
}
}
block_2133:
{
lean_object* x_1959; 
lean_dec(x_1958);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1959 = l_Lean_Compiler_LCNF_Simp_simp(x_1956, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1957);
if (lean_obj_tag(x_1959) == 0)
{
lean_object* x_1960; lean_object* x_1961; uint8_t x_1962; 
x_1960 = lean_ctor_get(x_1959, 0);
lean_inc(x_1960);
x_1961 = lean_ctor_get(x_1959, 1);
lean_inc(x_1961);
lean_dec(x_1959);
lean_inc(x_1960);
x_1962 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1960);
if (x_1962 == 0)
{
lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; uint8_t x_1966; 
x_1963 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1961);
x_1964 = lean_ctor_get(x_1963, 1);
lean_inc(x_1964);
lean_dec(x_1963);
lean_inc(x_1950);
x_1965 = l_Lean_Expr_headBeta(x_1950);
x_1966 = l_Lean_Expr_isForall(x_1965);
lean_dec(x_1965);
if (x_1966 == 0)
{
lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; uint8_t x_1971; lean_object* x_1972; lean_object* x_1973; 
x_1967 = l_Lean_Compiler_LCNF_mkAuxParam(x_1950, x_1954, x_6, x_7, x_8, x_9, x_1964);
x_1968 = lean_ctor_get(x_1967, 0);
lean_inc(x_1968);
x_1969 = lean_ctor_get(x_1967, 1);
lean_inc(x_1969);
lean_dec(x_1967);
x_1970 = lean_ctor_get(x_1968, 0);
lean_inc(x_1970);
x_1971 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1971 == 0)
{
lean_object* x_2000; 
lean_dec(x_27);
lean_dec(x_23);
x_2000 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1970, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1969);
if (lean_obj_tag(x_2000) == 0)
{
lean_object* x_2001; lean_object* x_2002; 
x_2001 = lean_ctor_get(x_2000, 1);
lean_inc(x_2001);
lean_dec(x_2000);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2002 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2001);
if (lean_obj_tag(x_2002) == 0)
{
lean_object* x_2003; lean_object* x_2004; 
x_2003 = lean_ctor_get(x_2002, 0);
lean_inc(x_2003);
x_2004 = lean_ctor_get(x_2002, 1);
lean_inc(x_2004);
lean_dec(x_2002);
x_1972 = x_2003;
x_1973 = x_2004;
goto block_1999;
}
else
{
uint8_t x_2005; 
lean_dec(x_1968);
lean_dec(x_1960);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2005 = !lean_is_exclusive(x_2002);
if (x_2005 == 0)
{
return x_2002;
}
else
{
lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; 
x_2006 = lean_ctor_get(x_2002, 0);
x_2007 = lean_ctor_get(x_2002, 1);
lean_inc(x_2007);
lean_inc(x_2006);
lean_dec(x_2002);
x_2008 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2008, 0, x_2006);
lean_ctor_set(x_2008, 1, x_2007);
return x_2008;
}
}
}
else
{
uint8_t x_2009; 
lean_dec(x_1968);
lean_dec(x_1960);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2009 = !lean_is_exclusive(x_2000);
if (x_2009 == 0)
{
return x_2000;
}
else
{
lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; 
x_2010 = lean_ctor_get(x_2000, 0);
x_2011 = lean_ctor_get(x_2000, 1);
lean_inc(x_2011);
lean_inc(x_2010);
lean_dec(x_2000);
x_2012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2012, 0, x_2010);
lean_ctor_set(x_2012, 1, x_2011);
return x_2012;
}
}
}
else
{
lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; 
x_2013 = l_Lean_Expr_fvar___override(x_1970);
x_2014 = lean_array_get_size(x_23);
x_2015 = l_Array_toSubarray___rarg(x_23, x_27, x_2014);
x_2016 = l_Array_ofSubarray___rarg(x_2015);
x_2017 = l_Lean_mkAppN(x_2013, x_2016);
x_2018 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2019 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2017, x_2018, x_6, x_7, x_8, x_9, x_1969);
if (lean_obj_tag(x_2019) == 0)
{
lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; 
x_2020 = lean_ctor_get(x_2019, 0);
lean_inc(x_2020);
x_2021 = lean_ctor_get(x_2019, 1);
lean_inc(x_2021);
lean_dec(x_2019);
x_2022 = lean_ctor_get(x_2020, 0);
lean_inc(x_2022);
x_2023 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2022, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2021);
if (lean_obj_tag(x_2023) == 0)
{
lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; 
x_2024 = lean_ctor_get(x_2023, 1);
lean_inc(x_2024);
lean_dec(x_2023);
x_2025 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2025, 0, x_2020);
lean_ctor_set(x_2025, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2026 = l_Lean_Compiler_LCNF_Simp_simp(x_2025, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2024);
if (lean_obj_tag(x_2026) == 0)
{
lean_object* x_2027; lean_object* x_2028; 
x_2027 = lean_ctor_get(x_2026, 0);
lean_inc(x_2027);
x_2028 = lean_ctor_get(x_2026, 1);
lean_inc(x_2028);
lean_dec(x_2026);
x_1972 = x_2027;
x_1973 = x_2028;
goto block_1999;
}
else
{
uint8_t x_2029; 
lean_dec(x_1968);
lean_dec(x_1960);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2029 = !lean_is_exclusive(x_2026);
if (x_2029 == 0)
{
return x_2026;
}
else
{
lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; 
x_2030 = lean_ctor_get(x_2026, 0);
x_2031 = lean_ctor_get(x_2026, 1);
lean_inc(x_2031);
lean_inc(x_2030);
lean_dec(x_2026);
x_2032 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2032, 0, x_2030);
lean_ctor_set(x_2032, 1, x_2031);
return x_2032;
}
}
}
else
{
uint8_t x_2033; 
lean_dec(x_2020);
lean_dec(x_1968);
lean_dec(x_1960);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2033 = !lean_is_exclusive(x_2023);
if (x_2033 == 0)
{
return x_2023;
}
else
{
lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; 
x_2034 = lean_ctor_get(x_2023, 0);
x_2035 = lean_ctor_get(x_2023, 1);
lean_inc(x_2035);
lean_inc(x_2034);
lean_dec(x_2023);
x_2036 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2036, 0, x_2034);
lean_ctor_set(x_2036, 1, x_2035);
return x_2036;
}
}
}
else
{
uint8_t x_2037; 
lean_dec(x_1968);
lean_dec(x_1960);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2037 = !lean_is_exclusive(x_2019);
if (x_2037 == 0)
{
return x_2019;
}
else
{
lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; 
x_2038 = lean_ctor_get(x_2019, 0);
x_2039 = lean_ctor_get(x_2019, 1);
lean_inc(x_2039);
lean_inc(x_2038);
lean_dec(x_2019);
x_2040 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2040, 0, x_2038);
lean_ctor_set(x_2040, 1, x_2039);
return x_2040;
}
}
}
block_1999:
{
lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; 
x_1974 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1975 = lean_array_push(x_1974, x_1968);
x_1976 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1977 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1975, x_1972, x_1976, x_6, x_7, x_8, x_9, x_1973);
if (lean_obj_tag(x_1977) == 0)
{
lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; 
x_1978 = lean_ctor_get(x_1977, 0);
lean_inc(x_1978);
x_1979 = lean_ctor_get(x_1977, 1);
lean_inc(x_1979);
lean_dec(x_1977);
lean_inc(x_1978);
x_1980 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1980, 0, x_1978);
lean_closure_set(x_1980, 1, x_1974);
x_1981 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1960, x_1980, x_6, x_7, x_8, x_9, x_1979);
if (lean_obj_tag(x_1981) == 0)
{
uint8_t x_1982; 
x_1982 = !lean_is_exclusive(x_1981);
if (x_1982 == 0)
{
lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; 
x_1983 = lean_ctor_get(x_1981, 0);
x_1984 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1984, 0, x_1978);
lean_ctor_set(x_1984, 1, x_1983);
if (lean_is_scalar(x_22)) {
 x_1985 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1985 = x_22;
}
lean_ctor_set(x_1985, 0, x_1984);
lean_ctor_set(x_1981, 0, x_1985);
return x_1981;
}
else
{
lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; 
x_1986 = lean_ctor_get(x_1981, 0);
x_1987 = lean_ctor_get(x_1981, 1);
lean_inc(x_1987);
lean_inc(x_1986);
lean_dec(x_1981);
x_1988 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1988, 0, x_1978);
lean_ctor_set(x_1988, 1, x_1986);
if (lean_is_scalar(x_22)) {
 x_1989 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1989 = x_22;
}
lean_ctor_set(x_1989, 0, x_1988);
x_1990 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1990, 0, x_1989);
lean_ctor_set(x_1990, 1, x_1987);
return x_1990;
}
}
else
{
uint8_t x_1991; 
lean_dec(x_1978);
lean_dec(x_22);
x_1991 = !lean_is_exclusive(x_1981);
if (x_1991 == 0)
{
return x_1981;
}
else
{
lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; 
x_1992 = lean_ctor_get(x_1981, 0);
x_1993 = lean_ctor_get(x_1981, 1);
lean_inc(x_1993);
lean_inc(x_1992);
lean_dec(x_1981);
x_1994 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1994, 0, x_1992);
lean_ctor_set(x_1994, 1, x_1993);
return x_1994;
}
}
}
else
{
uint8_t x_1995; 
lean_dec(x_1960);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1995 = !lean_is_exclusive(x_1977);
if (x_1995 == 0)
{
return x_1977;
}
else
{
lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; 
x_1996 = lean_ctor_get(x_1977, 0);
x_1997 = lean_ctor_get(x_1977, 1);
lean_inc(x_1997);
lean_inc(x_1996);
lean_dec(x_1977);
x_1998 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1998, 0, x_1996);
lean_ctor_set(x_1998, 1, x_1997);
return x_1998;
}
}
}
}
else
{
lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; 
lean_dec(x_1950);
x_2041 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_2042 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2043 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_2041, x_1960, x_2042, x_6, x_7, x_8, x_9, x_1964);
if (lean_obj_tag(x_2043) == 0)
{
lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; 
x_2044 = lean_ctor_get(x_2043, 0);
lean_inc(x_2044);
x_2045 = lean_ctor_get(x_2043, 1);
lean_inc(x_2045);
lean_dec(x_2043);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2046 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_2044, x_6, x_7, x_8, x_9, x_2045);
if (lean_obj_tag(x_2046) == 0)
{
lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; uint8_t x_2050; lean_object* x_2051; lean_object* x_2052; 
x_2047 = lean_ctor_get(x_2046, 0);
lean_inc(x_2047);
x_2048 = lean_ctor_get(x_2046, 1);
lean_inc(x_2048);
lean_dec(x_2046);
x_2049 = lean_ctor_get(x_2047, 0);
lean_inc(x_2049);
x_2050 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_2050 == 0)
{
lean_object* x_2065; 
lean_dec(x_27);
lean_dec(x_23);
x_2065 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2049, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2048);
if (lean_obj_tag(x_2065) == 0)
{
lean_object* x_2066; lean_object* x_2067; 
x_2066 = lean_ctor_get(x_2065, 1);
lean_inc(x_2066);
lean_dec(x_2065);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2067 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2066);
if (lean_obj_tag(x_2067) == 0)
{
lean_object* x_2068; lean_object* x_2069; 
x_2068 = lean_ctor_get(x_2067, 0);
lean_inc(x_2068);
x_2069 = lean_ctor_get(x_2067, 1);
lean_inc(x_2069);
lean_dec(x_2067);
x_2051 = x_2068;
x_2052 = x_2069;
goto block_2064;
}
else
{
uint8_t x_2070; 
lean_dec(x_2047);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2070 = !lean_is_exclusive(x_2067);
if (x_2070 == 0)
{
return x_2067;
}
else
{
lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; 
x_2071 = lean_ctor_get(x_2067, 0);
x_2072 = lean_ctor_get(x_2067, 1);
lean_inc(x_2072);
lean_inc(x_2071);
lean_dec(x_2067);
x_2073 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2073, 0, x_2071);
lean_ctor_set(x_2073, 1, x_2072);
return x_2073;
}
}
}
else
{
uint8_t x_2074; 
lean_dec(x_2047);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2074 = !lean_is_exclusive(x_2065);
if (x_2074 == 0)
{
return x_2065;
}
else
{
lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; 
x_2075 = lean_ctor_get(x_2065, 0);
x_2076 = lean_ctor_get(x_2065, 1);
lean_inc(x_2076);
lean_inc(x_2075);
lean_dec(x_2065);
x_2077 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2077, 0, x_2075);
lean_ctor_set(x_2077, 1, x_2076);
return x_2077;
}
}
}
else
{
lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; 
x_2078 = l_Lean_Expr_fvar___override(x_2049);
x_2079 = lean_array_get_size(x_23);
x_2080 = l_Array_toSubarray___rarg(x_23, x_27, x_2079);
x_2081 = l_Array_ofSubarray___rarg(x_2080);
x_2082 = l_Lean_mkAppN(x_2078, x_2081);
x_2083 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2084 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2082, x_2083, x_6, x_7, x_8, x_9, x_2048);
if (lean_obj_tag(x_2084) == 0)
{
lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; 
x_2085 = lean_ctor_get(x_2084, 0);
lean_inc(x_2085);
x_2086 = lean_ctor_get(x_2084, 1);
lean_inc(x_2086);
lean_dec(x_2084);
x_2087 = lean_ctor_get(x_2085, 0);
lean_inc(x_2087);
x_2088 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2087, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2086);
if (lean_obj_tag(x_2088) == 0)
{
lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; 
x_2089 = lean_ctor_get(x_2088, 1);
lean_inc(x_2089);
lean_dec(x_2088);
x_2090 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2090, 0, x_2085);
lean_ctor_set(x_2090, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2091 = l_Lean_Compiler_LCNF_Simp_simp(x_2090, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2089);
if (lean_obj_tag(x_2091) == 0)
{
lean_object* x_2092; lean_object* x_2093; 
x_2092 = lean_ctor_get(x_2091, 0);
lean_inc(x_2092);
x_2093 = lean_ctor_get(x_2091, 1);
lean_inc(x_2093);
lean_dec(x_2091);
x_2051 = x_2092;
x_2052 = x_2093;
goto block_2064;
}
else
{
uint8_t x_2094; 
lean_dec(x_2047);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2094 = !lean_is_exclusive(x_2091);
if (x_2094 == 0)
{
return x_2091;
}
else
{
lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; 
x_2095 = lean_ctor_get(x_2091, 0);
x_2096 = lean_ctor_get(x_2091, 1);
lean_inc(x_2096);
lean_inc(x_2095);
lean_dec(x_2091);
x_2097 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2097, 0, x_2095);
lean_ctor_set(x_2097, 1, x_2096);
return x_2097;
}
}
}
else
{
uint8_t x_2098; 
lean_dec(x_2085);
lean_dec(x_2047);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2098 = !lean_is_exclusive(x_2088);
if (x_2098 == 0)
{
return x_2088;
}
else
{
lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; 
x_2099 = lean_ctor_get(x_2088, 0);
x_2100 = lean_ctor_get(x_2088, 1);
lean_inc(x_2100);
lean_inc(x_2099);
lean_dec(x_2088);
x_2101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2101, 0, x_2099);
lean_ctor_set(x_2101, 1, x_2100);
return x_2101;
}
}
}
else
{
uint8_t x_2102; 
lean_dec(x_2047);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2102 = !lean_is_exclusive(x_2084);
if (x_2102 == 0)
{
return x_2084;
}
else
{
lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; 
x_2103 = lean_ctor_get(x_2084, 0);
x_2104 = lean_ctor_get(x_2084, 1);
lean_inc(x_2104);
lean_inc(x_2103);
lean_dec(x_2084);
x_2105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2105, 0, x_2103);
lean_ctor_set(x_2105, 1, x_2104);
return x_2105;
}
}
}
block_2064:
{
lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; uint8_t x_2057; 
x_2053 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2053, 0, x_2047);
x_2054 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2055 = lean_array_push(x_2054, x_2053);
x_2056 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_2055, x_2051, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2052);
lean_dec(x_2055);
x_2057 = !lean_is_exclusive(x_2056);
if (x_2057 == 0)
{
lean_object* x_2058; lean_object* x_2059; 
x_2058 = lean_ctor_get(x_2056, 0);
if (lean_is_scalar(x_22)) {
 x_2059 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2059 = x_22;
}
lean_ctor_set(x_2059, 0, x_2058);
lean_ctor_set(x_2056, 0, x_2059);
return x_2056;
}
else
{
lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; 
x_2060 = lean_ctor_get(x_2056, 0);
x_2061 = lean_ctor_get(x_2056, 1);
lean_inc(x_2061);
lean_inc(x_2060);
lean_dec(x_2056);
if (lean_is_scalar(x_22)) {
 x_2062 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2062 = x_22;
}
lean_ctor_set(x_2062, 0, x_2060);
x_2063 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2063, 0, x_2062);
lean_ctor_set(x_2063, 1, x_2061);
return x_2063;
}
}
}
else
{
uint8_t x_2106; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2106 = !lean_is_exclusive(x_2046);
if (x_2106 == 0)
{
return x_2046;
}
else
{
lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; 
x_2107 = lean_ctor_get(x_2046, 0);
x_2108 = lean_ctor_get(x_2046, 1);
lean_inc(x_2108);
lean_inc(x_2107);
lean_dec(x_2046);
x_2109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2109, 0, x_2107);
lean_ctor_set(x_2109, 1, x_2108);
return x_2109;
}
}
}
else
{
uint8_t x_2110; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2110 = !lean_is_exclusive(x_2043);
if (x_2110 == 0)
{
return x_2043;
}
else
{
lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; 
x_2111 = lean_ctor_get(x_2043, 0);
x_2112 = lean_ctor_get(x_2043, 1);
lean_inc(x_2112);
lean_inc(x_2111);
lean_dec(x_2043);
x_2113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2113, 0, x_2111);
lean_ctor_set(x_2113, 1, x_2112);
return x_2113;
}
}
}
}
else
{
lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; 
lean_dec(x_1950);
x_2114 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1961);
x_2115 = lean_ctor_get(x_2114, 1);
lean_inc(x_2115);
lean_dec(x_2114);
x_2116 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_2116, 0, x_3);
lean_closure_set(x_2116, 1, x_4);
lean_closure_set(x_2116, 2, x_5);
lean_closure_set(x_2116, 3, x_27);
lean_closure_set(x_2116, 4, x_24);
lean_closure_set(x_2116, 5, x_26);
lean_closure_set(x_2116, 6, x_2);
lean_closure_set(x_2116, 7, x_23);
x_2117 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1960, x_2116, x_6, x_7, x_8, x_9, x_2115);
if (lean_obj_tag(x_2117) == 0)
{
uint8_t x_2118; 
x_2118 = !lean_is_exclusive(x_2117);
if (x_2118 == 0)
{
lean_object* x_2119; lean_object* x_2120; 
x_2119 = lean_ctor_get(x_2117, 0);
if (lean_is_scalar(x_22)) {
 x_2120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2120 = x_22;
}
lean_ctor_set(x_2120, 0, x_2119);
lean_ctor_set(x_2117, 0, x_2120);
return x_2117;
}
else
{
lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; 
x_2121 = lean_ctor_get(x_2117, 0);
x_2122 = lean_ctor_get(x_2117, 1);
lean_inc(x_2122);
lean_inc(x_2121);
lean_dec(x_2117);
if (lean_is_scalar(x_22)) {
 x_2123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2123 = x_22;
}
lean_ctor_set(x_2123, 0, x_2121);
x_2124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2124, 0, x_2123);
lean_ctor_set(x_2124, 1, x_2122);
return x_2124;
}
}
else
{
uint8_t x_2125; 
lean_dec(x_22);
x_2125 = !lean_is_exclusive(x_2117);
if (x_2125 == 0)
{
return x_2117;
}
else
{
lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; 
x_2126 = lean_ctor_get(x_2117, 0);
x_2127 = lean_ctor_get(x_2117, 1);
lean_inc(x_2127);
lean_inc(x_2126);
lean_dec(x_2117);
x_2128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2128, 0, x_2126);
lean_ctor_set(x_2128, 1, x_2127);
return x_2128;
}
}
}
}
else
{
uint8_t x_2129; 
lean_dec(x_1950);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2129 = !lean_is_exclusive(x_1959);
if (x_2129 == 0)
{
return x_1959;
}
else
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; 
x_2130 = lean_ctor_get(x_1959, 0);
x_2131 = lean_ctor_get(x_1959, 1);
lean_inc(x_2131);
lean_inc(x_2130);
lean_dec(x_1959);
x_2132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2132, 0, x_2130);
lean_ctor_set(x_2132, 1, x_2131);
return x_2132;
}
}
}
}
else
{
uint8_t x_2152; 
lean_dec(x_1950);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2152 = !lean_is_exclusive(x_1955);
if (x_2152 == 0)
{
return x_1955;
}
else
{
lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; 
x_2153 = lean_ctor_get(x_1955, 0);
x_2154 = lean_ctor_get(x_1955, 1);
lean_inc(x_2154);
lean_inc(x_2153);
lean_dec(x_1955);
x_2155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2155, 0, x_2153);
lean_ctor_set(x_2155, 1, x_2154);
return x_2155;
}
}
}
else
{
uint8_t x_2156; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2156 = !lean_is_exclusive(x_1949);
if (x_2156 == 0)
{
return x_1949;
}
else
{
lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; 
x_2157 = lean_ctor_get(x_1949, 0);
x_2158 = lean_ctor_get(x_1949, 1);
lean_inc(x_2158);
lean_inc(x_2157);
lean_dec(x_1949);
x_2159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2159, 0, x_2157);
lean_ctor_set(x_2159, 1, x_2158);
return x_2159;
}
}
}
case 10:
{
lean_object* x_2160; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2160 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_2160) == 0)
{
lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; uint8_t x_2165; lean_object* x_2166; 
x_2161 = lean_ctor_get(x_2160, 0);
lean_inc(x_2161);
x_2162 = lean_ctor_get(x_2160, 1);
lean_inc(x_2162);
lean_dec(x_2160);
x_2163 = lean_ctor_get(x_21, 0);
lean_inc(x_2163);
x_2164 = lean_ctor_get(x_21, 1);
lean_inc(x_2164);
lean_dec(x_21);
x_2165 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2166 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2163, x_2164, x_32, x_2165, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2162);
lean_dec(x_2163);
if (lean_obj_tag(x_2166) == 0)
{
lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; uint8_t x_2345; 
x_2167 = lean_ctor_get(x_2166, 0);
lean_inc(x_2167);
x_2168 = lean_ctor_get(x_2166, 1);
lean_inc(x_2168);
lean_dec(x_2166);
x_2345 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_2345 == 0)
{
lean_object* x_2346; 
x_2346 = lean_box(0);
x_2169 = x_2346;
goto block_2344;
}
else
{
uint8_t x_2347; 
x_2347 = lean_nat_dec_eq(x_24, x_27);
if (x_2347 == 0)
{
lean_object* x_2348; 
x_2348 = lean_box(0);
x_2169 = x_2348;
goto block_2344;
}
else
{
lean_object* x_2349; lean_object* x_2350; lean_object* x_2351; 
lean_dec(x_2161);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_2349 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2168);
x_2350 = lean_ctor_get(x_2349, 1);
lean_inc(x_2350);
lean_dec(x_2349);
x_2351 = l_Lean_Compiler_LCNF_Simp_simp(x_2167, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2350);
if (lean_obj_tag(x_2351) == 0)
{
uint8_t x_2352; 
x_2352 = !lean_is_exclusive(x_2351);
if (x_2352 == 0)
{
lean_object* x_2353; lean_object* x_2354; 
x_2353 = lean_ctor_get(x_2351, 0);
x_2354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2354, 0, x_2353);
lean_ctor_set(x_2351, 0, x_2354);
return x_2351;
}
else
{
lean_object* x_2355; lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; 
x_2355 = lean_ctor_get(x_2351, 0);
x_2356 = lean_ctor_get(x_2351, 1);
lean_inc(x_2356);
lean_inc(x_2355);
lean_dec(x_2351);
x_2357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2357, 0, x_2355);
x_2358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2358, 0, x_2357);
lean_ctor_set(x_2358, 1, x_2356);
return x_2358;
}
}
else
{
uint8_t x_2359; 
x_2359 = !lean_is_exclusive(x_2351);
if (x_2359 == 0)
{
return x_2351;
}
else
{
lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; 
x_2360 = lean_ctor_get(x_2351, 0);
x_2361 = lean_ctor_get(x_2351, 1);
lean_inc(x_2361);
lean_inc(x_2360);
lean_dec(x_2351);
x_2362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2362, 0, x_2360);
lean_ctor_set(x_2362, 1, x_2361);
return x_2362;
}
}
}
}
block_2344:
{
lean_object* x_2170; 
lean_dec(x_2169);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2170 = l_Lean_Compiler_LCNF_Simp_simp(x_2167, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2168);
if (lean_obj_tag(x_2170) == 0)
{
lean_object* x_2171; lean_object* x_2172; uint8_t x_2173; 
x_2171 = lean_ctor_get(x_2170, 0);
lean_inc(x_2171);
x_2172 = lean_ctor_get(x_2170, 1);
lean_inc(x_2172);
lean_dec(x_2170);
lean_inc(x_2171);
x_2173 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_2171);
if (x_2173 == 0)
{
lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; uint8_t x_2177; 
x_2174 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2172);
x_2175 = lean_ctor_get(x_2174, 1);
lean_inc(x_2175);
lean_dec(x_2174);
lean_inc(x_2161);
x_2176 = l_Lean_Expr_headBeta(x_2161);
x_2177 = l_Lean_Expr_isForall(x_2176);
lean_dec(x_2176);
if (x_2177 == 0)
{
lean_object* x_2178; lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; uint8_t x_2182; lean_object* x_2183; lean_object* x_2184; 
x_2178 = l_Lean_Compiler_LCNF_mkAuxParam(x_2161, x_2165, x_6, x_7, x_8, x_9, x_2175);
x_2179 = lean_ctor_get(x_2178, 0);
lean_inc(x_2179);
x_2180 = lean_ctor_get(x_2178, 1);
lean_inc(x_2180);
lean_dec(x_2178);
x_2181 = lean_ctor_get(x_2179, 0);
lean_inc(x_2181);
x_2182 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_2182 == 0)
{
lean_object* x_2211; 
lean_dec(x_27);
lean_dec(x_23);
x_2211 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2181, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2180);
if (lean_obj_tag(x_2211) == 0)
{
lean_object* x_2212; lean_object* x_2213; 
x_2212 = lean_ctor_get(x_2211, 1);
lean_inc(x_2212);
lean_dec(x_2211);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2213 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2212);
if (lean_obj_tag(x_2213) == 0)
{
lean_object* x_2214; lean_object* x_2215; 
x_2214 = lean_ctor_get(x_2213, 0);
lean_inc(x_2214);
x_2215 = lean_ctor_get(x_2213, 1);
lean_inc(x_2215);
lean_dec(x_2213);
x_2183 = x_2214;
x_2184 = x_2215;
goto block_2210;
}
else
{
uint8_t x_2216; 
lean_dec(x_2179);
lean_dec(x_2171);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2216 = !lean_is_exclusive(x_2213);
if (x_2216 == 0)
{
return x_2213;
}
else
{
lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; 
x_2217 = lean_ctor_get(x_2213, 0);
x_2218 = lean_ctor_get(x_2213, 1);
lean_inc(x_2218);
lean_inc(x_2217);
lean_dec(x_2213);
x_2219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2219, 0, x_2217);
lean_ctor_set(x_2219, 1, x_2218);
return x_2219;
}
}
}
else
{
uint8_t x_2220; 
lean_dec(x_2179);
lean_dec(x_2171);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2220 = !lean_is_exclusive(x_2211);
if (x_2220 == 0)
{
return x_2211;
}
else
{
lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; 
x_2221 = lean_ctor_get(x_2211, 0);
x_2222 = lean_ctor_get(x_2211, 1);
lean_inc(x_2222);
lean_inc(x_2221);
lean_dec(x_2211);
x_2223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2223, 0, x_2221);
lean_ctor_set(x_2223, 1, x_2222);
return x_2223;
}
}
}
else
{
lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; 
x_2224 = l_Lean_Expr_fvar___override(x_2181);
x_2225 = lean_array_get_size(x_23);
x_2226 = l_Array_toSubarray___rarg(x_23, x_27, x_2225);
x_2227 = l_Array_ofSubarray___rarg(x_2226);
x_2228 = l_Lean_mkAppN(x_2224, x_2227);
x_2229 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2230 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2228, x_2229, x_6, x_7, x_8, x_9, x_2180);
if (lean_obj_tag(x_2230) == 0)
{
lean_object* x_2231; lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; 
x_2231 = lean_ctor_get(x_2230, 0);
lean_inc(x_2231);
x_2232 = lean_ctor_get(x_2230, 1);
lean_inc(x_2232);
lean_dec(x_2230);
x_2233 = lean_ctor_get(x_2231, 0);
lean_inc(x_2233);
x_2234 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2233, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2232);
if (lean_obj_tag(x_2234) == 0)
{
lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; 
x_2235 = lean_ctor_get(x_2234, 1);
lean_inc(x_2235);
lean_dec(x_2234);
x_2236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2236, 0, x_2231);
lean_ctor_set(x_2236, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2237 = l_Lean_Compiler_LCNF_Simp_simp(x_2236, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2235);
if (lean_obj_tag(x_2237) == 0)
{
lean_object* x_2238; lean_object* x_2239; 
x_2238 = lean_ctor_get(x_2237, 0);
lean_inc(x_2238);
x_2239 = lean_ctor_get(x_2237, 1);
lean_inc(x_2239);
lean_dec(x_2237);
x_2183 = x_2238;
x_2184 = x_2239;
goto block_2210;
}
else
{
uint8_t x_2240; 
lean_dec(x_2179);
lean_dec(x_2171);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2240 = !lean_is_exclusive(x_2237);
if (x_2240 == 0)
{
return x_2237;
}
else
{
lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; 
x_2241 = lean_ctor_get(x_2237, 0);
x_2242 = lean_ctor_get(x_2237, 1);
lean_inc(x_2242);
lean_inc(x_2241);
lean_dec(x_2237);
x_2243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2243, 0, x_2241);
lean_ctor_set(x_2243, 1, x_2242);
return x_2243;
}
}
}
else
{
uint8_t x_2244; 
lean_dec(x_2231);
lean_dec(x_2179);
lean_dec(x_2171);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2244 = !lean_is_exclusive(x_2234);
if (x_2244 == 0)
{
return x_2234;
}
else
{
lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; 
x_2245 = lean_ctor_get(x_2234, 0);
x_2246 = lean_ctor_get(x_2234, 1);
lean_inc(x_2246);
lean_inc(x_2245);
lean_dec(x_2234);
x_2247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2247, 0, x_2245);
lean_ctor_set(x_2247, 1, x_2246);
return x_2247;
}
}
}
else
{
uint8_t x_2248; 
lean_dec(x_2179);
lean_dec(x_2171);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2248 = !lean_is_exclusive(x_2230);
if (x_2248 == 0)
{
return x_2230;
}
else
{
lean_object* x_2249; lean_object* x_2250; lean_object* x_2251; 
x_2249 = lean_ctor_get(x_2230, 0);
x_2250 = lean_ctor_get(x_2230, 1);
lean_inc(x_2250);
lean_inc(x_2249);
lean_dec(x_2230);
x_2251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2251, 0, x_2249);
lean_ctor_set(x_2251, 1, x_2250);
return x_2251;
}
}
}
block_2210:
{
lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; 
x_2185 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2186 = lean_array_push(x_2185, x_2179);
x_2187 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2188 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_2186, x_2183, x_2187, x_6, x_7, x_8, x_9, x_2184);
if (lean_obj_tag(x_2188) == 0)
{
lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; 
x_2189 = lean_ctor_get(x_2188, 0);
lean_inc(x_2189);
x_2190 = lean_ctor_get(x_2188, 1);
lean_inc(x_2190);
lean_dec(x_2188);
lean_inc(x_2189);
x_2191 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_2191, 0, x_2189);
lean_closure_set(x_2191, 1, x_2185);
x_2192 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_2171, x_2191, x_6, x_7, x_8, x_9, x_2190);
if (lean_obj_tag(x_2192) == 0)
{
uint8_t x_2193; 
x_2193 = !lean_is_exclusive(x_2192);
if (x_2193 == 0)
{
lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; 
x_2194 = lean_ctor_get(x_2192, 0);
x_2195 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2195, 0, x_2189);
lean_ctor_set(x_2195, 1, x_2194);
if (lean_is_scalar(x_22)) {
 x_2196 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2196 = x_22;
}
lean_ctor_set(x_2196, 0, x_2195);
lean_ctor_set(x_2192, 0, x_2196);
return x_2192;
}
else
{
lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; 
x_2197 = lean_ctor_get(x_2192, 0);
x_2198 = lean_ctor_get(x_2192, 1);
lean_inc(x_2198);
lean_inc(x_2197);
lean_dec(x_2192);
x_2199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2199, 0, x_2189);
lean_ctor_set(x_2199, 1, x_2197);
if (lean_is_scalar(x_22)) {
 x_2200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2200 = x_22;
}
lean_ctor_set(x_2200, 0, x_2199);
x_2201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2201, 0, x_2200);
lean_ctor_set(x_2201, 1, x_2198);
return x_2201;
}
}
else
{
uint8_t x_2202; 
lean_dec(x_2189);
lean_dec(x_22);
x_2202 = !lean_is_exclusive(x_2192);
if (x_2202 == 0)
{
return x_2192;
}
else
{
lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; 
x_2203 = lean_ctor_get(x_2192, 0);
x_2204 = lean_ctor_get(x_2192, 1);
lean_inc(x_2204);
lean_inc(x_2203);
lean_dec(x_2192);
x_2205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2205, 0, x_2203);
lean_ctor_set(x_2205, 1, x_2204);
return x_2205;
}
}
}
else
{
uint8_t x_2206; 
lean_dec(x_2171);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2206 = !lean_is_exclusive(x_2188);
if (x_2206 == 0)
{
return x_2188;
}
else
{
lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; 
x_2207 = lean_ctor_get(x_2188, 0);
x_2208 = lean_ctor_get(x_2188, 1);
lean_inc(x_2208);
lean_inc(x_2207);
lean_dec(x_2188);
x_2209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2209, 0, x_2207);
lean_ctor_set(x_2209, 1, x_2208);
return x_2209;
}
}
}
}
else
{
lean_object* x_2252; lean_object* x_2253; lean_object* x_2254; 
lean_dec(x_2161);
x_2252 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_2253 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2254 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_2252, x_2171, x_2253, x_6, x_7, x_8, x_9, x_2175);
if (lean_obj_tag(x_2254) == 0)
{
lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; 
x_2255 = lean_ctor_get(x_2254, 0);
lean_inc(x_2255);
x_2256 = lean_ctor_get(x_2254, 1);
lean_inc(x_2256);
lean_dec(x_2254);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2257 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_2255, x_6, x_7, x_8, x_9, x_2256);
if (lean_obj_tag(x_2257) == 0)
{
lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; uint8_t x_2261; lean_object* x_2262; lean_object* x_2263; 
x_2258 = lean_ctor_get(x_2257, 0);
lean_inc(x_2258);
x_2259 = lean_ctor_get(x_2257, 1);
lean_inc(x_2259);
lean_dec(x_2257);
x_2260 = lean_ctor_get(x_2258, 0);
lean_inc(x_2260);
x_2261 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_2261 == 0)
{
lean_object* x_2276; 
lean_dec(x_27);
lean_dec(x_23);
x_2276 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2260, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2259);
if (lean_obj_tag(x_2276) == 0)
{
lean_object* x_2277; lean_object* x_2278; 
x_2277 = lean_ctor_get(x_2276, 1);
lean_inc(x_2277);
lean_dec(x_2276);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2278 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2277);
if (lean_obj_tag(x_2278) == 0)
{
lean_object* x_2279; lean_object* x_2280; 
x_2279 = lean_ctor_get(x_2278, 0);
lean_inc(x_2279);
x_2280 = lean_ctor_get(x_2278, 1);
lean_inc(x_2280);
lean_dec(x_2278);
x_2262 = x_2279;
x_2263 = x_2280;
goto block_2275;
}
else
{
uint8_t x_2281; 
lean_dec(x_2258);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2281 = !lean_is_exclusive(x_2278);
if (x_2281 == 0)
{
return x_2278;
}
else
{
lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; 
x_2282 = lean_ctor_get(x_2278, 0);
x_2283 = lean_ctor_get(x_2278, 1);
lean_inc(x_2283);
lean_inc(x_2282);
lean_dec(x_2278);
x_2284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2284, 0, x_2282);
lean_ctor_set(x_2284, 1, x_2283);
return x_2284;
}
}
}
else
{
uint8_t x_2285; 
lean_dec(x_2258);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2285 = !lean_is_exclusive(x_2276);
if (x_2285 == 0)
{
return x_2276;
}
else
{
lean_object* x_2286; lean_object* x_2287; lean_object* x_2288; 
x_2286 = lean_ctor_get(x_2276, 0);
x_2287 = lean_ctor_get(x_2276, 1);
lean_inc(x_2287);
lean_inc(x_2286);
lean_dec(x_2276);
x_2288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2288, 0, x_2286);
lean_ctor_set(x_2288, 1, x_2287);
return x_2288;
}
}
}
else
{
lean_object* x_2289; lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; lean_object* x_2295; 
x_2289 = l_Lean_Expr_fvar___override(x_2260);
x_2290 = lean_array_get_size(x_23);
x_2291 = l_Array_toSubarray___rarg(x_23, x_27, x_2290);
x_2292 = l_Array_ofSubarray___rarg(x_2291);
x_2293 = l_Lean_mkAppN(x_2289, x_2292);
x_2294 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2295 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2293, x_2294, x_6, x_7, x_8, x_9, x_2259);
if (lean_obj_tag(x_2295) == 0)
{
lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; 
x_2296 = lean_ctor_get(x_2295, 0);
lean_inc(x_2296);
x_2297 = lean_ctor_get(x_2295, 1);
lean_inc(x_2297);
lean_dec(x_2295);
x_2298 = lean_ctor_get(x_2296, 0);
lean_inc(x_2298);
x_2299 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2298, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2297);
if (lean_obj_tag(x_2299) == 0)
{
lean_object* x_2300; lean_object* x_2301; lean_object* x_2302; 
x_2300 = lean_ctor_get(x_2299, 1);
lean_inc(x_2300);
lean_dec(x_2299);
x_2301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2301, 0, x_2296);
lean_ctor_set(x_2301, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2302 = l_Lean_Compiler_LCNF_Simp_simp(x_2301, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2300);
if (lean_obj_tag(x_2302) == 0)
{
lean_object* x_2303; lean_object* x_2304; 
x_2303 = lean_ctor_get(x_2302, 0);
lean_inc(x_2303);
x_2304 = lean_ctor_get(x_2302, 1);
lean_inc(x_2304);
lean_dec(x_2302);
x_2262 = x_2303;
x_2263 = x_2304;
goto block_2275;
}
else
{
uint8_t x_2305; 
lean_dec(x_2258);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2305 = !lean_is_exclusive(x_2302);
if (x_2305 == 0)
{
return x_2302;
}
else
{
lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; 
x_2306 = lean_ctor_get(x_2302, 0);
x_2307 = lean_ctor_get(x_2302, 1);
lean_inc(x_2307);
lean_inc(x_2306);
lean_dec(x_2302);
x_2308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2308, 0, x_2306);
lean_ctor_set(x_2308, 1, x_2307);
return x_2308;
}
}
}
else
{
uint8_t x_2309; 
lean_dec(x_2296);
lean_dec(x_2258);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2309 = !lean_is_exclusive(x_2299);
if (x_2309 == 0)
{
return x_2299;
}
else
{
lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; 
x_2310 = lean_ctor_get(x_2299, 0);
x_2311 = lean_ctor_get(x_2299, 1);
lean_inc(x_2311);
lean_inc(x_2310);
lean_dec(x_2299);
x_2312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2312, 0, x_2310);
lean_ctor_set(x_2312, 1, x_2311);
return x_2312;
}
}
}
else
{
uint8_t x_2313; 
lean_dec(x_2258);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2313 = !lean_is_exclusive(x_2295);
if (x_2313 == 0)
{
return x_2295;
}
else
{
lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; 
x_2314 = lean_ctor_get(x_2295, 0);
x_2315 = lean_ctor_get(x_2295, 1);
lean_inc(x_2315);
lean_inc(x_2314);
lean_dec(x_2295);
x_2316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2316, 0, x_2314);
lean_ctor_set(x_2316, 1, x_2315);
return x_2316;
}
}
}
block_2275:
{
lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; uint8_t x_2268; 
x_2264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2264, 0, x_2258);
x_2265 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2266 = lean_array_push(x_2265, x_2264);
x_2267 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_2266, x_2262, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2263);
lean_dec(x_2266);
x_2268 = !lean_is_exclusive(x_2267);
if (x_2268 == 0)
{
lean_object* x_2269; lean_object* x_2270; 
x_2269 = lean_ctor_get(x_2267, 0);
if (lean_is_scalar(x_22)) {
 x_2270 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2270 = x_22;
}
lean_ctor_set(x_2270, 0, x_2269);
lean_ctor_set(x_2267, 0, x_2270);
return x_2267;
}
else
{
lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; 
x_2271 = lean_ctor_get(x_2267, 0);
x_2272 = lean_ctor_get(x_2267, 1);
lean_inc(x_2272);
lean_inc(x_2271);
lean_dec(x_2267);
if (lean_is_scalar(x_22)) {
 x_2273 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2273 = x_22;
}
lean_ctor_set(x_2273, 0, x_2271);
x_2274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2274, 0, x_2273);
lean_ctor_set(x_2274, 1, x_2272);
return x_2274;
}
}
}
else
{
uint8_t x_2317; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2317 = !lean_is_exclusive(x_2257);
if (x_2317 == 0)
{
return x_2257;
}
else
{
lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; 
x_2318 = lean_ctor_get(x_2257, 0);
x_2319 = lean_ctor_get(x_2257, 1);
lean_inc(x_2319);
lean_inc(x_2318);
lean_dec(x_2257);
x_2320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2320, 0, x_2318);
lean_ctor_set(x_2320, 1, x_2319);
return x_2320;
}
}
}
else
{
uint8_t x_2321; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2321 = !lean_is_exclusive(x_2254);
if (x_2321 == 0)
{
return x_2254;
}
else
{
lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; 
x_2322 = lean_ctor_get(x_2254, 0);
x_2323 = lean_ctor_get(x_2254, 1);
lean_inc(x_2323);
lean_inc(x_2322);
lean_dec(x_2254);
x_2324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2324, 0, x_2322);
lean_ctor_set(x_2324, 1, x_2323);
return x_2324;
}
}
}
}
else
{
lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; 
lean_dec(x_2161);
x_2325 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2172);
x_2326 = lean_ctor_get(x_2325, 1);
lean_inc(x_2326);
lean_dec(x_2325);
x_2327 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_2327, 0, x_3);
lean_closure_set(x_2327, 1, x_4);
lean_closure_set(x_2327, 2, x_5);
lean_closure_set(x_2327, 3, x_27);
lean_closure_set(x_2327, 4, x_24);
lean_closure_set(x_2327, 5, x_26);
lean_closure_set(x_2327, 6, x_2);
lean_closure_set(x_2327, 7, x_23);
x_2328 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_2171, x_2327, x_6, x_7, x_8, x_9, x_2326);
if (lean_obj_tag(x_2328) == 0)
{
uint8_t x_2329; 
x_2329 = !lean_is_exclusive(x_2328);
if (x_2329 == 0)
{
lean_object* x_2330; lean_object* x_2331; 
x_2330 = lean_ctor_get(x_2328, 0);
if (lean_is_scalar(x_22)) {
 x_2331 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2331 = x_22;
}
lean_ctor_set(x_2331, 0, x_2330);
lean_ctor_set(x_2328, 0, x_2331);
return x_2328;
}
else
{
lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; lean_object* x_2335; 
x_2332 = lean_ctor_get(x_2328, 0);
x_2333 = lean_ctor_get(x_2328, 1);
lean_inc(x_2333);
lean_inc(x_2332);
lean_dec(x_2328);
if (lean_is_scalar(x_22)) {
 x_2334 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2334 = x_22;
}
lean_ctor_set(x_2334, 0, x_2332);
x_2335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2335, 0, x_2334);
lean_ctor_set(x_2335, 1, x_2333);
return x_2335;
}
}
else
{
uint8_t x_2336; 
lean_dec(x_22);
x_2336 = !lean_is_exclusive(x_2328);
if (x_2336 == 0)
{
return x_2328;
}
else
{
lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; 
x_2337 = lean_ctor_get(x_2328, 0);
x_2338 = lean_ctor_get(x_2328, 1);
lean_inc(x_2338);
lean_inc(x_2337);
lean_dec(x_2328);
x_2339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2339, 0, x_2337);
lean_ctor_set(x_2339, 1, x_2338);
return x_2339;
}
}
}
}
else
{
uint8_t x_2340; 
lean_dec(x_2161);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2340 = !lean_is_exclusive(x_2170);
if (x_2340 == 0)
{
return x_2170;
}
else
{
lean_object* x_2341; lean_object* x_2342; lean_object* x_2343; 
x_2341 = lean_ctor_get(x_2170, 0);
x_2342 = lean_ctor_get(x_2170, 1);
lean_inc(x_2342);
lean_inc(x_2341);
lean_dec(x_2170);
x_2343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2343, 0, x_2341);
lean_ctor_set(x_2343, 1, x_2342);
return x_2343;
}
}
}
}
else
{
uint8_t x_2363; 
lean_dec(x_2161);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2363 = !lean_is_exclusive(x_2166);
if (x_2363 == 0)
{
return x_2166;
}
else
{
lean_object* x_2364; lean_object* x_2365; lean_object* x_2366; 
x_2364 = lean_ctor_get(x_2166, 0);
x_2365 = lean_ctor_get(x_2166, 1);
lean_inc(x_2365);
lean_inc(x_2364);
lean_dec(x_2166);
x_2366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2366, 0, x_2364);
lean_ctor_set(x_2366, 1, x_2365);
return x_2366;
}
}
}
else
{
uint8_t x_2367; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2367 = !lean_is_exclusive(x_2160);
if (x_2367 == 0)
{
return x_2160;
}
else
{
lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; 
x_2368 = lean_ctor_get(x_2160, 0);
x_2369 = lean_ctor_get(x_2160, 1);
lean_inc(x_2369);
lean_inc(x_2368);
lean_dec(x_2160);
x_2370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2370, 0, x_2368);
lean_ctor_set(x_2370, 1, x_2369);
return x_2370;
}
}
}
default: 
{
lean_object* x_2371; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2371 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_2371) == 0)
{
lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; uint8_t x_2376; lean_object* x_2377; 
x_2372 = lean_ctor_get(x_2371, 0);
lean_inc(x_2372);
x_2373 = lean_ctor_get(x_2371, 1);
lean_inc(x_2373);
lean_dec(x_2371);
x_2374 = lean_ctor_get(x_21, 0);
lean_inc(x_2374);
x_2375 = lean_ctor_get(x_21, 1);
lean_inc(x_2375);
lean_dec(x_21);
x_2376 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2377 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2374, x_2375, x_32, x_2376, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2373);
lean_dec(x_2374);
if (lean_obj_tag(x_2377) == 0)
{
lean_object* x_2378; lean_object* x_2379; lean_object* x_2380; uint8_t x_2556; 
x_2378 = lean_ctor_get(x_2377, 0);
lean_inc(x_2378);
x_2379 = lean_ctor_get(x_2377, 1);
lean_inc(x_2379);
lean_dec(x_2377);
x_2556 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_2556 == 0)
{
lean_object* x_2557; 
x_2557 = lean_box(0);
x_2380 = x_2557;
goto block_2555;
}
else
{
uint8_t x_2558; 
x_2558 = lean_nat_dec_eq(x_24, x_27);
if (x_2558 == 0)
{
lean_object* x_2559; 
x_2559 = lean_box(0);
x_2380 = x_2559;
goto block_2555;
}
else
{
lean_object* x_2560; lean_object* x_2561; lean_object* x_2562; 
lean_dec(x_2372);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_2560 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2379);
x_2561 = lean_ctor_get(x_2560, 1);
lean_inc(x_2561);
lean_dec(x_2560);
x_2562 = l_Lean_Compiler_LCNF_Simp_simp(x_2378, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2561);
if (lean_obj_tag(x_2562) == 0)
{
uint8_t x_2563; 
x_2563 = !lean_is_exclusive(x_2562);
if (x_2563 == 0)
{
lean_object* x_2564; lean_object* x_2565; 
x_2564 = lean_ctor_get(x_2562, 0);
x_2565 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2565, 0, x_2564);
lean_ctor_set(x_2562, 0, x_2565);
return x_2562;
}
else
{
lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; lean_object* x_2569; 
x_2566 = lean_ctor_get(x_2562, 0);
x_2567 = lean_ctor_get(x_2562, 1);
lean_inc(x_2567);
lean_inc(x_2566);
lean_dec(x_2562);
x_2568 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2568, 0, x_2566);
x_2569 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2569, 0, x_2568);
lean_ctor_set(x_2569, 1, x_2567);
return x_2569;
}
}
else
{
uint8_t x_2570; 
x_2570 = !lean_is_exclusive(x_2562);
if (x_2570 == 0)
{
return x_2562;
}
else
{
lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; 
x_2571 = lean_ctor_get(x_2562, 0);
x_2572 = lean_ctor_get(x_2562, 1);
lean_inc(x_2572);
lean_inc(x_2571);
lean_dec(x_2562);
x_2573 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2573, 0, x_2571);
lean_ctor_set(x_2573, 1, x_2572);
return x_2573;
}
}
}
}
block_2555:
{
lean_object* x_2381; 
lean_dec(x_2380);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2381 = l_Lean_Compiler_LCNF_Simp_simp(x_2378, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2379);
if (lean_obj_tag(x_2381) == 0)
{
lean_object* x_2382; lean_object* x_2383; uint8_t x_2384; 
x_2382 = lean_ctor_get(x_2381, 0);
lean_inc(x_2382);
x_2383 = lean_ctor_get(x_2381, 1);
lean_inc(x_2383);
lean_dec(x_2381);
lean_inc(x_2382);
x_2384 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_2382);
if (x_2384 == 0)
{
lean_object* x_2385; lean_object* x_2386; lean_object* x_2387; uint8_t x_2388; 
x_2385 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2383);
x_2386 = lean_ctor_get(x_2385, 1);
lean_inc(x_2386);
lean_dec(x_2385);
lean_inc(x_2372);
x_2387 = l_Lean_Expr_headBeta(x_2372);
x_2388 = l_Lean_Expr_isForall(x_2387);
lean_dec(x_2387);
if (x_2388 == 0)
{
lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; uint8_t x_2393; lean_object* x_2394; lean_object* x_2395; 
x_2389 = l_Lean_Compiler_LCNF_mkAuxParam(x_2372, x_2376, x_6, x_7, x_8, x_9, x_2386);
x_2390 = lean_ctor_get(x_2389, 0);
lean_inc(x_2390);
x_2391 = lean_ctor_get(x_2389, 1);
lean_inc(x_2391);
lean_dec(x_2389);
x_2392 = lean_ctor_get(x_2390, 0);
lean_inc(x_2392);
x_2393 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_2393 == 0)
{
lean_object* x_2422; 
lean_dec(x_27);
lean_dec(x_23);
x_2422 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2392, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2391);
if (lean_obj_tag(x_2422) == 0)
{
lean_object* x_2423; lean_object* x_2424; 
x_2423 = lean_ctor_get(x_2422, 1);
lean_inc(x_2423);
lean_dec(x_2422);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2424 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2423);
if (lean_obj_tag(x_2424) == 0)
{
lean_object* x_2425; lean_object* x_2426; 
x_2425 = lean_ctor_get(x_2424, 0);
lean_inc(x_2425);
x_2426 = lean_ctor_get(x_2424, 1);
lean_inc(x_2426);
lean_dec(x_2424);
x_2394 = x_2425;
x_2395 = x_2426;
goto block_2421;
}
else
{
uint8_t x_2427; 
lean_dec(x_2390);
lean_dec(x_2382);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2427 = !lean_is_exclusive(x_2424);
if (x_2427 == 0)
{
return x_2424;
}
else
{
lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; 
x_2428 = lean_ctor_get(x_2424, 0);
x_2429 = lean_ctor_get(x_2424, 1);
lean_inc(x_2429);
lean_inc(x_2428);
lean_dec(x_2424);
x_2430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2430, 0, x_2428);
lean_ctor_set(x_2430, 1, x_2429);
return x_2430;
}
}
}
else
{
uint8_t x_2431; 
lean_dec(x_2390);
lean_dec(x_2382);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2431 = !lean_is_exclusive(x_2422);
if (x_2431 == 0)
{
return x_2422;
}
else
{
lean_object* x_2432; lean_object* x_2433; lean_object* x_2434; 
x_2432 = lean_ctor_get(x_2422, 0);
x_2433 = lean_ctor_get(x_2422, 1);
lean_inc(x_2433);
lean_inc(x_2432);
lean_dec(x_2422);
x_2434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2434, 0, x_2432);
lean_ctor_set(x_2434, 1, x_2433);
return x_2434;
}
}
}
else
{
lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; 
x_2435 = l_Lean_Expr_fvar___override(x_2392);
x_2436 = lean_array_get_size(x_23);
x_2437 = l_Array_toSubarray___rarg(x_23, x_27, x_2436);
x_2438 = l_Array_ofSubarray___rarg(x_2437);
x_2439 = l_Lean_mkAppN(x_2435, x_2438);
x_2440 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2441 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2439, x_2440, x_6, x_7, x_8, x_9, x_2391);
if (lean_obj_tag(x_2441) == 0)
{
lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; 
x_2442 = lean_ctor_get(x_2441, 0);
lean_inc(x_2442);
x_2443 = lean_ctor_get(x_2441, 1);
lean_inc(x_2443);
lean_dec(x_2441);
x_2444 = lean_ctor_get(x_2442, 0);
lean_inc(x_2444);
x_2445 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2444, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2443);
if (lean_obj_tag(x_2445) == 0)
{
lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; 
x_2446 = lean_ctor_get(x_2445, 1);
lean_inc(x_2446);
lean_dec(x_2445);
x_2447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2447, 0, x_2442);
lean_ctor_set(x_2447, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2448 = l_Lean_Compiler_LCNF_Simp_simp(x_2447, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2446);
if (lean_obj_tag(x_2448) == 0)
{
lean_object* x_2449; lean_object* x_2450; 
x_2449 = lean_ctor_get(x_2448, 0);
lean_inc(x_2449);
x_2450 = lean_ctor_get(x_2448, 1);
lean_inc(x_2450);
lean_dec(x_2448);
x_2394 = x_2449;
x_2395 = x_2450;
goto block_2421;
}
else
{
uint8_t x_2451; 
lean_dec(x_2390);
lean_dec(x_2382);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2451 = !lean_is_exclusive(x_2448);
if (x_2451 == 0)
{
return x_2448;
}
else
{
lean_object* x_2452; lean_object* x_2453; lean_object* x_2454; 
x_2452 = lean_ctor_get(x_2448, 0);
x_2453 = lean_ctor_get(x_2448, 1);
lean_inc(x_2453);
lean_inc(x_2452);
lean_dec(x_2448);
x_2454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2454, 0, x_2452);
lean_ctor_set(x_2454, 1, x_2453);
return x_2454;
}
}
}
else
{
uint8_t x_2455; 
lean_dec(x_2442);
lean_dec(x_2390);
lean_dec(x_2382);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2455 = !lean_is_exclusive(x_2445);
if (x_2455 == 0)
{
return x_2445;
}
else
{
lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; 
x_2456 = lean_ctor_get(x_2445, 0);
x_2457 = lean_ctor_get(x_2445, 1);
lean_inc(x_2457);
lean_inc(x_2456);
lean_dec(x_2445);
x_2458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2458, 0, x_2456);
lean_ctor_set(x_2458, 1, x_2457);
return x_2458;
}
}
}
else
{
uint8_t x_2459; 
lean_dec(x_2390);
lean_dec(x_2382);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2459 = !lean_is_exclusive(x_2441);
if (x_2459 == 0)
{
return x_2441;
}
else
{
lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; 
x_2460 = lean_ctor_get(x_2441, 0);
x_2461 = lean_ctor_get(x_2441, 1);
lean_inc(x_2461);
lean_inc(x_2460);
lean_dec(x_2441);
x_2462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2462, 0, x_2460);
lean_ctor_set(x_2462, 1, x_2461);
return x_2462;
}
}
}
block_2421:
{
lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; 
x_2396 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2397 = lean_array_push(x_2396, x_2390);
x_2398 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2399 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_2397, x_2394, x_2398, x_6, x_7, x_8, x_9, x_2395);
if (lean_obj_tag(x_2399) == 0)
{
lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; 
x_2400 = lean_ctor_get(x_2399, 0);
lean_inc(x_2400);
x_2401 = lean_ctor_get(x_2399, 1);
lean_inc(x_2401);
lean_dec(x_2399);
lean_inc(x_2400);
x_2402 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_2402, 0, x_2400);
lean_closure_set(x_2402, 1, x_2396);
x_2403 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_2382, x_2402, x_6, x_7, x_8, x_9, x_2401);
if (lean_obj_tag(x_2403) == 0)
{
uint8_t x_2404; 
x_2404 = !lean_is_exclusive(x_2403);
if (x_2404 == 0)
{
lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; 
x_2405 = lean_ctor_get(x_2403, 0);
x_2406 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2406, 0, x_2400);
lean_ctor_set(x_2406, 1, x_2405);
if (lean_is_scalar(x_22)) {
 x_2407 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2407 = x_22;
}
lean_ctor_set(x_2407, 0, x_2406);
lean_ctor_set(x_2403, 0, x_2407);
return x_2403;
}
else
{
lean_object* x_2408; lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; 
x_2408 = lean_ctor_get(x_2403, 0);
x_2409 = lean_ctor_get(x_2403, 1);
lean_inc(x_2409);
lean_inc(x_2408);
lean_dec(x_2403);
x_2410 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2410, 0, x_2400);
lean_ctor_set(x_2410, 1, x_2408);
if (lean_is_scalar(x_22)) {
 x_2411 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2411 = x_22;
}
lean_ctor_set(x_2411, 0, x_2410);
x_2412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2412, 0, x_2411);
lean_ctor_set(x_2412, 1, x_2409);
return x_2412;
}
}
else
{
uint8_t x_2413; 
lean_dec(x_2400);
lean_dec(x_22);
x_2413 = !lean_is_exclusive(x_2403);
if (x_2413 == 0)
{
return x_2403;
}
else
{
lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; 
x_2414 = lean_ctor_get(x_2403, 0);
x_2415 = lean_ctor_get(x_2403, 1);
lean_inc(x_2415);
lean_inc(x_2414);
lean_dec(x_2403);
x_2416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2416, 0, x_2414);
lean_ctor_set(x_2416, 1, x_2415);
return x_2416;
}
}
}
else
{
uint8_t x_2417; 
lean_dec(x_2382);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2417 = !lean_is_exclusive(x_2399);
if (x_2417 == 0)
{
return x_2399;
}
else
{
lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; 
x_2418 = lean_ctor_get(x_2399, 0);
x_2419 = lean_ctor_get(x_2399, 1);
lean_inc(x_2419);
lean_inc(x_2418);
lean_dec(x_2399);
x_2420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2420, 0, x_2418);
lean_ctor_set(x_2420, 1, x_2419);
return x_2420;
}
}
}
}
else
{
lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; 
lean_dec(x_2372);
x_2463 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_2464 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2465 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_2463, x_2382, x_2464, x_6, x_7, x_8, x_9, x_2386);
if (lean_obj_tag(x_2465) == 0)
{
lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; 
x_2466 = lean_ctor_get(x_2465, 0);
lean_inc(x_2466);
x_2467 = lean_ctor_get(x_2465, 1);
lean_inc(x_2467);
lean_dec(x_2465);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2468 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_2466, x_6, x_7, x_8, x_9, x_2467);
if (lean_obj_tag(x_2468) == 0)
{
lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; uint8_t x_2472; lean_object* x_2473; lean_object* x_2474; 
x_2469 = lean_ctor_get(x_2468, 0);
lean_inc(x_2469);
x_2470 = lean_ctor_get(x_2468, 1);
lean_inc(x_2470);
lean_dec(x_2468);
x_2471 = lean_ctor_get(x_2469, 0);
lean_inc(x_2471);
x_2472 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_2472 == 0)
{
lean_object* x_2487; 
lean_dec(x_27);
lean_dec(x_23);
x_2487 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2471, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2470);
if (lean_obj_tag(x_2487) == 0)
{
lean_object* x_2488; lean_object* x_2489; 
x_2488 = lean_ctor_get(x_2487, 1);
lean_inc(x_2488);
lean_dec(x_2487);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2489 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2488);
if (lean_obj_tag(x_2489) == 0)
{
lean_object* x_2490; lean_object* x_2491; 
x_2490 = lean_ctor_get(x_2489, 0);
lean_inc(x_2490);
x_2491 = lean_ctor_get(x_2489, 1);
lean_inc(x_2491);
lean_dec(x_2489);
x_2473 = x_2490;
x_2474 = x_2491;
goto block_2486;
}
else
{
uint8_t x_2492; 
lean_dec(x_2469);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2492 = !lean_is_exclusive(x_2489);
if (x_2492 == 0)
{
return x_2489;
}
else
{
lean_object* x_2493; lean_object* x_2494; lean_object* x_2495; 
x_2493 = lean_ctor_get(x_2489, 0);
x_2494 = lean_ctor_get(x_2489, 1);
lean_inc(x_2494);
lean_inc(x_2493);
lean_dec(x_2489);
x_2495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2495, 0, x_2493);
lean_ctor_set(x_2495, 1, x_2494);
return x_2495;
}
}
}
else
{
uint8_t x_2496; 
lean_dec(x_2469);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2496 = !lean_is_exclusive(x_2487);
if (x_2496 == 0)
{
return x_2487;
}
else
{
lean_object* x_2497; lean_object* x_2498; lean_object* x_2499; 
x_2497 = lean_ctor_get(x_2487, 0);
x_2498 = lean_ctor_get(x_2487, 1);
lean_inc(x_2498);
lean_inc(x_2497);
lean_dec(x_2487);
x_2499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2499, 0, x_2497);
lean_ctor_set(x_2499, 1, x_2498);
return x_2499;
}
}
}
else
{
lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; lean_object* x_2503; lean_object* x_2504; lean_object* x_2505; lean_object* x_2506; 
x_2500 = l_Lean_Expr_fvar___override(x_2471);
x_2501 = lean_array_get_size(x_23);
x_2502 = l_Array_toSubarray___rarg(x_23, x_27, x_2501);
x_2503 = l_Array_ofSubarray___rarg(x_2502);
x_2504 = l_Lean_mkAppN(x_2500, x_2503);
x_2505 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2506 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2504, x_2505, x_6, x_7, x_8, x_9, x_2470);
if (lean_obj_tag(x_2506) == 0)
{
lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; 
x_2507 = lean_ctor_get(x_2506, 0);
lean_inc(x_2507);
x_2508 = lean_ctor_get(x_2506, 1);
lean_inc(x_2508);
lean_dec(x_2506);
x_2509 = lean_ctor_get(x_2507, 0);
lean_inc(x_2509);
x_2510 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2509, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2508);
if (lean_obj_tag(x_2510) == 0)
{
lean_object* x_2511; lean_object* x_2512; lean_object* x_2513; 
x_2511 = lean_ctor_get(x_2510, 1);
lean_inc(x_2511);
lean_dec(x_2510);
x_2512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2512, 0, x_2507);
lean_ctor_set(x_2512, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2513 = l_Lean_Compiler_LCNF_Simp_simp(x_2512, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2511);
if (lean_obj_tag(x_2513) == 0)
{
lean_object* x_2514; lean_object* x_2515; 
x_2514 = lean_ctor_get(x_2513, 0);
lean_inc(x_2514);
x_2515 = lean_ctor_get(x_2513, 1);
lean_inc(x_2515);
lean_dec(x_2513);
x_2473 = x_2514;
x_2474 = x_2515;
goto block_2486;
}
else
{
uint8_t x_2516; 
lean_dec(x_2469);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2516 = !lean_is_exclusive(x_2513);
if (x_2516 == 0)
{
return x_2513;
}
else
{
lean_object* x_2517; lean_object* x_2518; lean_object* x_2519; 
x_2517 = lean_ctor_get(x_2513, 0);
x_2518 = lean_ctor_get(x_2513, 1);
lean_inc(x_2518);
lean_inc(x_2517);
lean_dec(x_2513);
x_2519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2519, 0, x_2517);
lean_ctor_set(x_2519, 1, x_2518);
return x_2519;
}
}
}
else
{
uint8_t x_2520; 
lean_dec(x_2507);
lean_dec(x_2469);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2520 = !lean_is_exclusive(x_2510);
if (x_2520 == 0)
{
return x_2510;
}
else
{
lean_object* x_2521; lean_object* x_2522; lean_object* x_2523; 
x_2521 = lean_ctor_get(x_2510, 0);
x_2522 = lean_ctor_get(x_2510, 1);
lean_inc(x_2522);
lean_inc(x_2521);
lean_dec(x_2510);
x_2523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2523, 0, x_2521);
lean_ctor_set(x_2523, 1, x_2522);
return x_2523;
}
}
}
else
{
uint8_t x_2524; 
lean_dec(x_2469);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2524 = !lean_is_exclusive(x_2506);
if (x_2524 == 0)
{
return x_2506;
}
else
{
lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; 
x_2525 = lean_ctor_get(x_2506, 0);
x_2526 = lean_ctor_get(x_2506, 1);
lean_inc(x_2526);
lean_inc(x_2525);
lean_dec(x_2506);
x_2527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2527, 0, x_2525);
lean_ctor_set(x_2527, 1, x_2526);
return x_2527;
}
}
}
block_2486:
{
lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; uint8_t x_2479; 
x_2475 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2475, 0, x_2469);
x_2476 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2477 = lean_array_push(x_2476, x_2475);
x_2478 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_2477, x_2473, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2474);
lean_dec(x_2477);
x_2479 = !lean_is_exclusive(x_2478);
if (x_2479 == 0)
{
lean_object* x_2480; lean_object* x_2481; 
x_2480 = lean_ctor_get(x_2478, 0);
if (lean_is_scalar(x_22)) {
 x_2481 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2481 = x_22;
}
lean_ctor_set(x_2481, 0, x_2480);
lean_ctor_set(x_2478, 0, x_2481);
return x_2478;
}
else
{
lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; 
x_2482 = lean_ctor_get(x_2478, 0);
x_2483 = lean_ctor_get(x_2478, 1);
lean_inc(x_2483);
lean_inc(x_2482);
lean_dec(x_2478);
if (lean_is_scalar(x_22)) {
 x_2484 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2484 = x_22;
}
lean_ctor_set(x_2484, 0, x_2482);
x_2485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2485, 0, x_2484);
lean_ctor_set(x_2485, 1, x_2483);
return x_2485;
}
}
}
else
{
uint8_t x_2528; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2528 = !lean_is_exclusive(x_2468);
if (x_2528 == 0)
{
return x_2468;
}
else
{
lean_object* x_2529; lean_object* x_2530; lean_object* x_2531; 
x_2529 = lean_ctor_get(x_2468, 0);
x_2530 = lean_ctor_get(x_2468, 1);
lean_inc(x_2530);
lean_inc(x_2529);
lean_dec(x_2468);
x_2531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2531, 0, x_2529);
lean_ctor_set(x_2531, 1, x_2530);
return x_2531;
}
}
}
else
{
uint8_t x_2532; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2532 = !lean_is_exclusive(x_2465);
if (x_2532 == 0)
{
return x_2465;
}
else
{
lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; 
x_2533 = lean_ctor_get(x_2465, 0);
x_2534 = lean_ctor_get(x_2465, 1);
lean_inc(x_2534);
lean_inc(x_2533);
lean_dec(x_2465);
x_2535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2535, 0, x_2533);
lean_ctor_set(x_2535, 1, x_2534);
return x_2535;
}
}
}
}
else
{
lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; 
lean_dec(x_2372);
x_2536 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2383);
x_2537 = lean_ctor_get(x_2536, 1);
lean_inc(x_2537);
lean_dec(x_2536);
x_2538 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_2538, 0, x_3);
lean_closure_set(x_2538, 1, x_4);
lean_closure_set(x_2538, 2, x_5);
lean_closure_set(x_2538, 3, x_27);
lean_closure_set(x_2538, 4, x_24);
lean_closure_set(x_2538, 5, x_26);
lean_closure_set(x_2538, 6, x_2);
lean_closure_set(x_2538, 7, x_23);
x_2539 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_2382, x_2538, x_6, x_7, x_8, x_9, x_2537);
if (lean_obj_tag(x_2539) == 0)
{
uint8_t x_2540; 
x_2540 = !lean_is_exclusive(x_2539);
if (x_2540 == 0)
{
lean_object* x_2541; lean_object* x_2542; 
x_2541 = lean_ctor_get(x_2539, 0);
if (lean_is_scalar(x_22)) {
 x_2542 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2542 = x_22;
}
lean_ctor_set(x_2542, 0, x_2541);
lean_ctor_set(x_2539, 0, x_2542);
return x_2539;
}
else
{
lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; 
x_2543 = lean_ctor_get(x_2539, 0);
x_2544 = lean_ctor_get(x_2539, 1);
lean_inc(x_2544);
lean_inc(x_2543);
lean_dec(x_2539);
if (lean_is_scalar(x_22)) {
 x_2545 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2545 = x_22;
}
lean_ctor_set(x_2545, 0, x_2543);
x_2546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2546, 0, x_2545);
lean_ctor_set(x_2546, 1, x_2544);
return x_2546;
}
}
else
{
uint8_t x_2547; 
lean_dec(x_22);
x_2547 = !lean_is_exclusive(x_2539);
if (x_2547 == 0)
{
return x_2539;
}
else
{
lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; 
x_2548 = lean_ctor_get(x_2539, 0);
x_2549 = lean_ctor_get(x_2539, 1);
lean_inc(x_2549);
lean_inc(x_2548);
lean_dec(x_2539);
x_2550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2550, 0, x_2548);
lean_ctor_set(x_2550, 1, x_2549);
return x_2550;
}
}
}
}
else
{
uint8_t x_2551; 
lean_dec(x_2372);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2551 = !lean_is_exclusive(x_2381);
if (x_2551 == 0)
{
return x_2381;
}
else
{
lean_object* x_2552; lean_object* x_2553; lean_object* x_2554; 
x_2552 = lean_ctor_get(x_2381, 0);
x_2553 = lean_ctor_get(x_2381, 1);
lean_inc(x_2553);
lean_inc(x_2552);
lean_dec(x_2381);
x_2554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2554, 0, x_2552);
lean_ctor_set(x_2554, 1, x_2553);
return x_2554;
}
}
}
}
else
{
uint8_t x_2574; 
lean_dec(x_2372);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2574 = !lean_is_exclusive(x_2377);
if (x_2574 == 0)
{
return x_2377;
}
else
{
lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; 
x_2575 = lean_ctor_get(x_2377, 0);
x_2576 = lean_ctor_get(x_2377, 1);
lean_inc(x_2576);
lean_inc(x_2575);
lean_dec(x_2377);
x_2577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2577, 0, x_2575);
lean_ctor_set(x_2577, 1, x_2576);
return x_2577;
}
}
}
else
{
uint8_t x_2578; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2578 = !lean_is_exclusive(x_2371);
if (x_2578 == 0)
{
return x_2371;
}
else
{
lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; 
x_2579 = lean_ctor_get(x_2371, 0);
x_2580 = lean_ctor_get(x_2371, 1);
lean_inc(x_2580);
lean_inc(x_2579);
lean_dec(x_2371);
x_2581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2581, 0, x_2579);
lean_ctor_set(x_2581, 1, x_2580);
return x_2581;
}
}
}
}
}
else
{
lean_object* x_2582; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
x_2582 = l_Lean_Expr_getAppFn(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_2582) == 4)
{
lean_object* x_2583; lean_object* x_2584; 
x_2583 = lean_ctor_get(x_2582, 0);
lean_inc(x_2583);
lean_dec(x_2582);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2583);
x_2584 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_2583, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_2584) == 0)
{
lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; 
x_2585 = lean_ctor_get(x_2584, 0);
lean_inc(x_2585);
x_2586 = lean_ctor_get(x_2584, 1);
lean_inc(x_2586);
lean_dec(x_2584);
x_2587 = lean_ctor_get(x_3, 0);
lean_inc(x_2587);
x_2588 = lean_ctor_get(x_3, 1);
lean_inc(x_2588);
x_2589 = lean_ctor_get(x_3, 2);
lean_inc(x_2589);
lean_inc(x_2583);
x_2590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2590, 0, x_2583);
lean_ctor_set(x_2590, 1, x_2589);
x_2591 = lean_ctor_get(x_3, 3);
lean_inc(x_2591);
lean_dec(x_3);
x_2592 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_2591, x_2583, x_2585);
x_2593 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2593, 0, x_2587);
lean_ctor_set(x_2593, 1, x_2588);
lean_ctor_set(x_2593, 2, x_2590);
lean_ctor_set(x_2593, 3, x_2592);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2594 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_2593, x_4, x_5, x_6, x_7, x_8, x_9, x_2586);
if (lean_obj_tag(x_2594) == 0)
{
lean_object* x_2595; lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; 
x_2595 = lean_ctor_get(x_2594, 0);
lean_inc(x_2595);
x_2596 = lean_ctor_get(x_2594, 1);
lean_inc(x_2596);
lean_dec(x_2594);
x_2597 = lean_ctor_get(x_2595, 0);
lean_inc(x_2597);
x_2598 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2597, x_2593, x_4, x_5, x_6, x_7, x_8, x_9, x_2596);
if (lean_obj_tag(x_2598) == 0)
{
lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; lean_object* x_2603; 
x_2599 = lean_ctor_get(x_2598, 1);
lean_inc(x_2599);
lean_dec(x_2598);
x_2600 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2599);
x_2601 = lean_ctor_get(x_2600, 1);
lean_inc(x_2601);
lean_dec(x_2600);
x_2602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2602, 0, x_2595);
lean_ctor_set(x_2602, 1, x_2);
x_2603 = l_Lean_Compiler_LCNF_Simp_simp(x_2602, x_2593, x_4, x_5, x_6, x_7, x_8, x_9, x_2601);
if (lean_obj_tag(x_2603) == 0)
{
uint8_t x_2604; 
x_2604 = !lean_is_exclusive(x_2603);
if (x_2604 == 0)
{
lean_object* x_2605; lean_object* x_2606; 
x_2605 = lean_ctor_get(x_2603, 0);
if (lean_is_scalar(x_22)) {
 x_2606 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2606 = x_22;
}
lean_ctor_set(x_2606, 0, x_2605);
lean_ctor_set(x_2603, 0, x_2606);
return x_2603;
}
else
{
lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; 
x_2607 = lean_ctor_get(x_2603, 0);
x_2608 = lean_ctor_get(x_2603, 1);
lean_inc(x_2608);
lean_inc(x_2607);
lean_dec(x_2603);
if (lean_is_scalar(x_22)) {
 x_2609 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2609 = x_22;
}
lean_ctor_set(x_2609, 0, x_2607);
x_2610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2610, 0, x_2609);
lean_ctor_set(x_2610, 1, x_2608);
return x_2610;
}
}
else
{
uint8_t x_2611; 
lean_dec(x_22);
x_2611 = !lean_is_exclusive(x_2603);
if (x_2611 == 0)
{
return x_2603;
}
else
{
lean_object* x_2612; lean_object* x_2613; lean_object* x_2614; 
x_2612 = lean_ctor_get(x_2603, 0);
x_2613 = lean_ctor_get(x_2603, 1);
lean_inc(x_2613);
lean_inc(x_2612);
lean_dec(x_2603);
x_2614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2614, 0, x_2612);
lean_ctor_set(x_2614, 1, x_2613);
return x_2614;
}
}
}
else
{
uint8_t x_2615; 
lean_dec(x_2595);
lean_dec(x_2593);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2615 = !lean_is_exclusive(x_2598);
if (x_2615 == 0)
{
return x_2598;
}
else
{
lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; 
x_2616 = lean_ctor_get(x_2598, 0);
x_2617 = lean_ctor_get(x_2598, 1);
lean_inc(x_2617);
lean_inc(x_2616);
lean_dec(x_2598);
x_2618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2618, 0, x_2616);
lean_ctor_set(x_2618, 1, x_2617);
return x_2618;
}
}
}
else
{
uint8_t x_2619; 
lean_dec(x_2593);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2619 = !lean_is_exclusive(x_2594);
if (x_2619 == 0)
{
return x_2594;
}
else
{
lean_object* x_2620; lean_object* x_2621; lean_object* x_2622; 
x_2620 = lean_ctor_get(x_2594, 0);
x_2621 = lean_ctor_get(x_2594, 1);
lean_inc(x_2621);
lean_inc(x_2620);
lean_dec(x_2594);
x_2622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2622, 0, x_2620);
lean_ctor_set(x_2622, 1, x_2621);
return x_2622;
}
}
}
else
{
uint8_t x_2623; 
lean_dec(x_2583);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2623 = !lean_is_exclusive(x_2584);
if (x_2623 == 0)
{
return x_2584;
}
else
{
lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; 
x_2624 = lean_ctor_get(x_2584, 0);
x_2625 = lean_ctor_get(x_2584, 1);
lean_inc(x_2625);
lean_inc(x_2624);
lean_dec(x_2584);
x_2626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2626, 0, x_2624);
lean_ctor_set(x_2626, 1, x_2625);
return x_2626;
}
}
}
else
{
lean_object* x_2627; 
lean_dec(x_2582);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2627 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_2627) == 0)
{
lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; 
x_2628 = lean_ctor_get(x_2627, 0);
lean_inc(x_2628);
x_2629 = lean_ctor_get(x_2627, 1);
lean_inc(x_2629);
lean_dec(x_2627);
x_2630 = lean_ctor_get(x_2628, 0);
lean_inc(x_2630);
x_2631 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2630, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2629);
if (lean_obj_tag(x_2631) == 0)
{
lean_object* x_2632; lean_object* x_2633; lean_object* x_2634; lean_object* x_2635; lean_object* x_2636; 
x_2632 = lean_ctor_get(x_2631, 1);
lean_inc(x_2632);
lean_dec(x_2631);
x_2633 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2632);
x_2634 = lean_ctor_get(x_2633, 1);
lean_inc(x_2634);
lean_dec(x_2633);
x_2635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2635, 0, x_2628);
lean_ctor_set(x_2635, 1, x_2);
x_2636 = l_Lean_Compiler_LCNF_Simp_simp(x_2635, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2634);
if (lean_obj_tag(x_2636) == 0)
{
uint8_t x_2637; 
x_2637 = !lean_is_exclusive(x_2636);
if (x_2637 == 0)
{
lean_object* x_2638; lean_object* x_2639; 
x_2638 = lean_ctor_get(x_2636, 0);
if (lean_is_scalar(x_22)) {
 x_2639 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2639 = x_22;
}
lean_ctor_set(x_2639, 0, x_2638);
lean_ctor_set(x_2636, 0, x_2639);
return x_2636;
}
else
{
lean_object* x_2640; lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; 
x_2640 = lean_ctor_get(x_2636, 0);
x_2641 = lean_ctor_get(x_2636, 1);
lean_inc(x_2641);
lean_inc(x_2640);
lean_dec(x_2636);
if (lean_is_scalar(x_22)) {
 x_2642 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2642 = x_22;
}
lean_ctor_set(x_2642, 0, x_2640);
x_2643 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2643, 0, x_2642);
lean_ctor_set(x_2643, 1, x_2641);
return x_2643;
}
}
else
{
uint8_t x_2644; 
lean_dec(x_22);
x_2644 = !lean_is_exclusive(x_2636);
if (x_2644 == 0)
{
return x_2636;
}
else
{
lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; 
x_2645 = lean_ctor_get(x_2636, 0);
x_2646 = lean_ctor_get(x_2636, 1);
lean_inc(x_2646);
lean_inc(x_2645);
lean_dec(x_2636);
x_2647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2647, 0, x_2645);
lean_ctor_set(x_2647, 1, x_2646);
return x_2647;
}
}
}
else
{
uint8_t x_2648; 
lean_dec(x_2628);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2648 = !lean_is_exclusive(x_2631);
if (x_2648 == 0)
{
return x_2631;
}
else
{
lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; 
x_2649 = lean_ctor_get(x_2631, 0);
x_2650 = lean_ctor_get(x_2631, 1);
lean_inc(x_2650);
lean_inc(x_2649);
lean_dec(x_2631);
x_2651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2651, 0, x_2649);
lean_ctor_set(x_2651, 1, x_2650);
return x_2651;
}
}
}
else
{
uint8_t x_2652; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2652 = !lean_is_exclusive(x_2627);
if (x_2652 == 0)
{
return x_2627;
}
else
{
lean_object* x_2653; lean_object* x_2654; lean_object* x_2655; 
x_2653 = lean_ctor_get(x_2627, 0);
x_2654 = lean_ctor_get(x_2627, 1);
lean_inc(x_2654);
lean_inc(x_2653);
lean_dec(x_2627);
x_2655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2655, 0, x_2653);
lean_ctor_set(x_2655, 1, x_2654);
return x_2655;
}
}
}
}
}
}
else
{
uint8_t x_2656; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2656 = !lean_is_exclusive(x_12);
if (x_2656 == 0)
{
return x_12;
}
else
{
lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; 
x_2657 = lean_ctor_get(x_12, 0);
x_2658 = lean_ctor_get(x_12, 1);
lean_inc(x_2658);
lean_inc(x_2657);
lean_dec(x_12);
x_2659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2659, 0, x_2657);
lean_ctor_set(x_2659, 1, x_2658);
return x_2659;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_st_ref_get(x_9, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_17, x_1, x_11);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
x_20 = lean_st_ref_get(x_9, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_4, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_25, x_1, x_19);
x_27 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(x_2, x_18, x_26, x_6, x_7, x_8, x_9, x_24);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_16, x_1, x_2);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_20, x_1, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_16 = lean_apply_9(x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ptr_addr(x_15);
lean_dec(x_15);
x_20 = lean_ptr_addr(x_17);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
x_24 = lean_array_fset(x_3, x_2, x_17);
lean_dec(x_2);
x_2 = x_23;
x_3 = x_24;
x_11 = x_18;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_2, x_26);
lean_dec(x_2);
x_2 = x_27;
x_11 = x_18;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(x_2, x_11, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed), 10, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Compiler_LCNF_isInductiveWithNoCtors(x_14, x_9, x_10, x_11);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_11 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_11);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_16 = lean_apply_9(x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ptr_addr(x_15);
lean_dec(x_15);
x_20 = lean_ptr_addr(x_17);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
x_24 = lean_array_fset(x_3, x_2, x_17);
lean_dec(x_2);
x_2 = x_23;
x_3 = x_24;
x_11 = x_18;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_2, x_26);
lean_dec(x_2);
x_2 = x_27;
x_11 = x_18;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__8(x_2, x_11, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_dec(x_5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_14 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_17 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_4, 3);
lean_inc(x_20);
x_21 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_4);
x_24 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_4, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_30 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
x_34 = l_Lean_Compiler_LCNF_Simp_isUsed(x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_31);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
lean_inc(x_4);
x_44 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_43);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; size_t x_47; size_t x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_48 = lean_ptr_addr(x_31);
x_49 = lean_usize_dec_eq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_31);
lean_ctor_set(x_44, 0, x_50);
return x_44;
}
else
{
size_t x_51; size_t x_52; uint8_t x_53; 
x_51 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_52 = lean_ptr_addr(x_4);
x_53 = lean_usize_dec_eq(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_3);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_31);
lean_ctor_set(x_44, 0, x_54);
return x_44;
}
else
{
lean_dec(x_31);
lean_dec(x_4);
lean_ctor_set(x_44, 0, x_3);
return x_44;
}
}
}
else
{
lean_object* x_55; size_t x_56; size_t x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
lean_dec(x_44);
x_56 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_57 = lean_ptr_addr(x_31);
x_58 = lean_usize_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_31);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
else
{
size_t x_61; size_t x_62; uint8_t x_63; 
x_61 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_62 = lean_ptr_addr(x_4);
x_63 = lean_usize_dec_eq(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_3);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_4);
lean_ctor_set(x_64, 1, x_31);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_55);
return x_65;
}
else
{
lean_object* x_66; 
lean_dec(x_31);
lean_dec(x_4);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_3);
lean_ctor_set(x_66, 1, x_55);
return x_66;
}
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_30);
if (x_67 == 0)
{
return x_30;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_30, 0);
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_30);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_28, 0);
lean_inc(x_71);
lean_dec(x_28);
x_72 = lean_ctor_get(x_27, 1);
lean_inc(x_72);
lean_dec(x_27);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_ctor_get(x_4, 0);
lean_inc(x_75);
x_76 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_75, x_74, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_72);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_77);
lean_dec(x_4);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_80 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_73, x_81, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_82);
lean_dec(x_73);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_73);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
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
lean_dec(x_73);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_76);
if (x_88 == 0)
{
return x_76;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_76, 0);
x_90 = lean_ctor_get(x_76, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_76);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_27);
if (x_92 == 0)
{
return x_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_27, 0);
x_94 = lean_ctor_get(x_27, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_27);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_ctor_get(x_24, 1);
lean_inc(x_96);
lean_dec(x_24);
x_97 = lean_ctor_get(x_25, 0);
lean_inc(x_97);
lean_dec(x_25);
x_98 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_96);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_97);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_24);
if (x_103 == 0)
{
return x_24;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_24, 0);
x_105 = lean_ctor_get(x_24, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_24);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
x_107 = lean_ctor_get(x_21, 1);
lean_inc(x_107);
lean_dec(x_21);
x_108 = lean_ctor_get(x_22, 0);
lean_inc(x_108);
lean_dec(x_22);
x_109 = lean_ctor_get(x_4, 0);
lean_inc(x_109);
x_110 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_109, x_108, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_107);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_111);
lean_dec(x_4);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_113);
return x_114;
}
else
{
uint8_t x_115; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_110);
if (x_115 == 0)
{
return x_110;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_110, 0);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_110);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = lean_ctor_get(x_17, 1);
lean_inc(x_119);
lean_dec(x_17);
x_120 = lean_ctor_get(x_18, 0);
lean_inc(x_120);
lean_dec(x_18);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_1);
x_122 = l_Lean_Compiler_LCNF_Simp_simp(x_121, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_119);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_17);
if (x_123 == 0)
{
return x_17;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_17, 0);
x_125 = lean_ctor_get(x_17, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_17);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_ctor_get(x_14, 1);
lean_inc(x_127);
lean_dec(x_14);
x_128 = lean_ctor_get(x_15, 0);
lean_inc(x_128);
lean_dec(x_15);
x_129 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_127);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_131 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_128, x_132, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_133);
lean_dec(x_128);
return x_134;
}
else
{
uint8_t x_135; 
lean_dec(x_128);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_135 = !lean_is_exclusive(x_131);
if (x_135 == 0)
{
return x_131;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_131, 0);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_131);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_14);
if (x_139 == 0)
{
return x_14;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_14, 0);
x_141 = lean_ctor_get(x_14, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_14);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_ptr_addr(x_1);
x_16 = lean_ptr_addr(x_2);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_4);
x_21 = lean_ptr_addr(x_3);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_dec(x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = l_Lean_Compiler_LCNF_Simp_isUsed(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_16);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_16, x_5, x_2, x_3, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_32 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_16, x_5, x_2, x_3, x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_34);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_33);
lean_dec(x_2);
lean_dec(x_1);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_apply_10(x_1, x_13, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_ptr_addr(x_1);
x_16 = lean_ptr_addr(x_2);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_4);
x_21 = lean_ptr_addr(x_3);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_dec(x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = l_Lean_Compiler_LCNF_Simp_isUsed(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_16);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_16, x_5, x_2, x_3, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_32 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_16, x_5, x_2, x_3, x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_34);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_33);
lean_dec(x_2);
lean_dec(x_1);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_array_get_size(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
uint8_t x_79; 
lean_dec(x_14);
x_79 = 0;
x_17 = x_79;
x_18 = x_10;
goto block_78;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_14, x_14);
if (x_80 == 0)
{
uint8_t x_81; 
lean_dec(x_14);
x_81 = 0;
x_17 = x_81;
x_18 = x_10;
goto block_78;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_84 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_12, x_82, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_17 = x_87;
x_18 = x_86;
goto block_78;
}
}
block_78:
{
lean_object* x_19; 
if (lean_obj_tag(x_13) == 6)
{
lean_object* x_58; 
lean_inc(x_9);
lean_inc(x_8);
x_58 = l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Compiler_LCNF_Simp_simp(x_13, x_3, x_4, x_59, x_6, x_7, x_8, x_9, x_60);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_63);
lean_ctor_set(x_61, 0, x_64);
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_67 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
return x_61;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_61, 0);
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_61);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_58);
if (x_73 == 0)
{
return x_58;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_58, 0);
x_75 = lean_ctor_get(x_58, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_58);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; 
x_77 = lean_box(0);
x_19 = x_77;
goto block_57;
}
block_57:
{
lean_dec(x_19);
if (x_17 == 0)
{
lean_object* x_20; 
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Compiler_LCNF_Simp_simp(x_13, x_3, x_4, x_21, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_39 = l_Lean_Compiler_LCNF_Code_inferType(x_13, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_LCNF_eraseCode(x_13, x_6, x_7, x_8, x_9, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_47, 0, x_40);
x_48 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_47);
lean_ctor_set(x_44, 0, x_48);
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_50, 0, x_40);
x_51 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_39);
if (x_53 == 0)
{
return x_39;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_39, 0);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_39);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_1);
x_88 = lean_ctor_get(x_2, 0);
lean_inc(x_88);
x_89 = l_Lean_Compiler_LCNF_Simp_simp(x_88, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_91);
lean_ctor_set(x_89, 0, x_92);
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_89);
x_95 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
return x_89;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_89, 0);
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_89);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 8);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 9);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 10);
lean_inc(x_20);
x_21 = lean_nat_dec_eq(x_13, x_14);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_7, 10);
lean_dec(x_23);
x_24 = lean_ctor_get(x_7, 9);
lean_dec(x_24);
x_25 = lean_ctor_get(x_7, 8);
lean_dec(x_25);
x_26 = lean_ctor_get(x_7, 7);
lean_dec(x_26);
x_27 = lean_ctor_get(x_7, 6);
lean_dec(x_27);
x_28 = lean_ctor_get(x_7, 5);
lean_dec(x_28);
x_29 = lean_ctor_get(x_7, 4);
lean_dec(x_29);
x_30 = lean_ctor_get(x_7, 3);
lean_dec(x_30);
x_31 = lean_ctor_get(x_7, 2);
lean_dec(x_31);
x_32 = lean_ctor_get(x_7, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_7, 0);
lean_dec(x_33);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_13, x_34);
lean_dec(x_13);
lean_ctor_set(x_7, 3, x_35);
x_36 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = 0;
lean_inc(x_38);
x_41 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_40, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 3);
lean_inc(x_44);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_45 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(0);
x_49 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_39, x_38, x_1, x_42, x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
x_52 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_50);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_42, x_51, x_5, x_6, x_7, x_8, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_box(0);
x_58 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_39, x_38, x_1, x_55, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
return x_45;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_45, 0);
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_45);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 1:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_63 = lean_ctor_get(x_36, 1);
lean_inc(x_63);
lean_dec(x_36);
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
lean_inc(x_1);
lean_inc(x_64);
x_71 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed), 14, 4);
lean_closure_set(x_71, 0, x_65);
lean_closure_set(x_71, 1, x_64);
lean_closure_set(x_71, 2, x_1);
lean_closure_set(x_71, 3, x_68);
x_72 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_box(0);
x_74 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_71, x_64, x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_70);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_64, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_64, 2);
lean_inc(x_76);
x_77 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_75, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_box(0);
x_79 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_71, x_64, x_78, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_70);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_80 = lean_st_ref_get(x_8, x_70);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_get(x_3, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_87 = l_Lean_Compiler_LCNF_normFunDeclImp(x_86, x_64, x_85, x_5, x_6, x_7, x_8, x_84);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_90 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_88, x_5, x_6, x_7, x_8, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_71, x_91, x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_95);
lean_dec(x_94);
return x_96;
}
else
{
uint8_t x_97; 
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_90);
if (x_97 == 0)
{
return x_90;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_90, 0);
x_99 = lean_ctor_get(x_90, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_90);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_87);
if (x_101 == 0)
{
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_87, 0);
x_103 = lean_ctor_get(x_87, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_87);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_67, 1);
lean_inc(x_105);
lean_dec(x_67);
x_106 = lean_st_ref_get(x_8, x_105);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_get(x_3, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_64);
x_113 = l_Lean_Compiler_LCNF_normFunDeclImp(x_112, x_64, x_111, x_5, x_6, x_7, x_8, x_110);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_box(0);
x_117 = lean_unbox(x_68);
lean_dec(x_68);
x_118 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_65, x_64, x_1, x_117, x_114, x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_115);
return x_118;
}
else
{
uint8_t x_119; 
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
case 2:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_123 = lean_ctor_get(x_36, 1);
lean_inc(x_123);
lean_dec(x_36);
x_124 = lean_ctor_get(x_1, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_1, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_126, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_123);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
lean_inc(x_1);
lean_inc(x_124);
x_131 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 14, 4);
lean_closure_set(x_131, 0, x_125);
lean_closure_set(x_131, 1, x_124);
lean_closure_set(x_131, 2, x_1);
lean_closure_set(x_131, 3, x_128);
x_132 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_box(0);
x_134 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_131, x_124, x_133, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_130);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_124, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_124, 2);
lean_inc(x_136);
x_137 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_135, x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_box(0);
x_139 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_131, x_124, x_138, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_130);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_140 = lean_st_ref_get(x_8, x_130);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_st_ref_get(x_3, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
lean_dec(x_143);
x_146 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_147 = l_Lean_Compiler_LCNF_normFunDeclImp(x_146, x_124, x_145, x_5, x_6, x_7, x_8, x_144);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_150 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_148, x_5, x_6, x_7, x_8, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_131, x_151, x_154, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_155);
lean_dec(x_154);
return x_156;
}
else
{
uint8_t x_157; 
lean_dec(x_131);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_150);
if (x_157 == 0)
{
return x_150;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_150, 0);
x_159 = lean_ctor_get(x_150, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_150);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_131);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_161 = !lean_is_exclusive(x_147);
if (x_161 == 0)
{
return x_147;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_147, 0);
x_163 = lean_ctor_get(x_147, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_147);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_165 = lean_ctor_get(x_127, 1);
lean_inc(x_165);
lean_dec(x_127);
x_166 = lean_st_ref_get(x_8, x_165);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_st_ref_get(x_3, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec(x_169);
x_172 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_124);
x_173 = l_Lean_Compiler_LCNF_normFunDeclImp(x_172, x_124, x_171, x_5, x_6, x_7, x_8, x_170);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_box(0);
x_177 = lean_unbox(x_128);
lean_dec(x_128);
x_178 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_125, x_124, x_1, x_177, x_174, x_176, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_175);
return x_178;
}
else
{
uint8_t x_179; 
lean_dec(x_128);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_173);
if (x_179 == 0)
{
return x_173;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_173, 0);
x_181 = lean_ctor_get(x_173, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_173);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
case 3:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; 
x_183 = lean_ctor_get(x_36, 1);
lean_inc(x_183);
lean_dec(x_36);
x_184 = lean_ctor_get(x_1, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_1, 1);
lean_inc(x_185);
x_186 = lean_st_ref_get(x_8, x_183);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_188 = lean_st_ref_get(x_3, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
lean_dec(x_189);
x_192 = 0;
lean_inc(x_184);
x_193 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_191, x_184, x_192);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_185);
x_194 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_192, x_185, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_190);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_217; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_195);
lean_inc(x_193);
x_217 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_193, x_195, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_196);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_193);
x_220 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_193, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_219);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_array_get_size(x_195);
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_nat_dec_lt(x_223, x_222);
if (x_224 == 0)
{
lean_dec(x_222);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_198 = x_221;
goto block_216;
}
else
{
uint8_t x_225; 
x_225 = lean_nat_dec_le(x_222, x_222);
if (x_225 == 0)
{
lean_dec(x_222);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_198 = x_221;
goto block_216;
}
else
{
size_t x_226; size_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = 0;
x_227 = lean_usize_of_nat(x_222);
lean_dec(x_222);
x_228 = lean_box(0);
x_229 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_195, x_226, x_227, x_228, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_221);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_198 = x_230;
goto block_216;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_1);
x_231 = lean_ctor_get(x_217, 1);
lean_inc(x_231);
lean_dec(x_217);
x_232 = lean_ctor_get(x_218, 0);
lean_inc(x_232);
lean_dec(x_218);
x_1 = x_232;
x_9 = x_231;
goto _start;
}
}
else
{
uint8_t x_234; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_217);
if (x_234 == 0)
{
return x_217;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_217, 0);
x_236 = lean_ctor_get(x_217, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_217);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
block_216:
{
uint8_t x_199; 
x_199 = lean_name_eq(x_184, x_193);
lean_dec(x_184);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_185);
x_200 = !lean_is_exclusive(x_1);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_1, 1);
lean_dec(x_201);
x_202 = lean_ctor_get(x_1, 0);
lean_dec(x_202);
lean_ctor_set(x_1, 1, x_195);
lean_ctor_set(x_1, 0, x_193);
if (lean_is_scalar(x_197)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_197;
}
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_198);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_1);
x_204 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_204, 0, x_193);
lean_ctor_set(x_204, 1, x_195);
if (lean_is_scalar(x_197)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_197;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_198);
return x_205;
}
}
else
{
size_t x_206; size_t x_207; uint8_t x_208; 
x_206 = lean_ptr_addr(x_185);
lean_dec(x_185);
x_207 = lean_ptr_addr(x_195);
x_208 = lean_usize_dec_eq(x_206, x_207);
if (x_208 == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_1);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_1, 1);
lean_dec(x_210);
x_211 = lean_ctor_get(x_1, 0);
lean_dec(x_211);
lean_ctor_set(x_1, 1, x_195);
lean_ctor_set(x_1, 0, x_193);
if (lean_is_scalar(x_197)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_197;
}
lean_ctor_set(x_212, 0, x_1);
lean_ctor_set(x_212, 1, x_198);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_1);
x_213 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_213, 0, x_193);
lean_ctor_set(x_213, 1, x_195);
if (lean_is_scalar(x_197)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_197;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_198);
return x_214;
}
}
else
{
lean_object* x_215; 
lean_dec(x_195);
lean_dec(x_193);
if (lean_is_scalar(x_197)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_197;
}
lean_ctor_set(x_215, 0, x_1);
lean_ctor_set(x_215, 1, x_198);
return x_215;
}
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_193);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_194);
if (x_238 == 0)
{
return x_194;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_194, 0);
x_240 = lean_ctor_get(x_194, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_194);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
case 4:
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_36, 1);
lean_inc(x_242);
lean_dec(x_36);
x_243 = lean_ctor_get(x_1, 0);
lean_inc(x_243);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_243);
x_244 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_243, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_242);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_243, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_243, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_243, 2);
lean_inc(x_249);
x_250 = lean_ctor_get(x_243, 3);
lean_inc(x_250);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 lean_ctor_release(x_243, 3);
 x_251 = x_243;
} else {
 lean_dec_ref(x_243);
 x_251 = lean_box(0);
}
x_252 = lean_st_ref_get(x_8, x_246);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_254 = lean_st_ref_get(x_3, x_253);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_ctor_get(x_255, 0);
lean_inc(x_257);
lean_dec(x_255);
x_258 = 0;
lean_inc(x_249);
x_259 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_257, x_249, x_258);
x_260 = lean_st_ref_get(x_8, x_256);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_262 = lean_st_ref_get(x_3, x_261);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_ctor_get(x_263, 0);
lean_inc(x_265);
lean_dec(x_263);
lean_inc(x_248);
x_266 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_265, x_258, x_248);
lean_inc(x_259);
x_267 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_259, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_264);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
lean_inc(x_259);
x_269 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7), 10, 1);
lean_closure_set(x_269, 0, x_259);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_250);
x_270 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__7(x_250, x_269, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_268);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_273 = x_270;
} else {
 lean_dec_ref(x_270);
 x_273 = lean_box(0);
}
x_274 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_271, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_272);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_309; lean_object* x_310; uint8_t x_321; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_277 = x_274;
} else {
 lean_dec_ref(x_274);
 x_277 = lean_box(0);
}
x_309 = lean_array_get_size(x_275);
x_321 = lean_nat_dec_eq(x_309, x_34);
if (x_321 == 0)
{
lean_object* x_322; 
lean_dec(x_309);
lean_dec(x_273);
x_322 = lean_box(0);
x_278 = x_322;
goto block_308;
}
else
{
lean_object* x_323; uint8_t x_324; 
x_323 = lean_unsigned_to_nat(0u);
x_324 = lean_nat_dec_lt(x_323, x_309);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; 
x_325 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_326 = l___private_Init_Util_0__outOfBounds___rarg(x_325);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
lean_dec(x_326);
lean_dec(x_309);
lean_dec(x_273);
x_327 = lean_box(0);
x_278 = x_327;
goto block_308;
}
else
{
lean_object* x_328; 
lean_dec(x_326);
lean_dec(x_277);
lean_dec(x_266);
lean_dec(x_259);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_1);
x_328 = lean_box(0);
x_310 = x_328;
goto block_320;
}
}
else
{
lean_object* x_329; 
x_329 = lean_array_fget(x_275, x_323);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; 
lean_dec(x_329);
lean_dec(x_309);
lean_dec(x_273);
x_330 = lean_box(0);
x_278 = x_330;
goto block_308;
}
else
{
lean_object* x_331; 
lean_dec(x_329);
lean_dec(x_277);
lean_dec(x_266);
lean_dec(x_259);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_1);
x_331 = lean_box(0);
x_310 = x_331;
goto block_320;
}
}
}
block_308:
{
size_t x_279; size_t x_280; uint8_t x_281; 
lean_dec(x_278);
x_279 = lean_ptr_addr(x_250);
lean_dec(x_250);
x_280 = lean_ptr_addr(x_275);
x_281 = lean_usize_dec_eq(x_279, x_280);
if (x_281 == 0)
{
uint8_t x_282; 
lean_dec(x_249);
lean_dec(x_248);
x_282 = !lean_is_exclusive(x_1);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_1, 0);
lean_dec(x_283);
if (lean_is_scalar(x_251)) {
 x_284 = lean_alloc_ctor(0, 4, 0);
} else {
 x_284 = x_251;
}
lean_ctor_set(x_284, 0, x_247);
lean_ctor_set(x_284, 1, x_266);
lean_ctor_set(x_284, 2, x_259);
lean_ctor_set(x_284, 3, x_275);
lean_ctor_set(x_1, 0, x_284);
if (lean_is_scalar(x_277)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_277;
}
lean_ctor_set(x_285, 0, x_1);
lean_ctor_set(x_285, 1, x_276);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_1);
if (lean_is_scalar(x_251)) {
 x_286 = lean_alloc_ctor(0, 4, 0);
} else {
 x_286 = x_251;
}
lean_ctor_set(x_286, 0, x_247);
lean_ctor_set(x_286, 1, x_266);
lean_ctor_set(x_286, 2, x_259);
lean_ctor_set(x_286, 3, x_275);
x_287 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_287, 0, x_286);
if (lean_is_scalar(x_277)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_277;
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_276);
return x_288;
}
}
else
{
size_t x_289; size_t x_290; uint8_t x_291; 
x_289 = lean_ptr_addr(x_248);
lean_dec(x_248);
x_290 = lean_ptr_addr(x_266);
x_291 = lean_usize_dec_eq(x_289, x_290);
if (x_291 == 0)
{
uint8_t x_292; 
lean_dec(x_249);
x_292 = !lean_is_exclusive(x_1);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_1, 0);
lean_dec(x_293);
if (lean_is_scalar(x_251)) {
 x_294 = lean_alloc_ctor(0, 4, 0);
} else {
 x_294 = x_251;
}
lean_ctor_set(x_294, 0, x_247);
lean_ctor_set(x_294, 1, x_266);
lean_ctor_set(x_294, 2, x_259);
lean_ctor_set(x_294, 3, x_275);
lean_ctor_set(x_1, 0, x_294);
if (lean_is_scalar(x_277)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_277;
}
lean_ctor_set(x_295, 0, x_1);
lean_ctor_set(x_295, 1, x_276);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_1);
if (lean_is_scalar(x_251)) {
 x_296 = lean_alloc_ctor(0, 4, 0);
} else {
 x_296 = x_251;
}
lean_ctor_set(x_296, 0, x_247);
lean_ctor_set(x_296, 1, x_266);
lean_ctor_set(x_296, 2, x_259);
lean_ctor_set(x_296, 3, x_275);
x_297 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_297, 0, x_296);
if (lean_is_scalar(x_277)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_277;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_276);
return x_298;
}
}
else
{
uint8_t x_299; 
x_299 = lean_name_eq(x_249, x_259);
lean_dec(x_249);
if (x_299 == 0)
{
uint8_t x_300; 
x_300 = !lean_is_exclusive(x_1);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_1, 0);
lean_dec(x_301);
if (lean_is_scalar(x_251)) {
 x_302 = lean_alloc_ctor(0, 4, 0);
} else {
 x_302 = x_251;
}
lean_ctor_set(x_302, 0, x_247);
lean_ctor_set(x_302, 1, x_266);
lean_ctor_set(x_302, 2, x_259);
lean_ctor_set(x_302, 3, x_275);
lean_ctor_set(x_1, 0, x_302);
if (lean_is_scalar(x_277)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_277;
}
lean_ctor_set(x_303, 0, x_1);
lean_ctor_set(x_303, 1, x_276);
return x_303;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_1);
if (lean_is_scalar(x_251)) {
 x_304 = lean_alloc_ctor(0, 4, 0);
} else {
 x_304 = x_251;
}
lean_ctor_set(x_304, 0, x_247);
lean_ctor_set(x_304, 1, x_266);
lean_ctor_set(x_304, 2, x_259);
lean_ctor_set(x_304, 3, x_275);
x_305 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_305, 0, x_304);
if (lean_is_scalar(x_277)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_277;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_276);
return x_306;
}
}
else
{
lean_object* x_307; 
lean_dec(x_275);
lean_dec(x_266);
lean_dec(x_259);
lean_dec(x_251);
lean_dec(x_247);
if (lean_is_scalar(x_277)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_277;
}
lean_ctor_set(x_307, 0, x_1);
lean_ctor_set(x_307, 1, x_276);
return x_307;
}
}
}
}
block_320:
{
lean_object* x_311; uint8_t x_312; 
lean_dec(x_310);
x_311 = lean_unsigned_to_nat(0u);
x_312 = lean_nat_dec_lt(x_311, x_309);
lean_dec(x_309);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_275);
x_313 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_314 = l___private_Init_Util_0__outOfBounds___rarg(x_313);
x_315 = l_Lean_Compiler_LCNF_AltCore_getCode(x_314);
lean_dec(x_314);
if (lean_is_scalar(x_273)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_273;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_276);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_array_fget(x_275, x_311);
lean_dec(x_275);
x_318 = l_Lean_Compiler_LCNF_AltCore_getCode(x_317);
lean_dec(x_317);
if (lean_is_scalar(x_273)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_273;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_276);
return x_319;
}
}
}
else
{
uint8_t x_332; 
lean_dec(x_273);
lean_dec(x_266);
lean_dec(x_259);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_1);
x_332 = !lean_is_exclusive(x_274);
if (x_332 == 0)
{
return x_274;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_274, 0);
x_334 = lean_ctor_get(x_274, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_274);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
else
{
uint8_t x_336; 
lean_dec(x_266);
lean_dec(x_259);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_336 = !lean_is_exclusive(x_270);
if (x_336 == 0)
{
return x_270;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_270, 0);
x_338 = lean_ctor_get(x_270, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_270);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
else
{
uint8_t x_340; 
lean_dec(x_243);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_340 = !lean_is_exclusive(x_244);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_244, 0);
lean_dec(x_341);
x_342 = lean_ctor_get(x_245, 0);
lean_inc(x_342);
lean_dec(x_245);
lean_ctor_set(x_244, 0, x_342);
return x_244;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_244, 1);
lean_inc(x_343);
lean_dec(x_244);
x_344 = lean_ctor_get(x_245, 0);
lean_inc(x_344);
lean_dec(x_245);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_343);
return x_345;
}
}
}
else
{
uint8_t x_346; 
lean_dec(x_243);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_346 = !lean_is_exclusive(x_244);
if (x_346 == 0)
{
return x_244;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_244, 0);
x_348 = lean_ctor_get(x_244, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_244);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
case 5:
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; 
x_350 = lean_ctor_get(x_36, 1);
lean_inc(x_350);
lean_dec(x_36);
x_351 = lean_ctor_get(x_1, 0);
lean_inc(x_351);
x_352 = lean_st_ref_get(x_8, x_350);
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
lean_dec(x_352);
x_354 = lean_st_ref_get(x_3, x_353);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
x_357 = lean_ctor_get(x_355, 0);
lean_inc(x_357);
lean_dec(x_355);
x_358 = 0;
lean_inc(x_351);
x_359 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_357, x_351, x_358);
lean_inc(x_359);
x_360 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_359, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_356);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_361 = !lean_is_exclusive(x_360);
if (x_361 == 0)
{
lean_object* x_362; uint8_t x_363; 
x_362 = lean_ctor_get(x_360, 0);
lean_dec(x_362);
x_363 = lean_name_eq(x_351, x_359);
lean_dec(x_351);
if (x_363 == 0)
{
uint8_t x_364; 
x_364 = !lean_is_exclusive(x_1);
if (x_364 == 0)
{
lean_object* x_365; 
x_365 = lean_ctor_get(x_1, 0);
lean_dec(x_365);
lean_ctor_set(x_1, 0, x_359);
lean_ctor_set(x_360, 0, x_1);
return x_360;
}
else
{
lean_object* x_366; 
lean_dec(x_1);
x_366 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_366, 0, x_359);
lean_ctor_set(x_360, 0, x_366);
return x_360;
}
}
else
{
lean_dec(x_359);
lean_ctor_set(x_360, 0, x_1);
return x_360;
}
}
else
{
lean_object* x_367; uint8_t x_368; 
x_367 = lean_ctor_get(x_360, 1);
lean_inc(x_367);
lean_dec(x_360);
x_368 = lean_name_eq(x_351, x_359);
lean_dec(x_351);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_369 = x_1;
} else {
 lean_dec_ref(x_1);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(5, 1, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_359);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_367);
return x_371;
}
else
{
lean_object* x_372; 
lean_dec(x_359);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_1);
lean_ctor_set(x_372, 1, x_367);
return x_372;
}
}
}
default: 
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_373 = lean_ctor_get(x_36, 1);
lean_inc(x_373);
lean_dec(x_36);
x_374 = lean_ctor_get(x_1, 0);
lean_inc(x_374);
x_375 = lean_st_ref_get(x_8, x_373);
lean_dec(x_8);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec(x_375);
x_377 = lean_st_ref_get(x_3, x_376);
lean_dec(x_3);
x_378 = !lean_is_exclusive(x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; size_t x_383; size_t x_384; uint8_t x_385; 
x_379 = lean_ctor_get(x_377, 0);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
lean_dec(x_379);
x_381 = 0;
lean_inc(x_374);
x_382 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_380, x_381, x_374);
x_383 = lean_ptr_addr(x_374);
lean_dec(x_374);
x_384 = lean_ptr_addr(x_382);
x_385 = lean_usize_dec_eq(x_383, x_384);
if (x_385 == 0)
{
uint8_t x_386; 
x_386 = !lean_is_exclusive(x_1);
if (x_386 == 0)
{
lean_object* x_387; 
x_387 = lean_ctor_get(x_1, 0);
lean_dec(x_387);
lean_ctor_set(x_1, 0, x_382);
lean_ctor_set(x_377, 0, x_1);
return x_377;
}
else
{
lean_object* x_388; 
lean_dec(x_1);
x_388 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_388, 0, x_382);
lean_ctor_set(x_377, 0, x_388);
return x_377;
}
}
else
{
lean_dec(x_382);
lean_ctor_set(x_377, 0, x_1);
return x_377;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; size_t x_394; size_t x_395; uint8_t x_396; 
x_389 = lean_ctor_get(x_377, 0);
x_390 = lean_ctor_get(x_377, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_377);
x_391 = lean_ctor_get(x_389, 0);
lean_inc(x_391);
lean_dec(x_389);
x_392 = 0;
lean_inc(x_374);
x_393 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_391, x_392, x_374);
x_394 = lean_ptr_addr(x_374);
lean_dec(x_374);
x_395 = lean_ptr_addr(x_393);
x_396 = lean_usize_dec_eq(x_394, x_395);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_397 = x_1;
} else {
 lean_dec_ref(x_1);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(6, 1, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_393);
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_390);
return x_399;
}
else
{
lean_object* x_400; 
lean_dec(x_393);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_1);
lean_ctor_set(x_400, 1, x_390);
return x_400;
}
}
}
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_7);
x_401 = lean_unsigned_to_nat(1u);
x_402 = lean_nat_add(x_13, x_401);
lean_dec(x_13);
x_403 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_403, 0, x_10);
lean_ctor_set(x_403, 1, x_11);
lean_ctor_set(x_403, 2, x_12);
lean_ctor_set(x_403, 3, x_402);
lean_ctor_set(x_403, 4, x_14);
lean_ctor_set(x_403, 5, x_15);
lean_ctor_set(x_403, 6, x_16);
lean_ctor_set(x_403, 7, x_17);
lean_ctor_set(x_403, 8, x_18);
lean_ctor_set(x_403, 9, x_19);
lean_ctor_set(x_403, 10, x_20);
x_404 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_5, x_6, x_403, x_8, x_9);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
lean_dec(x_404);
x_406 = lean_ctor_get(x_1, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_1, 1);
lean_inc(x_407);
x_408 = 0;
lean_inc(x_406);
x_409 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_408, x_406, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_405);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_ctor_get(x_410, 3);
lean_inc(x_412);
lean_inc(x_8);
lean_inc(x_403);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_413 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_412, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_411);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_box(0);
x_417 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_407, x_406, x_1, x_410, x_416, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_415);
return x_417;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_418 = lean_ctor_get(x_413, 1);
lean_inc(x_418);
lean_dec(x_413);
x_419 = lean_ctor_get(x_414, 0);
lean_inc(x_419);
lean_dec(x_414);
x_420 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_403, x_8, x_418);
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
lean_dec(x_420);
x_422 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_410, x_419, x_5, x_6, x_403, x_8, x_421);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
x_425 = lean_box(0);
x_426 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_407, x_406, x_1, x_423, x_425, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_424);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_410);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_427 = lean_ctor_get(x_413, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_413, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_429 = x_413;
} else {
 lean_dec_ref(x_413);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_429)) {
 x_430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_430 = x_429;
}
lean_ctor_set(x_430, 0, x_427);
lean_ctor_set(x_430, 1, x_428);
return x_430;
}
}
case 1:
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_431 = lean_ctor_get(x_404, 1);
lean_inc(x_431);
lean_dec(x_404);
x_432 = lean_ctor_get(x_1, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_1, 1);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 0);
lean_inc(x_434);
x_435 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_434, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_431);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_unbox(x_436);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; uint8_t x_440; 
x_438 = lean_ctor_get(x_435, 1);
lean_inc(x_438);
lean_dec(x_435);
lean_inc(x_1);
lean_inc(x_432);
x_439 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed), 14, 4);
lean_closure_set(x_439, 0, x_433);
lean_closure_set(x_439, 1, x_432);
lean_closure_set(x_439, 2, x_1);
lean_closure_set(x_439, 3, x_436);
x_440 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_box(0);
x_442 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_439, x_432, x_441, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_438);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; uint8_t x_445; 
x_443 = lean_ctor_get(x_432, 3);
lean_inc(x_443);
x_444 = lean_ctor_get(x_432, 2);
lean_inc(x_444);
x_445 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_443, x_444);
lean_dec(x_444);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_box(0);
x_447 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_439, x_432, x_446, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_438);
return x_447;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; 
x_448 = lean_st_ref_get(x_8, x_438);
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
lean_dec(x_448);
x_450 = lean_st_ref_get(x_3, x_449);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
x_453 = lean_ctor_get(x_451, 0);
lean_inc(x_453);
lean_dec(x_451);
x_454 = 0;
lean_inc(x_8);
lean_inc(x_403);
lean_inc(x_6);
lean_inc(x_5);
x_455 = l_Lean_Compiler_LCNF_normFunDeclImp(x_454, x_432, x_453, x_5, x_6, x_403, x_8, x_452);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
lean_inc(x_8);
lean_inc(x_403);
lean_inc(x_6);
lean_inc(x_5);
x_458 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_456, x_5, x_6, x_403, x_8, x_457);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_403, x_8, x_460);
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec(x_461);
x_464 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_439, x_459, x_462, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_463);
lean_dec(x_462);
return x_464;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_439);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_465 = lean_ctor_get(x_458, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_458, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_467 = x_458;
} else {
 lean_dec_ref(x_458);
 x_467 = lean_box(0);
}
if (lean_is_scalar(x_467)) {
 x_468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_468 = x_467;
}
lean_ctor_set(x_468, 0, x_465);
lean_ctor_set(x_468, 1, x_466);
return x_468;
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_439);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_469 = lean_ctor_get(x_455, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_455, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_471 = x_455;
} else {
 lean_dec_ref(x_455);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_470);
return x_472;
}
}
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; 
x_473 = lean_ctor_get(x_435, 1);
lean_inc(x_473);
lean_dec(x_435);
x_474 = lean_st_ref_get(x_8, x_473);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
lean_dec(x_474);
x_476 = lean_st_ref_get(x_3, x_475);
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
x_479 = lean_ctor_get(x_477, 0);
lean_inc(x_479);
lean_dec(x_477);
x_480 = 0;
lean_inc(x_8);
lean_inc(x_403);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_432);
x_481 = l_Lean_Compiler_LCNF_normFunDeclImp(x_480, x_432, x_479, x_5, x_6, x_403, x_8, x_478);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = lean_box(0);
x_485 = lean_unbox(x_436);
lean_dec(x_436);
x_486 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_433, x_432, x_1, x_485, x_482, x_484, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_483);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_436);
lean_dec(x_433);
lean_dec(x_432);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_487 = lean_ctor_get(x_481, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_481, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_489 = x_481;
} else {
 lean_dec_ref(x_481);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
}
}
case 2:
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; 
x_491 = lean_ctor_get(x_404, 1);
lean_inc(x_491);
lean_dec(x_404);
x_492 = lean_ctor_get(x_1, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_1, 1);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 0);
lean_inc(x_494);
x_495 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_494, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_491);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_unbox(x_496);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; uint8_t x_500; 
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
lean_dec(x_495);
lean_inc(x_1);
lean_inc(x_492);
x_499 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 14, 4);
lean_closure_set(x_499, 0, x_493);
lean_closure_set(x_499, 1, x_492);
lean_closure_set(x_499, 2, x_1);
lean_closure_set(x_499, 3, x_496);
x_500 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_500 == 0)
{
lean_object* x_501; lean_object* x_502; 
x_501 = lean_box(0);
x_502 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_499, x_492, x_501, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_498);
return x_502;
}
else
{
lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_503 = lean_ctor_get(x_492, 3);
lean_inc(x_503);
x_504 = lean_ctor_get(x_492, 2);
lean_inc(x_504);
x_505 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_503, x_504);
lean_dec(x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; 
x_506 = lean_box(0);
x_507 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_499, x_492, x_506, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_498);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; lean_object* x_515; 
x_508 = lean_st_ref_get(x_8, x_498);
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
lean_dec(x_508);
x_510 = lean_st_ref_get(x_3, x_509);
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_513 = lean_ctor_get(x_511, 0);
lean_inc(x_513);
lean_dec(x_511);
x_514 = 0;
lean_inc(x_8);
lean_inc(x_403);
lean_inc(x_6);
lean_inc(x_5);
x_515 = l_Lean_Compiler_LCNF_normFunDeclImp(x_514, x_492, x_513, x_5, x_6, x_403, x_8, x_512);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
lean_inc(x_8);
lean_inc(x_403);
lean_inc(x_6);
lean_inc(x_5);
x_518 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_516, x_5, x_6, x_403, x_8, x_517);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_521 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_403, x_8, x_520);
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_499, x_519, x_522, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_523);
lean_dec(x_522);
return x_524;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_499);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_525 = lean_ctor_get(x_518, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_518, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_527 = x_518;
} else {
 lean_dec_ref(x_518);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(1, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_526);
return x_528;
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_499);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_529 = lean_ctor_get(x_515, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_515, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 x_531 = x_515;
} else {
 lean_dec_ref(x_515);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_529);
lean_ctor_set(x_532, 1, x_530);
return x_532;
}
}
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; lean_object* x_541; 
x_533 = lean_ctor_get(x_495, 1);
lean_inc(x_533);
lean_dec(x_495);
x_534 = lean_st_ref_get(x_8, x_533);
x_535 = lean_ctor_get(x_534, 1);
lean_inc(x_535);
lean_dec(x_534);
x_536 = lean_st_ref_get(x_3, x_535);
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = lean_ctor_get(x_537, 0);
lean_inc(x_539);
lean_dec(x_537);
x_540 = 0;
lean_inc(x_8);
lean_inc(x_403);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_492);
x_541 = l_Lean_Compiler_LCNF_normFunDeclImp(x_540, x_492, x_539, x_5, x_6, x_403, x_8, x_538);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; lean_object* x_546; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
lean_dec(x_541);
x_544 = lean_box(0);
x_545 = lean_unbox(x_496);
lean_dec(x_496);
x_546 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_493, x_492, x_1, x_545, x_542, x_544, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_543);
return x_546;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_496);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_547 = lean_ctor_get(x_541, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_541, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_549 = x_541;
} else {
 lean_dec_ref(x_541);
 x_549 = lean_box(0);
}
if (lean_is_scalar(x_549)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_549;
}
lean_ctor_set(x_550, 0, x_547);
lean_ctor_set(x_550, 1, x_548);
return x_550;
}
}
}
case 3:
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; lean_object* x_561; lean_object* x_562; 
x_551 = lean_ctor_get(x_404, 1);
lean_inc(x_551);
lean_dec(x_404);
x_552 = lean_ctor_get(x_1, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_1, 1);
lean_inc(x_553);
x_554 = lean_st_ref_get(x_8, x_551);
x_555 = lean_ctor_get(x_554, 1);
lean_inc(x_555);
lean_dec(x_554);
x_556 = lean_st_ref_get(x_3, x_555);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_559 = lean_ctor_get(x_557, 0);
lean_inc(x_559);
lean_dec(x_557);
x_560 = 0;
lean_inc(x_552);
x_561 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_559, x_552, x_560);
lean_inc(x_8);
lean_inc(x_403);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_553);
x_562 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_560, x_553, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_558);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_579; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_562, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_565 = x_562;
} else {
 lean_dec_ref(x_562);
 x_565 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_403);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_563);
lean_inc(x_561);
x_579 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_561, x_563, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_564);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; uint8_t x_586; 
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
lean_dec(x_579);
lean_inc(x_561);
x_582 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_561, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_581);
x_583 = lean_ctor_get(x_582, 1);
lean_inc(x_583);
lean_dec(x_582);
x_584 = lean_array_get_size(x_563);
x_585 = lean_unsigned_to_nat(0u);
x_586 = lean_nat_dec_lt(x_585, x_584);
if (x_586 == 0)
{
lean_dec(x_584);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_566 = x_583;
goto block_578;
}
else
{
uint8_t x_587; 
x_587 = lean_nat_dec_le(x_584, x_584);
if (x_587 == 0)
{
lean_dec(x_584);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_566 = x_583;
goto block_578;
}
else
{
size_t x_588; size_t x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_588 = 0;
x_589 = lean_usize_of_nat(x_584);
lean_dec(x_584);
x_590 = lean_box(0);
x_591 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_563, x_588, x_589, x_590, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_583);
lean_dec(x_8);
lean_dec(x_403);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_592 = lean_ctor_get(x_591, 1);
lean_inc(x_592);
lean_dec(x_591);
x_566 = x_592;
goto block_578;
}
}
}
else
{
lean_object* x_593; lean_object* x_594; 
lean_dec(x_565);
lean_dec(x_563);
lean_dec(x_561);
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_1);
x_593 = lean_ctor_get(x_579, 1);
lean_inc(x_593);
lean_dec(x_579);
x_594 = lean_ctor_get(x_580, 0);
lean_inc(x_594);
lean_dec(x_580);
x_1 = x_594;
x_7 = x_403;
x_9 = x_593;
goto _start;
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_565);
lean_dec(x_563);
lean_dec(x_561);
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_596 = lean_ctor_get(x_579, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_579, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_598 = x_579;
} else {
 lean_dec_ref(x_579);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_599 = x_598;
}
lean_ctor_set(x_599, 0, x_596);
lean_ctor_set(x_599, 1, x_597);
return x_599;
}
block_578:
{
uint8_t x_567; 
x_567 = lean_name_eq(x_552, x_561);
lean_dec(x_552);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_dec(x_553);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_568 = x_1;
} else {
 lean_dec_ref(x_1);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(3, 2, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_561);
lean_ctor_set(x_569, 1, x_563);
if (lean_is_scalar(x_565)) {
 x_570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_570 = x_565;
}
lean_ctor_set(x_570, 0, x_569);
lean_ctor_set(x_570, 1, x_566);
return x_570;
}
else
{
size_t x_571; size_t x_572; uint8_t x_573; 
x_571 = lean_ptr_addr(x_553);
lean_dec(x_553);
x_572 = lean_ptr_addr(x_563);
x_573 = lean_usize_dec_eq(x_571, x_572);
if (x_573 == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_574 = x_1;
} else {
 lean_dec_ref(x_1);
 x_574 = lean_box(0);
}
if (lean_is_scalar(x_574)) {
 x_575 = lean_alloc_ctor(3, 2, 0);
} else {
 x_575 = x_574;
}
lean_ctor_set(x_575, 0, x_561);
lean_ctor_set(x_575, 1, x_563);
if (lean_is_scalar(x_565)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_565;
}
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_566);
return x_576;
}
else
{
lean_object* x_577; 
lean_dec(x_563);
lean_dec(x_561);
if (lean_is_scalar(x_565)) {
 x_577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_577 = x_565;
}
lean_ctor_set(x_577, 0, x_1);
lean_ctor_set(x_577, 1, x_566);
return x_577;
}
}
}
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_561);
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_600 = lean_ctor_get(x_562, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_562, 1);
lean_inc(x_601);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_602 = x_562;
} else {
 lean_dec_ref(x_562);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(1, 2, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_600);
lean_ctor_set(x_603, 1, x_601);
return x_603;
}
}
case 4:
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_404, 1);
lean_inc(x_604);
lean_dec(x_404);
x_605 = lean_ctor_get(x_1, 0);
lean_inc(x_605);
lean_inc(x_8);
lean_inc(x_403);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_605);
x_606 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_605, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_604);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; 
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; uint8_t x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
x_609 = lean_ctor_get(x_605, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_605, 1);
lean_inc(x_610);
x_611 = lean_ctor_get(x_605, 2);
lean_inc(x_611);
x_612 = lean_ctor_get(x_605, 3);
lean_inc(x_612);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 lean_ctor_release(x_605, 2);
 lean_ctor_release(x_605, 3);
 x_613 = x_605;
} else {
 lean_dec_ref(x_605);
 x_613 = lean_box(0);
}
x_614 = lean_st_ref_get(x_8, x_608);
x_615 = lean_ctor_get(x_614, 1);
lean_inc(x_615);
lean_dec(x_614);
x_616 = lean_st_ref_get(x_3, x_615);
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = lean_ctor_get(x_617, 0);
lean_inc(x_619);
lean_dec(x_617);
x_620 = 0;
lean_inc(x_611);
x_621 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_619, x_611, x_620);
x_622 = lean_st_ref_get(x_8, x_618);
x_623 = lean_ctor_get(x_622, 1);
lean_inc(x_623);
lean_dec(x_622);
x_624 = lean_st_ref_get(x_3, x_623);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
x_627 = lean_ctor_get(x_625, 0);
lean_inc(x_627);
lean_dec(x_625);
lean_inc(x_610);
x_628 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_627, x_620, x_610);
lean_inc(x_621);
x_629 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_621, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_626);
x_630 = lean_ctor_get(x_629, 1);
lean_inc(x_630);
lean_dec(x_629);
lean_inc(x_621);
x_631 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7), 10, 1);
lean_closure_set(x_631, 0, x_621);
lean_inc(x_8);
lean_inc(x_403);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_612);
x_632 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__7(x_612, x_631, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_630);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_635 = x_632;
} else {
 lean_dec_ref(x_632);
 x_635 = lean_box(0);
}
x_636 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_633, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_634);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_662; lean_object* x_663; uint8_t x_674; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_636, 1);
lean_inc(x_638);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_639 = x_636;
} else {
 lean_dec_ref(x_636);
 x_639 = lean_box(0);
}
x_662 = lean_array_get_size(x_637);
x_674 = lean_nat_dec_eq(x_662, x_401);
if (x_674 == 0)
{
lean_object* x_675; 
lean_dec(x_662);
lean_dec(x_635);
x_675 = lean_box(0);
x_640 = x_675;
goto block_661;
}
else
{
lean_object* x_676; uint8_t x_677; 
x_676 = lean_unsigned_to_nat(0u);
x_677 = lean_nat_dec_lt(x_676, x_662);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; 
x_678 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_679 = l___private_Init_Util_0__outOfBounds___rarg(x_678);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; 
lean_dec(x_679);
lean_dec(x_662);
lean_dec(x_635);
x_680 = lean_box(0);
x_640 = x_680;
goto block_661;
}
else
{
lean_object* x_681; 
lean_dec(x_679);
lean_dec(x_639);
lean_dec(x_628);
lean_dec(x_621);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_1);
x_681 = lean_box(0);
x_663 = x_681;
goto block_673;
}
}
else
{
lean_object* x_682; 
x_682 = lean_array_fget(x_637, x_676);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; 
lean_dec(x_682);
lean_dec(x_662);
lean_dec(x_635);
x_683 = lean_box(0);
x_640 = x_683;
goto block_661;
}
else
{
lean_object* x_684; 
lean_dec(x_682);
lean_dec(x_639);
lean_dec(x_628);
lean_dec(x_621);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_1);
x_684 = lean_box(0);
x_663 = x_684;
goto block_673;
}
}
}
block_661:
{
size_t x_641; size_t x_642; uint8_t x_643; 
lean_dec(x_640);
x_641 = lean_ptr_addr(x_612);
lean_dec(x_612);
x_642 = lean_ptr_addr(x_637);
x_643 = lean_usize_dec_eq(x_641, x_642);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_dec(x_611);
lean_dec(x_610);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_644 = x_1;
} else {
 lean_dec_ref(x_1);
 x_644 = lean_box(0);
}
if (lean_is_scalar(x_613)) {
 x_645 = lean_alloc_ctor(0, 4, 0);
} else {
 x_645 = x_613;
}
lean_ctor_set(x_645, 0, x_609);
lean_ctor_set(x_645, 1, x_628);
lean_ctor_set(x_645, 2, x_621);
lean_ctor_set(x_645, 3, x_637);
if (lean_is_scalar(x_644)) {
 x_646 = lean_alloc_ctor(4, 1, 0);
} else {
 x_646 = x_644;
}
lean_ctor_set(x_646, 0, x_645);
if (lean_is_scalar(x_639)) {
 x_647 = lean_alloc_ctor(0, 2, 0);
} else {
 x_647 = x_639;
}
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_638);
return x_647;
}
else
{
size_t x_648; size_t x_649; uint8_t x_650; 
x_648 = lean_ptr_addr(x_610);
lean_dec(x_610);
x_649 = lean_ptr_addr(x_628);
x_650 = lean_usize_dec_eq(x_648, x_649);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
lean_dec(x_611);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_651 = x_1;
} else {
 lean_dec_ref(x_1);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_613)) {
 x_652 = lean_alloc_ctor(0, 4, 0);
} else {
 x_652 = x_613;
}
lean_ctor_set(x_652, 0, x_609);
lean_ctor_set(x_652, 1, x_628);
lean_ctor_set(x_652, 2, x_621);
lean_ctor_set(x_652, 3, x_637);
if (lean_is_scalar(x_651)) {
 x_653 = lean_alloc_ctor(4, 1, 0);
} else {
 x_653 = x_651;
}
lean_ctor_set(x_653, 0, x_652);
if (lean_is_scalar(x_639)) {
 x_654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_654 = x_639;
}
lean_ctor_set(x_654, 0, x_653);
lean_ctor_set(x_654, 1, x_638);
return x_654;
}
else
{
uint8_t x_655; 
x_655 = lean_name_eq(x_611, x_621);
lean_dec(x_611);
if (x_655 == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_656 = x_1;
} else {
 lean_dec_ref(x_1);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_613)) {
 x_657 = lean_alloc_ctor(0, 4, 0);
} else {
 x_657 = x_613;
}
lean_ctor_set(x_657, 0, x_609);
lean_ctor_set(x_657, 1, x_628);
lean_ctor_set(x_657, 2, x_621);
lean_ctor_set(x_657, 3, x_637);
if (lean_is_scalar(x_656)) {
 x_658 = lean_alloc_ctor(4, 1, 0);
} else {
 x_658 = x_656;
}
lean_ctor_set(x_658, 0, x_657);
if (lean_is_scalar(x_639)) {
 x_659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_659 = x_639;
}
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_638);
return x_659;
}
else
{
lean_object* x_660; 
lean_dec(x_637);
lean_dec(x_628);
lean_dec(x_621);
lean_dec(x_613);
lean_dec(x_609);
if (lean_is_scalar(x_639)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_639;
}
lean_ctor_set(x_660, 0, x_1);
lean_ctor_set(x_660, 1, x_638);
return x_660;
}
}
}
}
block_673:
{
lean_object* x_664; uint8_t x_665; 
lean_dec(x_663);
x_664 = lean_unsigned_to_nat(0u);
x_665 = lean_nat_dec_lt(x_664, x_662);
lean_dec(x_662);
if (x_665 == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_637);
x_666 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_667 = l___private_Init_Util_0__outOfBounds___rarg(x_666);
x_668 = l_Lean_Compiler_LCNF_AltCore_getCode(x_667);
lean_dec(x_667);
if (lean_is_scalar(x_635)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_635;
}
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_638);
return x_669;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_array_fget(x_637, x_664);
lean_dec(x_637);
x_671 = l_Lean_Compiler_LCNF_AltCore_getCode(x_670);
lean_dec(x_670);
if (lean_is_scalar(x_635)) {
 x_672 = lean_alloc_ctor(0, 2, 0);
} else {
 x_672 = x_635;
}
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_638);
return x_672;
}
}
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_635);
lean_dec(x_628);
lean_dec(x_621);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_1);
x_685 = lean_ctor_get(x_636, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_636, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_687 = x_636;
} else {
 lean_dec_ref(x_636);
 x_687 = lean_box(0);
}
if (lean_is_scalar(x_687)) {
 x_688 = lean_alloc_ctor(1, 2, 0);
} else {
 x_688 = x_687;
}
lean_ctor_set(x_688, 0, x_685);
lean_ctor_set(x_688, 1, x_686);
return x_688;
}
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
lean_dec(x_628);
lean_dec(x_621);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_689 = lean_ctor_get(x_632, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_632, 1);
lean_inc(x_690);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_691 = x_632;
} else {
 lean_dec_ref(x_632);
 x_691 = lean_box(0);
}
if (lean_is_scalar(x_691)) {
 x_692 = lean_alloc_ctor(1, 2, 0);
} else {
 x_692 = x_691;
}
lean_ctor_set(x_692, 0, x_689);
lean_ctor_set(x_692, 1, x_690);
return x_692;
}
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_605);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_693 = lean_ctor_get(x_606, 1);
lean_inc(x_693);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_694 = x_606;
} else {
 lean_dec_ref(x_606);
 x_694 = lean_box(0);
}
x_695 = lean_ctor_get(x_607, 0);
lean_inc(x_695);
lean_dec(x_607);
if (lean_is_scalar(x_694)) {
 x_696 = lean_alloc_ctor(0, 2, 0);
} else {
 x_696 = x_694;
}
lean_ctor_set(x_696, 0, x_695);
lean_ctor_set(x_696, 1, x_693);
return x_696;
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec(x_605);
lean_dec(x_403);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_697 = lean_ctor_get(x_606, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_606, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_699 = x_606;
} else {
 lean_dec_ref(x_606);
 x_699 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_700 = lean_alloc_ctor(1, 2, 0);
} else {
 x_700 = x_699;
}
lean_ctor_set(x_700, 0, x_697);
lean_ctor_set(x_700, 1, x_698);
return x_700;
}
}
case 5:
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; uint8_t x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; uint8_t x_714; 
x_701 = lean_ctor_get(x_404, 1);
lean_inc(x_701);
lean_dec(x_404);
x_702 = lean_ctor_get(x_1, 0);
lean_inc(x_702);
x_703 = lean_st_ref_get(x_8, x_701);
x_704 = lean_ctor_get(x_703, 1);
lean_inc(x_704);
lean_dec(x_703);
x_705 = lean_st_ref_get(x_3, x_704);
x_706 = lean_ctor_get(x_705, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_705, 1);
lean_inc(x_707);
lean_dec(x_705);
x_708 = lean_ctor_get(x_706, 0);
lean_inc(x_708);
lean_dec(x_706);
x_709 = 0;
lean_inc(x_702);
x_710 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_708, x_702, x_709);
lean_inc(x_710);
x_711 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_710, x_2, x_3, x_4, x_5, x_6, x_403, x_8, x_707);
lean_dec(x_8);
lean_dec(x_403);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_713 = x_711;
} else {
 lean_dec_ref(x_711);
 x_713 = lean_box(0);
}
x_714 = lean_name_eq(x_702, x_710);
lean_dec(x_702);
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
lean_ctor_set(x_716, 0, x_710);
if (lean_is_scalar(x_713)) {
 x_717 = lean_alloc_ctor(0, 2, 0);
} else {
 x_717 = x_713;
}
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_712);
return x_717;
}
else
{
lean_object* x_718; 
lean_dec(x_710);
if (lean_is_scalar(x_713)) {
 x_718 = lean_alloc_ctor(0, 2, 0);
} else {
 x_718 = x_713;
}
lean_ctor_set(x_718, 0, x_1);
lean_ctor_set(x_718, 1, x_712);
return x_718;
}
}
default: 
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; uint8_t x_728; lean_object* x_729; size_t x_730; size_t x_731; uint8_t x_732; 
lean_dec(x_403);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_719 = lean_ctor_get(x_404, 1);
lean_inc(x_719);
lean_dec(x_404);
x_720 = lean_ctor_get(x_1, 0);
lean_inc(x_720);
x_721 = lean_st_ref_get(x_8, x_719);
lean_dec(x_8);
x_722 = lean_ctor_get(x_721, 1);
lean_inc(x_722);
lean_dec(x_721);
x_723 = lean_st_ref_get(x_3, x_722);
lean_dec(x_3);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 lean_ctor_release(x_723, 1);
 x_726 = x_723;
} else {
 lean_dec_ref(x_723);
 x_726 = lean_box(0);
}
x_727 = lean_ctor_get(x_724, 0);
lean_inc(x_727);
lean_dec(x_724);
x_728 = 0;
lean_inc(x_720);
x_729 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_727, x_728, x_720);
x_730 = lean_ptr_addr(x_720);
lean_dec(x_720);
x_731 = lean_ptr_addr(x_729);
x_732 = lean_usize_dec_eq(x_730, x_731);
if (x_732 == 0)
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_733 = x_1;
} else {
 lean_dec_ref(x_1);
 x_733 = lean_box(0);
}
if (lean_is_scalar(x_733)) {
 x_734 = lean_alloc_ctor(6, 1, 0);
} else {
 x_734 = x_733;
}
lean_ctor_set(x_734, 0, x_729);
if (lean_is_scalar(x_726)) {
 x_735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_735 = x_726;
}
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_725);
return x_735;
}
else
{
lean_object* x_736; 
lean_dec(x_729);
if (lean_is_scalar(x_726)) {
 x_736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_736 = x_726;
}
lean_ctor_set(x_736, 0, x_1);
lean_ctor_set(x_736, 1, x_725);
return x_736;
}
}
}
}
}
else
{
lean_object* x_737; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_737 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_737;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_25; 
x_15 = lean_array_uget(x_1, x_3);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_4);
x_16 = x_32;
x_17 = x_12;
goto block_24;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_26, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_array_fget(x_28, x_29);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_29, x_38);
lean_dec(x_29);
lean_ctor_set(x_26, 1, x_39);
x_40 = l_Lean_Expr_isFVar(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_37, x_41, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_array_push(x_27, x_45);
x_47 = lean_ctor_get(x_15, 0);
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
lean_dec(x_43);
x_49 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_47, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_ctor_set(x_4, 1, x_46);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_4);
x_16 = x_51;
x_17 = x_50;
goto block_24;
}
else
{
uint8_t x_52; 
lean_dec(x_46);
lean_dec(x_26);
lean_free_object(x_4);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
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
lean_dec(x_26);
lean_free_object(x_4);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_56 = !lean_is_exclusive(x_42);
if (x_56 == 0)
{
return x_42;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_42, 0);
x_58 = lean_ctor_get(x_42, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_42);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_15, 0);
lean_inc(x_60);
lean_dec(x_15);
x_61 = l_Lean_Expr_fvarId_x21(x_37);
x_62 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_60, x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_4);
x_16 = x_64;
x_17 = x_63;
goto block_24;
}
else
{
uint8_t x_65; 
lean_dec(x_26);
lean_free_object(x_4);
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_62);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_26);
x_69 = lean_array_fget(x_28, x_29);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_29, x_70);
lean_dec(x_29);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_28);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_30);
x_73 = l_Lean_Expr_isFVar(x_69);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_75 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_69, x_74, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_76);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_76);
x_79 = lean_array_push(x_27, x_78);
x_80 = lean_ctor_get(x_15, 0);
lean_inc(x_80);
lean_dec(x_15);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
lean_dec(x_76);
x_82 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_80, x_81, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_77);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
lean_ctor_set(x_4, 1, x_79);
lean_ctor_set(x_4, 0, x_72);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_4);
x_16 = x_84;
x_17 = x_83;
goto block_24;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_79);
lean_dec(x_72);
lean_free_object(x_4);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_87 = x_82;
} else {
 lean_dec_ref(x_82);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_72);
lean_free_object(x_4);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_89 = lean_ctor_get(x_75, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_75, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_91 = x_75;
} else {
 lean_dec_ref(x_75);
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
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_15, 0);
lean_inc(x_93);
lean_dec(x_15);
x_94 = l_Lean_Expr_fvarId_x21(x_69);
x_95 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_93, x_94, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
lean_ctor_set(x_4, 0, x_72);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_4);
x_16 = x_97;
x_17 = x_96;
goto block_24;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_72);
lean_free_object(x_4);
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_100 = x_95;
} else {
 lean_dec_ref(x_95);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_102 = lean_ctor_get(x_4, 0);
x_103 = lean_ctor_get(x_4, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_4);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_102, 2);
lean_inc(x_106);
x_107 = lean_nat_dec_lt(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_15);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_103);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_16 = x_109;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 x_110 = x_102;
} else {
 lean_dec_ref(x_102);
 x_110 = lean_box(0);
}
x_111 = lean_array_fget(x_104, x_105);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_add(x_105, x_112);
lean_dec(x_105);
if (lean_is_scalar(x_110)) {
 x_114 = lean_alloc_ctor(0, 3, 0);
} else {
 x_114 = x_110;
}
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_106);
x_115 = l_Lean_Expr_isFVar(x_111);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_117 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_111, x_116, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_118);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_118);
x_121 = lean_array_push(x_103, x_120);
x_122 = lean_ctor_get(x_15, 0);
lean_inc(x_122);
lean_dec(x_15);
x_123 = lean_ctor_get(x_118, 0);
lean_inc(x_123);
lean_dec(x_118);
x_124 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_122, x_123, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_119);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_114);
lean_ctor_set(x_126, 1, x_121);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_16 = x_127;
x_17 = x_125;
goto block_24;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_121);
lean_dec(x_114);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_128 = lean_ctor_get(x_124, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_130 = x_124;
} else {
 lean_dec_ref(x_124);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_132 = lean_ctor_get(x_117, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_117, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_134 = x_117;
} else {
 lean_dec_ref(x_117);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_15, 0);
lean_inc(x_136);
lean_dec(x_15);
x_137 = l_Lean_Expr_fvarId_x21(x_111);
x_138 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_136, x_137, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_114);
lean_ctor_set(x_140, 1, x_103);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_16 = x_141;
x_17 = x_139;
goto block_24;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_142 = lean_ctor_get(x_138, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_144 = x_138;
} else {
 lean_dec_ref(x_138);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
}
block_24:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_4 = x_20;
x_12 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_16, x_10, x_17);
x_19 = l_Lean_Expr_fvar___override(x_18);
x_20 = l_Lean_Compiler_LCNF_Simp_findCtor(x_19, x_4, x_5, x_6, x_7, x_8, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_8, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 1;
x_29 = l_Lean_Expr_constructorApp_x3f(x_27, x_21, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(0);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
uint8_t x_31; 
lean_free_object(x_23);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_Compiler_LCNF_eraseCode(x_40, x_5, x_6, x_7, x_8, x_26);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_42);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_38, 2);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_ctor_get(x_33, 3);
lean_inc(x_47);
lean_dec(x_33);
x_48 = lean_array_get_size(x_34);
x_49 = l_Array_toSubarray___rarg(x_34, x_47, x_48);
x_50 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_get_size(x_45);
x_53 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_54 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_45, x_53, x_54, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_59 = l_Lean_Compiler_LCNF_Simp_simp(x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Compiler_LCNF_eraseParams(x_45, x_5, x_6, x_7, x_8, x_61);
lean_dec(x_45);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_58, x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
lean_dec(x_58);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_ctor_set(x_29, 0, x_66);
lean_ctor_set(x_64, 0, x_29);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_64);
lean_ctor_set(x_29, 0, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_29);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_58);
lean_dec(x_45);
lean_free_object(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_59);
if (x_70 == 0)
{
return x_59;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_59, 0);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_59);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_55);
if (x_74 == 0)
{
return x_55;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_55, 0);
x_76 = lean_ctor_get(x_55, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_55);
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
lean_dec(x_34);
lean_dec(x_33);
x_78 = lean_ctor_get(x_43, 1);
lean_inc(x_78);
lean_dec(x_43);
x_79 = lean_ctor_get(x_38, 0);
lean_inc(x_79);
lean_dec(x_38);
x_80 = l_Lean_Compiler_LCNF_Simp_simp(x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_78);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
lean_ctor_set(x_29, 0, x_82);
lean_ctor_set(x_80, 0, x_29);
return x_80;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_80, 0);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_80);
lean_ctor_set(x_29, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_29);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_free_object(x_29);
x_86 = !lean_is_exclusive(x_80);
if (x_86 == 0)
{
return x_80;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_80, 0);
x_88 = lean_ctor_get(x_80, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_80);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_90 = lean_ctor_get(x_29, 0);
lean_inc(x_90);
lean_dec(x_29);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l_Lean_Compiler_LCNF_eraseCode(x_98, x_5, x_6, x_7, x_8, x_26);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_100);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; lean_object* x_113; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_96, 2);
lean_inc(x_104);
lean_dec(x_96);
x_105 = lean_ctor_get(x_91, 3);
lean_inc(x_105);
lean_dec(x_91);
x_106 = lean_array_get_size(x_92);
x_107 = l_Array_toSubarray___rarg(x_92, x_105, x_106);
x_108 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_array_get_size(x_103);
x_111 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_112 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_113 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_103, x_111, x_112, x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_102);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_117 = l_Lean_Compiler_LCNF_Simp_simp(x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_Compiler_LCNF_eraseParams(x_103, x_5, x_6, x_7, x_8, x_119);
lean_dec(x_103);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_116, x_118, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_121);
lean_dec(x_116);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_123);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_116);
lean_dec(x_103);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = lean_ctor_get(x_117, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_117, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_130 = x_117;
} else {
 lean_dec_ref(x_117);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_132 = lean_ctor_get(x_113, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_113, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_134 = x_113;
} else {
 lean_dec_ref(x_113);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_92);
lean_dec(x_91);
x_136 = lean_ctor_get(x_101, 1);
lean_inc(x_136);
lean_dec(x_101);
x_137 = lean_ctor_get(x_96, 0);
lean_inc(x_137);
lean_dec(x_96);
x_138 = l_Lean_Compiler_LCNF_Simp_simp(x_137, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_139);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_138, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_146 = x_138;
} else {
 lean_dec_ref(x_138);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_23, 0);
x_149 = lean_ctor_get(x_23, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_23);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
lean_dec(x_148);
x_151 = 1;
x_152 = l_Lean_Expr_constructorApp_x3f(x_150, x_21, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_149);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_156 = x_152;
} else {
 lean_dec_ref(x_152);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
x_161 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Lean_Compiler_LCNF_eraseCode(x_164, x_5, x_6, x_7, x_8, x_149);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_166);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; size_t x_177; size_t x_178; lean_object* x_179; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_ctor_get(x_162, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_162, 2);
lean_inc(x_170);
lean_dec(x_162);
x_171 = lean_ctor_get(x_157, 3);
lean_inc(x_171);
lean_dec(x_157);
x_172 = lean_array_get_size(x_158);
x_173 = l_Array_toSubarray___rarg(x_158, x_171, x_172);
x_174 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_array_get_size(x_169);
x_177 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_178 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_179 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_169, x_177, x_178, x_175, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_168);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_183 = l_Lean_Compiler_LCNF_Simp_simp(x_170, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_181);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = l_Lean_Compiler_LCNF_eraseParams(x_169, x_5, x_6, x_7, x_8, x_185);
lean_dec(x_169);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_188 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_182, x_184, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_187);
lean_dec(x_182);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_156;
}
lean_ctor_set(x_192, 0, x_189);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_182);
lean_dec(x_169);
lean_dec(x_156);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_156);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_158);
lean_dec(x_157);
x_202 = lean_ctor_get(x_167, 1);
lean_inc(x_202);
lean_dec(x_167);
x_203 = lean_ctor_get(x_162, 0);
lean_inc(x_203);
lean_dec(x_162);
x_204 = l_Lean_Compiler_LCNF_Simp_simp(x_203, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_202);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_208 = lean_alloc_ctor(1, 1, 0);
} else {
 x_208 = x_156;
}
lean_ctor_set(x_208, 0, x_205);
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_206);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_156);
x_210 = lean_ctor_get(x_204, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_212 = x_204;
} else {
 lean_dec_ref(x_204);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_st_ref_get(x_9, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_17, x_1, x_11);
x_19 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(x_2, x_18, x_6, x_7, x_8, x_9, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_16 = lean_apply_9(x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ptr_addr(x_15);
lean_dec(x_15);
x_20 = lean_ptr_addr(x_17);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
x_24 = lean_array_fset(x_3, x_2, x_17);
lean_dec(x_2);
x_2 = x_23;
x_3 = x_24;
x_11 = x_18;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_2, x_26);
lean_dec(x_2);
x_2 = x_27;
x_11 = x_18;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(x_2, x_11, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed), 10, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_16, x_17, x_10);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(x_17, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_1, 4);
lean_inc(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Compiler_LCNF_Simp_simp(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_18, x_21, x_25, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
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
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4);
l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2);
l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3);
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
