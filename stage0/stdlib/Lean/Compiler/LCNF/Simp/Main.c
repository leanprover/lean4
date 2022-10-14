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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2;
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
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_jp", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1;
x_13 = lean_array_push(x_12, x_1);
x_14 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_13, x_3, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_12);
x_19 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_2, x_18, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_16);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_120; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_120 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_box(0);
x_44 = x_121;
goto block_119;
}
else
{
uint8_t x_122; 
x_122 = lean_nat_dec_eq(x_24, x_27);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_box(0);
x_44 = x_123;
goto block_119;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_124 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_43);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l_Lean_Compiler_LCNF_Simp_simp(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_125);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_126, 0, x_129);
return x_126;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_126, 0);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_126);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_130);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_126);
if (x_134 == 0)
{
return x_126;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_126, 0);
x_136 = lean_ctor_get(x_126, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_126);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
block_119:
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_22);
x_49 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_47);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Compiler_LCNF_mkAuxParam(x_36, x_40, x_6, x_7, x_8, x_9, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_27);
lean_dec(x_23);
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
x_56 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_58 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_52, x_46, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_60);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
return x_56;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_56, 0);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_56);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_52, 0);
lean_inc(x_70);
x_71 = l_Lean_Expr_fvar___override(x_70);
x_72 = lean_array_get_size(x_23);
x_73 = l_Array_toSubarray___rarg(x_23, x_27, x_72);
x_74 = l_Array_ofSubarray___rarg(x_73);
x_75 = l_Lean_mkAppN(x_71, x_74);
x_76 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_77 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_75, x_76, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_84 = l_Lean_Compiler_LCNF_Simp_simp(x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_52, x_46, x_85, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_84);
if (x_88 == 0)
{
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_84, 0);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_84);
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
lean_dec(x_78);
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_81);
if (x_92 == 0)
{
return x_81;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_81, 0);
x_94 = lean_ctor_get(x_81, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_81);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_77);
if (x_96 == 0)
{
return x_77;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_77, 0);
x_98 = lean_ctor_get(x_77, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_77);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_36);
x_100 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_47);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_102, 0, x_3);
lean_closure_set(x_102, 1, x_4);
lean_closure_set(x_102, 2, x_5);
lean_closure_set(x_102, 3, x_27);
lean_closure_set(x_102, 4, x_24);
lean_closure_set(x_102, 5, x_26);
lean_closure_set(x_102, 6, x_2);
lean_closure_set(x_102, 7, x_23);
x_103 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_46, x_102, x_6, x_7, x_8, x_9, x_101);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 0);
if (lean_is_scalar(x_22)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_22;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_103, 0, x_106);
return x_103;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_103, 0);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_103);
if (lean_is_scalar(x_22)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_22;
}
lean_ctor_set(x_109, 0, x_107);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
uint8_t x_111; 
lean_dec(x_22);
x_111 = !lean_is_exclusive(x_103);
if (x_111 == 0)
{
return x_103;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_103, 0);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_103);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
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
x_115 = !lean_is_exclusive(x_45);
if (x_115 == 0)
{
return x_45;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_45, 0);
x_117 = lean_ctor_get(x_45, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_45);
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
uint8_t x_138; 
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
x_138 = !lean_is_exclusive(x_41);
if (x_138 == 0)
{
return x_41;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_41, 0);
x_140 = lean_ctor_get(x_41, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_41);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
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
x_142 = !lean_is_exclusive(x_35);
if (x_142 == 0)
{
return x_35;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_35, 0);
x_144 = lean_ctor_get(x_35, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_35);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
case 1:
{
lean_object* x_146; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_146 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_21, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_21, 1);
lean_inc(x_150);
lean_dec(x_21);
x_151 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_152 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_149, x_150, x_32, x_151, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_148);
lean_dec(x_149);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_231; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_231 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_231 == 0)
{
lean_object* x_232; 
x_232 = lean_box(0);
x_155 = x_232;
goto block_230;
}
else
{
uint8_t x_233; 
x_233 = lean_nat_dec_eq(x_24, x_27);
if (x_233 == 0)
{
lean_object* x_234; 
x_234 = lean_box(0);
x_155 = x_234;
goto block_230;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_147);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_235 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_154);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_237 = l_Lean_Compiler_LCNF_Simp_simp(x_153, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_236);
if (lean_obj_tag(x_237) == 0)
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_237, 0, x_240);
return x_237;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_237, 0);
x_242 = lean_ctor_get(x_237, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_237);
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_241);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
else
{
uint8_t x_245; 
x_245 = !lean_is_exclusive(x_237);
if (x_245 == 0)
{
return x_237;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_237, 0);
x_247 = lean_ctor_get(x_237, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_237);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
}
block_230:
{
lean_object* x_156; 
lean_dec(x_155);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_156 = l_Lean_Compiler_LCNF_Simp_simp(x_153, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_154);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
lean_inc(x_157);
x_159 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
lean_dec(x_22);
x_160 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_158);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = l_Lean_Compiler_LCNF_mkAuxParam(x_147, x_151, x_6, x_7, x_8, x_9, x_161);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_27);
lean_dec(x_23);
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
x_167 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_166, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_164);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_169 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_163, x_157, x_170, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_171);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_172;
}
else
{
uint8_t x_173; 
lean_dec(x_163);
lean_dec(x_157);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_173 = !lean_is_exclusive(x_169);
if (x_173 == 0)
{
return x_169;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_169, 0);
x_175 = lean_ctor_get(x_169, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_169);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_163);
lean_dec(x_157);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_177 = !lean_is_exclusive(x_167);
if (x_177 == 0)
{
return x_167;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_167, 0);
x_179 = lean_ctor_get(x_167, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_167);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_181 = lean_ctor_get(x_163, 0);
lean_inc(x_181);
x_182 = l_Lean_Expr_fvar___override(x_181);
x_183 = lean_array_get_size(x_23);
x_184 = l_Array_toSubarray___rarg(x_23, x_27, x_183);
x_185 = l_Array_ofSubarray___rarg(x_184);
x_186 = l_Lean_mkAppN(x_182, x_185);
x_187 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_188 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_186, x_187, x_6, x_7, x_8, x_9, x_164);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
x_192 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_191, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_189);
lean_ctor_set(x_194, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_195 = l_Lean_Compiler_LCNF_Simp_simp(x_194, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_163, x_157, x_196, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_197);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_198;
}
else
{
uint8_t x_199; 
lean_dec(x_163);
lean_dec(x_157);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_199 = !lean_is_exclusive(x_195);
if (x_199 == 0)
{
return x_195;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_195, 0);
x_201 = lean_ctor_get(x_195, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_195);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_189);
lean_dec(x_163);
lean_dec(x_157);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_203 = !lean_is_exclusive(x_192);
if (x_203 == 0)
{
return x_192;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_192, 0);
x_205 = lean_ctor_get(x_192, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_192);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_163);
lean_dec(x_157);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = !lean_is_exclusive(x_188);
if (x_207 == 0)
{
return x_188;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_188, 0);
x_209 = lean_ctor_get(x_188, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_188);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_147);
x_211 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_158);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_213, 0, x_3);
lean_closure_set(x_213, 1, x_4);
lean_closure_set(x_213, 2, x_5);
lean_closure_set(x_213, 3, x_27);
lean_closure_set(x_213, 4, x_24);
lean_closure_set(x_213, 5, x_26);
lean_closure_set(x_213, 6, x_2);
lean_closure_set(x_213, 7, x_23);
x_214 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_157, x_213, x_6, x_7, x_8, x_9, x_212);
if (lean_obj_tag(x_214) == 0)
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_214, 0);
if (lean_is_scalar(x_22)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_22;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_214, 0, x_217);
return x_214;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_214, 0);
x_219 = lean_ctor_get(x_214, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_214);
if (lean_is_scalar(x_22)) {
 x_220 = lean_alloc_ctor(1, 1, 0);
} else {
 x_220 = x_22;
}
lean_ctor_set(x_220, 0, x_218);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
uint8_t x_222; 
lean_dec(x_22);
x_222 = !lean_is_exclusive(x_214);
if (x_222 == 0)
{
return x_214;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_214, 0);
x_224 = lean_ctor_get(x_214, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_214);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_147);
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
x_226 = !lean_is_exclusive(x_156);
if (x_226 == 0)
{
return x_156;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_156, 0);
x_228 = lean_ctor_get(x_156, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_156);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_147);
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
x_249 = !lean_is_exclusive(x_152);
if (x_249 == 0)
{
return x_152;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_152, 0);
x_251 = lean_ctor_get(x_152, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_152);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
else
{
uint8_t x_253; 
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
x_253 = !lean_is_exclusive(x_146);
if (x_253 == 0)
{
return x_146;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_146, 0);
x_255 = lean_ctor_get(x_146, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_146);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
case 2:
{
lean_object* x_257; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_257 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_ctor_get(x_21, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_21, 1);
lean_inc(x_261);
lean_dec(x_21);
x_262 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_263 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_260, x_261, x_32, x_262, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_259);
lean_dec(x_260);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_342; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_342 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_342 == 0)
{
lean_object* x_343; 
x_343 = lean_box(0);
x_266 = x_343;
goto block_341;
}
else
{
uint8_t x_344; 
x_344 = lean_nat_dec_eq(x_24, x_27);
if (x_344 == 0)
{
lean_object* x_345; 
x_345 = lean_box(0);
x_266 = x_345;
goto block_341;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_258);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_346 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_265);
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
lean_dec(x_346);
x_348 = l_Lean_Compiler_LCNF_Simp_simp(x_264, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_347);
if (lean_obj_tag(x_348) == 0)
{
uint8_t x_349; 
x_349 = !lean_is_exclusive(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_348, 0);
x_351 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_348, 0, x_351);
return x_348;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_352 = lean_ctor_get(x_348, 0);
x_353 = lean_ctor_get(x_348, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_348);
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_352);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
}
else
{
uint8_t x_356; 
x_356 = !lean_is_exclusive(x_348);
if (x_356 == 0)
{
return x_348;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_348, 0);
x_358 = lean_ctor_get(x_348, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_348);
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
return x_359;
}
}
}
}
block_341:
{
lean_object* x_267; 
lean_dec(x_266);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_267 = l_Lean_Compiler_LCNF_Simp_simp(x_264, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_265);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
lean_inc(x_268);
x_270 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_268);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
lean_dec(x_22);
x_271 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_269);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec(x_271);
x_273 = l_Lean_Compiler_LCNF_mkAuxParam(x_258, x_262, x_6, x_7, x_8, x_9, x_272);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_27);
lean_dec(x_23);
x_277 = lean_ctor_get(x_274, 0);
lean_inc(x_277);
x_278 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_277, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_275);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_280 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_274, x_268, x_281, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_282);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_283;
}
else
{
uint8_t x_284; 
lean_dec(x_274);
lean_dec(x_268);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_284 = !lean_is_exclusive(x_280);
if (x_284 == 0)
{
return x_280;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_280, 0);
x_286 = lean_ctor_get(x_280, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_280);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
else
{
uint8_t x_288; 
lean_dec(x_274);
lean_dec(x_268);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_292 = lean_ctor_get(x_274, 0);
lean_inc(x_292);
x_293 = l_Lean_Expr_fvar___override(x_292);
x_294 = lean_array_get_size(x_23);
x_295 = l_Array_toSubarray___rarg(x_23, x_27, x_294);
x_296 = l_Array_ofSubarray___rarg(x_295);
x_297 = l_Lean_mkAppN(x_293, x_296);
x_298 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_299 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_297, x_298, x_6, x_7, x_8, x_9, x_275);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_ctor_get(x_300, 0);
lean_inc(x_302);
x_303 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_302, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_301);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_300);
lean_ctor_set(x_305, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_306 = l_Lean_Compiler_LCNF_Simp_simp(x_305, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_304);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_274, x_268, x_307, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_308);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_309;
}
else
{
uint8_t x_310; 
lean_dec(x_274);
lean_dec(x_268);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_310 = !lean_is_exclusive(x_306);
if (x_310 == 0)
{
return x_306;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_306, 0);
x_312 = lean_ctor_get(x_306, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_306);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
uint8_t x_314; 
lean_dec(x_300);
lean_dec(x_274);
lean_dec(x_268);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_314 = !lean_is_exclusive(x_303);
if (x_314 == 0)
{
return x_303;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_303, 0);
x_316 = lean_ctor_get(x_303, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_303);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
else
{
uint8_t x_318; 
lean_dec(x_274);
lean_dec(x_268);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_318 = !lean_is_exclusive(x_299);
if (x_318 == 0)
{
return x_299;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_299, 0);
x_320 = lean_ctor_get(x_299, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_299);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_258);
x_322 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_269);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec(x_322);
x_324 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_324, 0, x_3);
lean_closure_set(x_324, 1, x_4);
lean_closure_set(x_324, 2, x_5);
lean_closure_set(x_324, 3, x_27);
lean_closure_set(x_324, 4, x_24);
lean_closure_set(x_324, 5, x_26);
lean_closure_set(x_324, 6, x_2);
lean_closure_set(x_324, 7, x_23);
x_325 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_268, x_324, x_6, x_7, x_8, x_9, x_323);
if (lean_obj_tag(x_325) == 0)
{
uint8_t x_326; 
x_326 = !lean_is_exclusive(x_325);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_325, 0);
if (lean_is_scalar(x_22)) {
 x_328 = lean_alloc_ctor(1, 1, 0);
} else {
 x_328 = x_22;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_325, 0, x_328);
return x_325;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_329 = lean_ctor_get(x_325, 0);
x_330 = lean_ctor_get(x_325, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_325);
if (lean_is_scalar(x_22)) {
 x_331 = lean_alloc_ctor(1, 1, 0);
} else {
 x_331 = x_22;
}
lean_ctor_set(x_331, 0, x_329);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
}
else
{
uint8_t x_333; 
lean_dec(x_22);
x_333 = !lean_is_exclusive(x_325);
if (x_333 == 0)
{
return x_325;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_325, 0);
x_335 = lean_ctor_get(x_325, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_325);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
}
else
{
uint8_t x_337; 
lean_dec(x_258);
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
x_337 = !lean_is_exclusive(x_267);
if (x_337 == 0)
{
return x_267;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_267, 0);
x_339 = lean_ctor_get(x_267, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_267);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
}
else
{
uint8_t x_360; 
lean_dec(x_258);
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
x_360 = !lean_is_exclusive(x_263);
if (x_360 == 0)
{
return x_263;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_263, 0);
x_362 = lean_ctor_get(x_263, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_263);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
}
}
else
{
uint8_t x_364; 
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
x_364 = !lean_is_exclusive(x_257);
if (x_364 == 0)
{
return x_257;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_257, 0);
x_366 = lean_ctor_get(x_257, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_257);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
return x_367;
}
}
}
case 3:
{
lean_object* x_368; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_368 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
lean_dec(x_368);
x_371 = lean_ctor_get(x_21, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_21, 1);
lean_inc(x_372);
lean_dec(x_21);
x_373 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_374 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_371, x_372, x_32, x_373, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_370);
lean_dec(x_371);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_453; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
x_453 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_453 == 0)
{
lean_object* x_454; 
x_454 = lean_box(0);
x_377 = x_454;
goto block_452;
}
else
{
uint8_t x_455; 
x_455 = lean_nat_dec_eq(x_24, x_27);
if (x_455 == 0)
{
lean_object* x_456; 
x_456 = lean_box(0);
x_377 = x_456;
goto block_452;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_369);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_457 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_376);
x_458 = lean_ctor_get(x_457, 1);
lean_inc(x_458);
lean_dec(x_457);
x_459 = l_Lean_Compiler_LCNF_Simp_simp(x_375, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_458);
if (lean_obj_tag(x_459) == 0)
{
uint8_t x_460; 
x_460 = !lean_is_exclusive(x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_459, 0);
x_462 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_459, 0, x_462);
return x_459;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_463 = lean_ctor_get(x_459, 0);
x_464 = lean_ctor_get(x_459, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_459);
x_465 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_465, 0, x_463);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_464);
return x_466;
}
}
else
{
uint8_t x_467; 
x_467 = !lean_is_exclusive(x_459);
if (x_467 == 0)
{
return x_459;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_459, 0);
x_469 = lean_ctor_get(x_459, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_459);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
return x_470;
}
}
}
}
block_452:
{
lean_object* x_378; 
lean_dec(x_377);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_378 = l_Lean_Compiler_LCNF_Simp_simp(x_375, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_376);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
lean_inc(x_379);
x_381 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_379);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
lean_dec(x_22);
x_382 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_380);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec(x_382);
x_384 = l_Lean_Compiler_LCNF_mkAuxParam(x_369, x_373, x_6, x_7, x_8, x_9, x_383);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; 
lean_dec(x_27);
lean_dec(x_23);
x_388 = lean_ctor_get(x_385, 0);
lean_inc(x_388);
x_389 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_388, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_386);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
lean_dec(x_389);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_391 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_390);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_385, x_379, x_392, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_393);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_394;
}
else
{
uint8_t x_395; 
lean_dec(x_385);
lean_dec(x_379);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_395 = !lean_is_exclusive(x_391);
if (x_395 == 0)
{
return x_391;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_391, 0);
x_397 = lean_ctor_get(x_391, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_391);
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
lean_dec(x_385);
lean_dec(x_379);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_399 = !lean_is_exclusive(x_389);
if (x_399 == 0)
{
return x_389;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_389, 0);
x_401 = lean_ctor_get(x_389, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_389);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
return x_402;
}
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_403 = lean_ctor_get(x_385, 0);
lean_inc(x_403);
x_404 = l_Lean_Expr_fvar___override(x_403);
x_405 = lean_array_get_size(x_23);
x_406 = l_Array_toSubarray___rarg(x_23, x_27, x_405);
x_407 = l_Array_ofSubarray___rarg(x_406);
x_408 = l_Lean_mkAppN(x_404, x_407);
x_409 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_410 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_408, x_409, x_6, x_7, x_8, x_9, x_386);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = lean_ctor_get(x_411, 0);
lean_inc(x_413);
x_414 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_413, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_412);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
lean_dec(x_414);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_417 = l_Lean_Compiler_LCNF_Simp_simp(x_416, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_415);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_385, x_379, x_418, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_419);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_420;
}
else
{
uint8_t x_421; 
lean_dec(x_385);
lean_dec(x_379);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_421 = !lean_is_exclusive(x_417);
if (x_421 == 0)
{
return x_417;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_417, 0);
x_423 = lean_ctor_get(x_417, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_417);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
}
else
{
uint8_t x_425; 
lean_dec(x_411);
lean_dec(x_385);
lean_dec(x_379);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_425 = !lean_is_exclusive(x_414);
if (x_425 == 0)
{
return x_414;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_414, 0);
x_427 = lean_ctor_get(x_414, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_414);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
return x_428;
}
}
}
else
{
uint8_t x_429; 
lean_dec(x_385);
lean_dec(x_379);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_429 = !lean_is_exclusive(x_410);
if (x_429 == 0)
{
return x_410;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_410, 0);
x_431 = lean_ctor_get(x_410, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_410);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_369);
x_433 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_380);
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
lean_dec(x_433);
x_435 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_435, 0, x_3);
lean_closure_set(x_435, 1, x_4);
lean_closure_set(x_435, 2, x_5);
lean_closure_set(x_435, 3, x_27);
lean_closure_set(x_435, 4, x_24);
lean_closure_set(x_435, 5, x_26);
lean_closure_set(x_435, 6, x_2);
lean_closure_set(x_435, 7, x_23);
x_436 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_379, x_435, x_6, x_7, x_8, x_9, x_434);
if (lean_obj_tag(x_436) == 0)
{
uint8_t x_437; 
x_437 = !lean_is_exclusive(x_436);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; 
x_438 = lean_ctor_get(x_436, 0);
if (lean_is_scalar(x_22)) {
 x_439 = lean_alloc_ctor(1, 1, 0);
} else {
 x_439 = x_22;
}
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_436, 0, x_439);
return x_436;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_440 = lean_ctor_get(x_436, 0);
x_441 = lean_ctor_get(x_436, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_436);
if (lean_is_scalar(x_22)) {
 x_442 = lean_alloc_ctor(1, 1, 0);
} else {
 x_442 = x_22;
}
lean_ctor_set(x_442, 0, x_440);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_441);
return x_443;
}
}
else
{
uint8_t x_444; 
lean_dec(x_22);
x_444 = !lean_is_exclusive(x_436);
if (x_444 == 0)
{
return x_436;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_436, 0);
x_446 = lean_ctor_get(x_436, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_436);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_369);
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
x_448 = !lean_is_exclusive(x_378);
if (x_448 == 0)
{
return x_378;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_378, 0);
x_450 = lean_ctor_get(x_378, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_378);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
return x_451;
}
}
}
}
else
{
uint8_t x_471; 
lean_dec(x_369);
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
x_471 = !lean_is_exclusive(x_374);
if (x_471 == 0)
{
return x_374;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_374, 0);
x_473 = lean_ctor_get(x_374, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_374);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
else
{
uint8_t x_475; 
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
x_475 = !lean_is_exclusive(x_368);
if (x_475 == 0)
{
return x_368;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_368, 0);
x_477 = lean_ctor_get(x_368, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_368);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
case 4:
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_34, 0);
lean_inc(x_479);
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_479);
x_480 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_479, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec(x_480);
x_483 = lean_ctor_get(x_3, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_3, 1);
lean_inc(x_484);
x_485 = lean_ctor_get(x_3, 2);
lean_inc(x_485);
lean_inc(x_479);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_479);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_ctor_get(x_3, 3);
lean_inc(x_487);
lean_dec(x_3);
x_488 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_487, x_479, x_481);
x_489 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_489, 0, x_483);
lean_ctor_set(x_489, 1, x_484);
lean_ctor_set(x_489, 2, x_486);
lean_ctor_set(x_489, 3, x_488);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_490 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_482);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
x_493 = lean_ctor_get(x_21, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_21, 1);
lean_inc(x_494);
lean_dec(x_21);
x_495 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_496 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_493, x_494, x_32, x_495, x_489, x_4, x_5, x_6, x_7, x_8, x_9, x_492);
lean_dec(x_493);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_575; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
x_575 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_575 == 0)
{
lean_object* x_576; 
x_576 = lean_box(0);
x_499 = x_576;
goto block_574;
}
else
{
uint8_t x_577; 
x_577 = lean_nat_dec_eq(x_24, x_27);
if (x_577 == 0)
{
lean_object* x_578; 
x_578 = lean_box(0);
x_499 = x_578;
goto block_574;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec(x_491);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_579 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_498);
x_580 = lean_ctor_get(x_579, 1);
lean_inc(x_580);
lean_dec(x_579);
x_581 = l_Lean_Compiler_LCNF_Simp_simp(x_497, x_489, x_4, x_5, x_6, x_7, x_8, x_9, x_580);
if (lean_obj_tag(x_581) == 0)
{
uint8_t x_582; 
x_582 = !lean_is_exclusive(x_581);
if (x_582 == 0)
{
lean_object* x_583; lean_object* x_584; 
x_583 = lean_ctor_get(x_581, 0);
x_584 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_584, 0, x_583);
lean_ctor_set(x_581, 0, x_584);
return x_581;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_585 = lean_ctor_get(x_581, 0);
x_586 = lean_ctor_get(x_581, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_581);
x_587 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_587, 0, x_585);
x_588 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_586);
return x_588;
}
}
else
{
uint8_t x_589; 
x_589 = !lean_is_exclusive(x_581);
if (x_589 == 0)
{
return x_581;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_581, 0);
x_591 = lean_ctor_get(x_581, 1);
lean_inc(x_591);
lean_inc(x_590);
lean_dec(x_581);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
}
}
block_574:
{
lean_object* x_500; 
lean_dec(x_499);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_489);
x_500 = l_Lean_Compiler_LCNF_Simp_simp(x_497, x_489, x_4, x_5, x_6, x_7, x_8, x_9, x_498);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
lean_inc(x_501);
x_503 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_501);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; 
lean_dec(x_22);
x_504 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_502);
x_505 = lean_ctor_get(x_504, 1);
lean_inc(x_505);
lean_dec(x_504);
x_506 = l_Lean_Compiler_LCNF_mkAuxParam(x_491, x_495, x_6, x_7, x_8, x_9, x_505);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_509 == 0)
{
lean_object* x_510; lean_object* x_511; 
lean_dec(x_27);
lean_dec(x_23);
x_510 = lean_ctor_get(x_507, 0);
lean_inc(x_510);
x_511 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_510, x_489, x_4, x_5, x_6, x_7, x_8, x_9, x_508);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; 
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
lean_dec(x_511);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_489);
x_513 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_9, x_512);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_507, x_501, x_514, x_489, x_4, x_5, x_6, x_7, x_8, x_9, x_515);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_489);
return x_516;
}
else
{
uint8_t x_517; 
lean_dec(x_507);
lean_dec(x_501);
lean_dec(x_489);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_517 = !lean_is_exclusive(x_513);
if (x_517 == 0)
{
return x_513;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_513, 0);
x_519 = lean_ctor_get(x_513, 1);
lean_inc(x_519);
lean_inc(x_518);
lean_dec(x_513);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
return x_520;
}
}
}
else
{
uint8_t x_521; 
lean_dec(x_507);
lean_dec(x_501);
lean_dec(x_489);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_521 = !lean_is_exclusive(x_511);
if (x_521 == 0)
{
return x_511;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_511, 0);
x_523 = lean_ctor_get(x_511, 1);
lean_inc(x_523);
lean_inc(x_522);
lean_dec(x_511);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
return x_524;
}
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_525 = lean_ctor_get(x_507, 0);
lean_inc(x_525);
x_526 = l_Lean_Expr_fvar___override(x_525);
x_527 = lean_array_get_size(x_23);
x_528 = l_Array_toSubarray___rarg(x_23, x_27, x_527);
x_529 = l_Array_ofSubarray___rarg(x_528);
x_530 = l_Lean_mkAppN(x_526, x_529);
x_531 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_532 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_530, x_531, x_6, x_7, x_8, x_9, x_508);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
lean_dec(x_532);
x_535 = lean_ctor_get(x_533, 0);
lean_inc(x_535);
x_536 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_535, x_489, x_4, x_5, x_6, x_7, x_8, x_9, x_534);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_537 = lean_ctor_get(x_536, 1);
lean_inc(x_537);
lean_dec(x_536);
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_533);
lean_ctor_set(x_538, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_489);
x_539 = l_Lean_Compiler_LCNF_Simp_simp(x_538, x_489, x_4, x_5, x_6, x_7, x_8, x_9, x_537);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_542 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_507, x_501, x_540, x_489, x_4, x_5, x_6, x_7, x_8, x_9, x_541);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_489);
return x_542;
}
else
{
uint8_t x_543; 
lean_dec(x_507);
lean_dec(x_501);
lean_dec(x_489);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_547; 
lean_dec(x_533);
lean_dec(x_507);
lean_dec(x_501);
lean_dec(x_489);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_547 = !lean_is_exclusive(x_536);
if (x_547 == 0)
{
return x_536;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_ctor_get(x_536, 0);
x_549 = lean_ctor_get(x_536, 1);
lean_inc(x_549);
lean_inc(x_548);
lean_dec(x_536);
x_550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_550, 0, x_548);
lean_ctor_set(x_550, 1, x_549);
return x_550;
}
}
}
else
{
uint8_t x_551; 
lean_dec(x_507);
lean_dec(x_501);
lean_dec(x_489);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_551 = !lean_is_exclusive(x_532);
if (x_551 == 0)
{
return x_532;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_532, 0);
x_553 = lean_ctor_get(x_532, 1);
lean_inc(x_553);
lean_inc(x_552);
lean_dec(x_532);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_552);
lean_ctor_set(x_554, 1, x_553);
return x_554;
}
}
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_491);
x_555 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_502);
x_556 = lean_ctor_get(x_555, 1);
lean_inc(x_556);
lean_dec(x_555);
x_557 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_557, 0, x_489);
lean_closure_set(x_557, 1, x_4);
lean_closure_set(x_557, 2, x_5);
lean_closure_set(x_557, 3, x_27);
lean_closure_set(x_557, 4, x_24);
lean_closure_set(x_557, 5, x_26);
lean_closure_set(x_557, 6, x_2);
lean_closure_set(x_557, 7, x_23);
x_558 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_501, x_557, x_6, x_7, x_8, x_9, x_556);
if (lean_obj_tag(x_558) == 0)
{
uint8_t x_559; 
x_559 = !lean_is_exclusive(x_558);
if (x_559 == 0)
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_ctor_get(x_558, 0);
if (lean_is_scalar(x_22)) {
 x_561 = lean_alloc_ctor(1, 1, 0);
} else {
 x_561 = x_22;
}
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_558, 0, x_561);
return x_558;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_562 = lean_ctor_get(x_558, 0);
x_563 = lean_ctor_get(x_558, 1);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_558);
if (lean_is_scalar(x_22)) {
 x_564 = lean_alloc_ctor(1, 1, 0);
} else {
 x_564 = x_22;
}
lean_ctor_set(x_564, 0, x_562);
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_563);
return x_565;
}
}
else
{
uint8_t x_566; 
lean_dec(x_22);
x_566 = !lean_is_exclusive(x_558);
if (x_566 == 0)
{
return x_558;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_558, 0);
x_568 = lean_ctor_get(x_558, 1);
lean_inc(x_568);
lean_inc(x_567);
lean_dec(x_558);
x_569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_569, 0, x_567);
lean_ctor_set(x_569, 1, x_568);
return x_569;
}
}
}
}
else
{
uint8_t x_570; 
lean_dec(x_491);
lean_dec(x_489);
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
x_570 = !lean_is_exclusive(x_500);
if (x_570 == 0)
{
return x_500;
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_571 = lean_ctor_get(x_500, 0);
x_572 = lean_ctor_get(x_500, 1);
lean_inc(x_572);
lean_inc(x_571);
lean_dec(x_500);
x_573 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_573, 0, x_571);
lean_ctor_set(x_573, 1, x_572);
return x_573;
}
}
}
}
else
{
uint8_t x_593; 
lean_dec(x_491);
lean_dec(x_489);
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
x_593 = !lean_is_exclusive(x_496);
if (x_593 == 0)
{
return x_496;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_594 = lean_ctor_get(x_496, 0);
x_595 = lean_ctor_get(x_496, 1);
lean_inc(x_595);
lean_inc(x_594);
lean_dec(x_496);
x_596 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_596, 0, x_594);
lean_ctor_set(x_596, 1, x_595);
return x_596;
}
}
}
else
{
uint8_t x_597; 
lean_dec(x_489);
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
x_597 = !lean_is_exclusive(x_490);
if (x_597 == 0)
{
return x_490;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_490, 0);
x_599 = lean_ctor_get(x_490, 1);
lean_inc(x_599);
lean_inc(x_598);
lean_dec(x_490);
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
return x_600;
}
}
}
else
{
uint8_t x_601; 
lean_dec(x_479);
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
x_601 = !lean_is_exclusive(x_480);
if (x_601 == 0)
{
return x_480;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_480, 0);
x_603 = lean_ctor_get(x_480, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_480);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
case 5:
{
lean_object* x_605; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_605 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; lean_object* x_611; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
lean_dec(x_605);
x_608 = lean_ctor_get(x_21, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_21, 1);
lean_inc(x_609);
lean_dec(x_21);
x_610 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_611 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_608, x_609, x_32, x_610, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_607);
lean_dec(x_608);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_690; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_690 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_690 == 0)
{
lean_object* x_691; 
x_691 = lean_box(0);
x_614 = x_691;
goto block_689;
}
else
{
uint8_t x_692; 
x_692 = lean_nat_dec_eq(x_24, x_27);
if (x_692 == 0)
{
lean_object* x_693; 
x_693 = lean_box(0);
x_614 = x_693;
goto block_689;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_606);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_694 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_613);
x_695 = lean_ctor_get(x_694, 1);
lean_inc(x_695);
lean_dec(x_694);
x_696 = l_Lean_Compiler_LCNF_Simp_simp(x_612, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_695);
if (lean_obj_tag(x_696) == 0)
{
uint8_t x_697; 
x_697 = !lean_is_exclusive(x_696);
if (x_697 == 0)
{
lean_object* x_698; lean_object* x_699; 
x_698 = lean_ctor_get(x_696, 0);
x_699 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_696, 0, x_699);
return x_696;
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_700 = lean_ctor_get(x_696, 0);
x_701 = lean_ctor_get(x_696, 1);
lean_inc(x_701);
lean_inc(x_700);
lean_dec(x_696);
x_702 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_702, 0, x_700);
x_703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_701);
return x_703;
}
}
else
{
uint8_t x_704; 
x_704 = !lean_is_exclusive(x_696);
if (x_704 == 0)
{
return x_696;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_705 = lean_ctor_get(x_696, 0);
x_706 = lean_ctor_get(x_696, 1);
lean_inc(x_706);
lean_inc(x_705);
lean_dec(x_696);
x_707 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
return x_707;
}
}
}
}
block_689:
{
lean_object* x_615; 
lean_dec(x_614);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_615 = l_Lean_Compiler_LCNF_Simp_simp(x_612, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_613);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; lean_object* x_617; uint8_t x_618; 
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
lean_dec(x_615);
lean_inc(x_616);
x_618 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_616);
if (x_618 == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
lean_dec(x_22);
x_619 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_617);
x_620 = lean_ctor_get(x_619, 1);
lean_inc(x_620);
lean_dec(x_619);
x_621 = l_Lean_Compiler_LCNF_mkAuxParam(x_606, x_610, x_6, x_7, x_8, x_9, x_620);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
x_624 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_624 == 0)
{
lean_object* x_625; lean_object* x_626; 
lean_dec(x_27);
lean_dec(x_23);
x_625 = lean_ctor_get(x_622, 0);
lean_inc(x_625);
x_626 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_625, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_623);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; 
x_627 = lean_ctor_get(x_626, 1);
lean_inc(x_627);
lean_dec(x_626);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_628 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_627);
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_628, 1);
lean_inc(x_630);
lean_dec(x_628);
x_631 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_622, x_616, x_629, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_630);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_631;
}
else
{
uint8_t x_632; 
lean_dec(x_622);
lean_dec(x_616);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_632 = !lean_is_exclusive(x_628);
if (x_632 == 0)
{
return x_628;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_628, 0);
x_634 = lean_ctor_get(x_628, 1);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_628);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
return x_635;
}
}
}
else
{
uint8_t x_636; 
lean_dec(x_622);
lean_dec(x_616);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_636 = !lean_is_exclusive(x_626);
if (x_636 == 0)
{
return x_626;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_637 = lean_ctor_get(x_626, 0);
x_638 = lean_ctor_get(x_626, 1);
lean_inc(x_638);
lean_inc(x_637);
lean_dec(x_626);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_637);
lean_ctor_set(x_639, 1, x_638);
return x_639;
}
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_640 = lean_ctor_get(x_622, 0);
lean_inc(x_640);
x_641 = l_Lean_Expr_fvar___override(x_640);
x_642 = lean_array_get_size(x_23);
x_643 = l_Array_toSubarray___rarg(x_23, x_27, x_642);
x_644 = l_Array_ofSubarray___rarg(x_643);
x_645 = l_Lean_mkAppN(x_641, x_644);
x_646 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_647 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_645, x_646, x_6, x_7, x_8, x_9, x_623);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_647, 1);
lean_inc(x_649);
lean_dec(x_647);
x_650 = lean_ctor_get(x_648, 0);
lean_inc(x_650);
x_651 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_650, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_649);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_651, 1);
lean_inc(x_652);
lean_dec(x_651);
x_653 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_653, 0, x_648);
lean_ctor_set(x_653, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_654 = l_Lean_Compiler_LCNF_Simp_simp(x_653, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_652);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
lean_dec(x_654);
x_657 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_622, x_616, x_655, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_656);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_657;
}
else
{
uint8_t x_658; 
lean_dec(x_622);
lean_dec(x_616);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_658 = !lean_is_exclusive(x_654);
if (x_658 == 0)
{
return x_654;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_654, 0);
x_660 = lean_ctor_get(x_654, 1);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_654);
x_661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
return x_661;
}
}
}
else
{
uint8_t x_662; 
lean_dec(x_648);
lean_dec(x_622);
lean_dec(x_616);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_662 = !lean_is_exclusive(x_651);
if (x_662 == 0)
{
return x_651;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_651, 0);
x_664 = lean_ctor_get(x_651, 1);
lean_inc(x_664);
lean_inc(x_663);
lean_dec(x_651);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
return x_665;
}
}
}
else
{
uint8_t x_666; 
lean_dec(x_622);
lean_dec(x_616);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_666 = !lean_is_exclusive(x_647);
if (x_666 == 0)
{
return x_647;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_667 = lean_ctor_get(x_647, 0);
x_668 = lean_ctor_get(x_647, 1);
lean_inc(x_668);
lean_inc(x_667);
lean_dec(x_647);
x_669 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_669, 0, x_667);
lean_ctor_set(x_669, 1, x_668);
return x_669;
}
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_606);
x_670 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_617);
x_671 = lean_ctor_get(x_670, 1);
lean_inc(x_671);
lean_dec(x_670);
x_672 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_672, 0, x_3);
lean_closure_set(x_672, 1, x_4);
lean_closure_set(x_672, 2, x_5);
lean_closure_set(x_672, 3, x_27);
lean_closure_set(x_672, 4, x_24);
lean_closure_set(x_672, 5, x_26);
lean_closure_set(x_672, 6, x_2);
lean_closure_set(x_672, 7, x_23);
x_673 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_616, x_672, x_6, x_7, x_8, x_9, x_671);
if (lean_obj_tag(x_673) == 0)
{
uint8_t x_674; 
x_674 = !lean_is_exclusive(x_673);
if (x_674 == 0)
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_673, 0);
if (lean_is_scalar(x_22)) {
 x_676 = lean_alloc_ctor(1, 1, 0);
} else {
 x_676 = x_22;
}
lean_ctor_set(x_676, 0, x_675);
lean_ctor_set(x_673, 0, x_676);
return x_673;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_677 = lean_ctor_get(x_673, 0);
x_678 = lean_ctor_get(x_673, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_673);
if (lean_is_scalar(x_22)) {
 x_679 = lean_alloc_ctor(1, 1, 0);
} else {
 x_679 = x_22;
}
lean_ctor_set(x_679, 0, x_677);
x_680 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_678);
return x_680;
}
}
else
{
uint8_t x_681; 
lean_dec(x_22);
x_681 = !lean_is_exclusive(x_673);
if (x_681 == 0)
{
return x_673;
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_682 = lean_ctor_get(x_673, 0);
x_683 = lean_ctor_get(x_673, 1);
lean_inc(x_683);
lean_inc(x_682);
lean_dec(x_673);
x_684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_684, 0, x_682);
lean_ctor_set(x_684, 1, x_683);
return x_684;
}
}
}
}
else
{
uint8_t x_685; 
lean_dec(x_606);
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
x_685 = !lean_is_exclusive(x_615);
if (x_685 == 0)
{
return x_615;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_615, 0);
x_687 = lean_ctor_get(x_615, 1);
lean_inc(x_687);
lean_inc(x_686);
lean_dec(x_615);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_686);
lean_ctor_set(x_688, 1, x_687);
return x_688;
}
}
}
}
else
{
uint8_t x_708; 
lean_dec(x_606);
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
x_708 = !lean_is_exclusive(x_611);
if (x_708 == 0)
{
return x_611;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_611, 0);
x_710 = lean_ctor_get(x_611, 1);
lean_inc(x_710);
lean_inc(x_709);
lean_dec(x_611);
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
return x_711;
}
}
}
else
{
uint8_t x_712; 
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
x_712 = !lean_is_exclusive(x_605);
if (x_712 == 0)
{
return x_605;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_605, 0);
x_714 = lean_ctor_get(x_605, 1);
lean_inc(x_714);
lean_inc(x_713);
lean_dec(x_605);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
return x_715;
}
}
}
case 6:
{
lean_object* x_716; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_716 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_716) == 0)
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; lean_object* x_722; 
x_717 = lean_ctor_get(x_716, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_716, 1);
lean_inc(x_718);
lean_dec(x_716);
x_719 = lean_ctor_get(x_21, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_21, 1);
lean_inc(x_720);
lean_dec(x_21);
x_721 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_722 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_719, x_720, x_32, x_721, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_718);
lean_dec(x_719);
if (lean_obj_tag(x_722) == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; uint8_t x_801; 
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_722, 1);
lean_inc(x_724);
lean_dec(x_722);
x_801 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_801 == 0)
{
lean_object* x_802; 
x_802 = lean_box(0);
x_725 = x_802;
goto block_800;
}
else
{
uint8_t x_803; 
x_803 = lean_nat_dec_eq(x_24, x_27);
if (x_803 == 0)
{
lean_object* x_804; 
x_804 = lean_box(0);
x_725 = x_804;
goto block_800;
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_717);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_805 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_724);
x_806 = lean_ctor_get(x_805, 1);
lean_inc(x_806);
lean_dec(x_805);
x_807 = l_Lean_Compiler_LCNF_Simp_simp(x_723, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_806);
if (lean_obj_tag(x_807) == 0)
{
uint8_t x_808; 
x_808 = !lean_is_exclusive(x_807);
if (x_808 == 0)
{
lean_object* x_809; lean_object* x_810; 
x_809 = lean_ctor_get(x_807, 0);
x_810 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_807, 0, x_810);
return x_807;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_807, 0);
x_812 = lean_ctor_get(x_807, 1);
lean_inc(x_812);
lean_inc(x_811);
lean_dec(x_807);
x_813 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_813, 0, x_811);
x_814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_814, 0, x_813);
lean_ctor_set(x_814, 1, x_812);
return x_814;
}
}
else
{
uint8_t x_815; 
x_815 = !lean_is_exclusive(x_807);
if (x_815 == 0)
{
return x_807;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_816 = lean_ctor_get(x_807, 0);
x_817 = lean_ctor_get(x_807, 1);
lean_inc(x_817);
lean_inc(x_816);
lean_dec(x_807);
x_818 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_818, 0, x_816);
lean_ctor_set(x_818, 1, x_817);
return x_818;
}
}
}
}
block_800:
{
lean_object* x_726; 
lean_dec(x_725);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_726 = l_Lean_Compiler_LCNF_Simp_simp(x_723, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_724);
if (lean_obj_tag(x_726) == 0)
{
lean_object* x_727; lean_object* x_728; uint8_t x_729; 
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_726, 1);
lean_inc(x_728);
lean_dec(x_726);
lean_inc(x_727);
x_729 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_727);
if (x_729 == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; uint8_t x_735; 
lean_dec(x_22);
x_730 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_728);
x_731 = lean_ctor_get(x_730, 1);
lean_inc(x_731);
lean_dec(x_730);
x_732 = l_Lean_Compiler_LCNF_mkAuxParam(x_717, x_721, x_6, x_7, x_8, x_9, x_731);
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec(x_732);
x_735 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_735 == 0)
{
lean_object* x_736; lean_object* x_737; 
lean_dec(x_27);
lean_dec(x_23);
x_736 = lean_ctor_get(x_733, 0);
lean_inc(x_736);
x_737 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_736, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_734);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; lean_object* x_739; 
x_738 = lean_ctor_get(x_737, 1);
lean_inc(x_738);
lean_dec(x_737);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_739 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_738);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_739, 1);
lean_inc(x_741);
lean_dec(x_739);
x_742 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_733, x_727, x_740, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_741);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_742;
}
else
{
uint8_t x_743; 
lean_dec(x_733);
lean_dec(x_727);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_743 = !lean_is_exclusive(x_739);
if (x_743 == 0)
{
return x_739;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_744 = lean_ctor_get(x_739, 0);
x_745 = lean_ctor_get(x_739, 1);
lean_inc(x_745);
lean_inc(x_744);
lean_dec(x_739);
x_746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_746, 0, x_744);
lean_ctor_set(x_746, 1, x_745);
return x_746;
}
}
}
else
{
uint8_t x_747; 
lean_dec(x_733);
lean_dec(x_727);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_747 = !lean_is_exclusive(x_737);
if (x_747 == 0)
{
return x_737;
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_748 = lean_ctor_get(x_737, 0);
x_749 = lean_ctor_get(x_737, 1);
lean_inc(x_749);
lean_inc(x_748);
lean_dec(x_737);
x_750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_750, 0, x_748);
lean_ctor_set(x_750, 1, x_749);
return x_750;
}
}
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_751 = lean_ctor_get(x_733, 0);
lean_inc(x_751);
x_752 = l_Lean_Expr_fvar___override(x_751);
x_753 = lean_array_get_size(x_23);
x_754 = l_Array_toSubarray___rarg(x_23, x_27, x_753);
x_755 = l_Array_ofSubarray___rarg(x_754);
x_756 = l_Lean_mkAppN(x_752, x_755);
x_757 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_758 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_756, x_757, x_6, x_7, x_8, x_9, x_734);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
x_761 = lean_ctor_get(x_759, 0);
lean_inc(x_761);
x_762 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_761, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_760);
if (lean_obj_tag(x_762) == 0)
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_763 = lean_ctor_get(x_762, 1);
lean_inc(x_763);
lean_dec(x_762);
x_764 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_764, 0, x_759);
lean_ctor_set(x_764, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_765 = l_Lean_Compiler_LCNF_Simp_simp(x_764, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_763);
if (lean_obj_tag(x_765) == 0)
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_766 = lean_ctor_get(x_765, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_765, 1);
lean_inc(x_767);
lean_dec(x_765);
x_768 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_733, x_727, x_766, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_767);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_768;
}
else
{
uint8_t x_769; 
lean_dec(x_733);
lean_dec(x_727);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_769 = !lean_is_exclusive(x_765);
if (x_769 == 0)
{
return x_765;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_765, 0);
x_771 = lean_ctor_get(x_765, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_765);
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
else
{
uint8_t x_773; 
lean_dec(x_759);
lean_dec(x_733);
lean_dec(x_727);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_773 = !lean_is_exclusive(x_762);
if (x_773 == 0)
{
return x_762;
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = lean_ctor_get(x_762, 0);
x_775 = lean_ctor_get(x_762, 1);
lean_inc(x_775);
lean_inc(x_774);
lean_dec(x_762);
x_776 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_776, 0, x_774);
lean_ctor_set(x_776, 1, x_775);
return x_776;
}
}
}
else
{
uint8_t x_777; 
lean_dec(x_733);
lean_dec(x_727);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_777 = !lean_is_exclusive(x_758);
if (x_777 == 0)
{
return x_758;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_758, 0);
x_779 = lean_ctor_get(x_758, 1);
lean_inc(x_779);
lean_inc(x_778);
lean_dec(x_758);
x_780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_780, 0, x_778);
lean_ctor_set(x_780, 1, x_779);
return x_780;
}
}
}
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
lean_dec(x_717);
x_781 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_728);
x_782 = lean_ctor_get(x_781, 1);
lean_inc(x_782);
lean_dec(x_781);
x_783 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_783, 0, x_3);
lean_closure_set(x_783, 1, x_4);
lean_closure_set(x_783, 2, x_5);
lean_closure_set(x_783, 3, x_27);
lean_closure_set(x_783, 4, x_24);
lean_closure_set(x_783, 5, x_26);
lean_closure_set(x_783, 6, x_2);
lean_closure_set(x_783, 7, x_23);
x_784 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_727, x_783, x_6, x_7, x_8, x_9, x_782);
if (lean_obj_tag(x_784) == 0)
{
uint8_t x_785; 
x_785 = !lean_is_exclusive(x_784);
if (x_785 == 0)
{
lean_object* x_786; lean_object* x_787; 
x_786 = lean_ctor_get(x_784, 0);
if (lean_is_scalar(x_22)) {
 x_787 = lean_alloc_ctor(1, 1, 0);
} else {
 x_787 = x_22;
}
lean_ctor_set(x_787, 0, x_786);
lean_ctor_set(x_784, 0, x_787);
return x_784;
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_788 = lean_ctor_get(x_784, 0);
x_789 = lean_ctor_get(x_784, 1);
lean_inc(x_789);
lean_inc(x_788);
lean_dec(x_784);
if (lean_is_scalar(x_22)) {
 x_790 = lean_alloc_ctor(1, 1, 0);
} else {
 x_790 = x_22;
}
lean_ctor_set(x_790, 0, x_788);
x_791 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_791, 0, x_790);
lean_ctor_set(x_791, 1, x_789);
return x_791;
}
}
else
{
uint8_t x_792; 
lean_dec(x_22);
x_792 = !lean_is_exclusive(x_784);
if (x_792 == 0)
{
return x_784;
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_793 = lean_ctor_get(x_784, 0);
x_794 = lean_ctor_get(x_784, 1);
lean_inc(x_794);
lean_inc(x_793);
lean_dec(x_784);
x_795 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_795, 0, x_793);
lean_ctor_set(x_795, 1, x_794);
return x_795;
}
}
}
}
else
{
uint8_t x_796; 
lean_dec(x_717);
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
x_796 = !lean_is_exclusive(x_726);
if (x_796 == 0)
{
return x_726;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_726, 0);
x_798 = lean_ctor_get(x_726, 1);
lean_inc(x_798);
lean_inc(x_797);
lean_dec(x_726);
x_799 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_799, 0, x_797);
lean_ctor_set(x_799, 1, x_798);
return x_799;
}
}
}
}
else
{
uint8_t x_819; 
lean_dec(x_717);
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
x_819 = !lean_is_exclusive(x_722);
if (x_819 == 0)
{
return x_722;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_820 = lean_ctor_get(x_722, 0);
x_821 = lean_ctor_get(x_722, 1);
lean_inc(x_821);
lean_inc(x_820);
lean_dec(x_722);
x_822 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_822, 0, x_820);
lean_ctor_set(x_822, 1, x_821);
return x_822;
}
}
}
else
{
uint8_t x_823; 
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
x_823 = !lean_is_exclusive(x_716);
if (x_823 == 0)
{
return x_716;
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_824 = lean_ctor_get(x_716, 0);
x_825 = lean_ctor_get(x_716, 1);
lean_inc(x_825);
lean_inc(x_824);
lean_dec(x_716);
x_826 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_826, 0, x_824);
lean_ctor_set(x_826, 1, x_825);
return x_826;
}
}
}
case 7:
{
lean_object* x_827; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_827 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_827) == 0)
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; uint8_t x_832; lean_object* x_833; 
x_828 = lean_ctor_get(x_827, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_827, 1);
lean_inc(x_829);
lean_dec(x_827);
x_830 = lean_ctor_get(x_21, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_21, 1);
lean_inc(x_831);
lean_dec(x_21);
x_832 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_833 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_830, x_831, x_32, x_832, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_829);
lean_dec(x_830);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; uint8_t x_912; 
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
lean_dec(x_833);
x_912 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_912 == 0)
{
lean_object* x_913; 
x_913 = lean_box(0);
x_836 = x_913;
goto block_911;
}
else
{
uint8_t x_914; 
x_914 = lean_nat_dec_eq(x_24, x_27);
if (x_914 == 0)
{
lean_object* x_915; 
x_915 = lean_box(0);
x_836 = x_915;
goto block_911;
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
lean_dec(x_828);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_916 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_835);
x_917 = lean_ctor_get(x_916, 1);
lean_inc(x_917);
lean_dec(x_916);
x_918 = l_Lean_Compiler_LCNF_Simp_simp(x_834, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_917);
if (lean_obj_tag(x_918) == 0)
{
uint8_t x_919; 
x_919 = !lean_is_exclusive(x_918);
if (x_919 == 0)
{
lean_object* x_920; lean_object* x_921; 
x_920 = lean_ctor_get(x_918, 0);
x_921 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_921, 0, x_920);
lean_ctor_set(x_918, 0, x_921);
return x_918;
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; 
x_922 = lean_ctor_get(x_918, 0);
x_923 = lean_ctor_get(x_918, 1);
lean_inc(x_923);
lean_inc(x_922);
lean_dec(x_918);
x_924 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_924, 0, x_922);
x_925 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_925, 0, x_924);
lean_ctor_set(x_925, 1, x_923);
return x_925;
}
}
else
{
uint8_t x_926; 
x_926 = !lean_is_exclusive(x_918);
if (x_926 == 0)
{
return x_918;
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; 
x_927 = lean_ctor_get(x_918, 0);
x_928 = lean_ctor_get(x_918, 1);
lean_inc(x_928);
lean_inc(x_927);
lean_dec(x_918);
x_929 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_929, 0, x_927);
lean_ctor_set(x_929, 1, x_928);
return x_929;
}
}
}
}
block_911:
{
lean_object* x_837; 
lean_dec(x_836);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_837 = l_Lean_Compiler_LCNF_Simp_simp(x_834, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_835);
if (lean_obj_tag(x_837) == 0)
{
lean_object* x_838; lean_object* x_839; uint8_t x_840; 
x_838 = lean_ctor_get(x_837, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_837, 1);
lean_inc(x_839);
lean_dec(x_837);
lean_inc(x_838);
x_840 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_838);
if (x_840 == 0)
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; uint8_t x_846; 
lean_dec(x_22);
x_841 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_839);
x_842 = lean_ctor_get(x_841, 1);
lean_inc(x_842);
lean_dec(x_841);
x_843 = l_Lean_Compiler_LCNF_mkAuxParam(x_828, x_832, x_6, x_7, x_8, x_9, x_842);
x_844 = lean_ctor_get(x_843, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_843, 1);
lean_inc(x_845);
lean_dec(x_843);
x_846 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_846 == 0)
{
lean_object* x_847; lean_object* x_848; 
lean_dec(x_27);
lean_dec(x_23);
x_847 = lean_ctor_get(x_844, 0);
lean_inc(x_847);
x_848 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_847, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_845);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; lean_object* x_850; 
x_849 = lean_ctor_get(x_848, 1);
lean_inc(x_849);
lean_dec(x_848);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_850 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_849);
if (lean_obj_tag(x_850) == 0)
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_851 = lean_ctor_get(x_850, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_850, 1);
lean_inc(x_852);
lean_dec(x_850);
x_853 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_844, x_838, x_851, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_852);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_853;
}
else
{
uint8_t x_854; 
lean_dec(x_844);
lean_dec(x_838);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_854 = !lean_is_exclusive(x_850);
if (x_854 == 0)
{
return x_850;
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; 
x_855 = lean_ctor_get(x_850, 0);
x_856 = lean_ctor_get(x_850, 1);
lean_inc(x_856);
lean_inc(x_855);
lean_dec(x_850);
x_857 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_857, 1, x_856);
return x_857;
}
}
}
else
{
uint8_t x_858; 
lean_dec(x_844);
lean_dec(x_838);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_858 = !lean_is_exclusive(x_848);
if (x_858 == 0)
{
return x_848;
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_859 = lean_ctor_get(x_848, 0);
x_860 = lean_ctor_get(x_848, 1);
lean_inc(x_860);
lean_inc(x_859);
lean_dec(x_848);
x_861 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_861, 0, x_859);
lean_ctor_set(x_861, 1, x_860);
return x_861;
}
}
}
else
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_862 = lean_ctor_get(x_844, 0);
lean_inc(x_862);
x_863 = l_Lean_Expr_fvar___override(x_862);
x_864 = lean_array_get_size(x_23);
x_865 = l_Array_toSubarray___rarg(x_23, x_27, x_864);
x_866 = l_Array_ofSubarray___rarg(x_865);
x_867 = l_Lean_mkAppN(x_863, x_866);
x_868 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_869 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_867, x_868, x_6, x_7, x_8, x_9, x_845);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_ctor_get(x_870, 0);
lean_inc(x_872);
x_873 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_872, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_871);
if (lean_obj_tag(x_873) == 0)
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_874 = lean_ctor_get(x_873, 1);
lean_inc(x_874);
lean_dec(x_873);
x_875 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_875, 0, x_870);
lean_ctor_set(x_875, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_876 = l_Lean_Compiler_LCNF_Simp_simp(x_875, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_874);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 1);
lean_inc(x_878);
lean_dec(x_876);
x_879 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_844, x_838, x_877, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_878);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_879;
}
else
{
uint8_t x_880; 
lean_dec(x_844);
lean_dec(x_838);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_880 = !lean_is_exclusive(x_876);
if (x_880 == 0)
{
return x_876;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_881 = lean_ctor_get(x_876, 0);
x_882 = lean_ctor_get(x_876, 1);
lean_inc(x_882);
lean_inc(x_881);
lean_dec(x_876);
x_883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_883, 0, x_881);
lean_ctor_set(x_883, 1, x_882);
return x_883;
}
}
}
else
{
uint8_t x_884; 
lean_dec(x_870);
lean_dec(x_844);
lean_dec(x_838);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_884 = !lean_is_exclusive(x_873);
if (x_884 == 0)
{
return x_873;
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_885 = lean_ctor_get(x_873, 0);
x_886 = lean_ctor_get(x_873, 1);
lean_inc(x_886);
lean_inc(x_885);
lean_dec(x_873);
x_887 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_887, 0, x_885);
lean_ctor_set(x_887, 1, x_886);
return x_887;
}
}
}
else
{
uint8_t x_888; 
lean_dec(x_844);
lean_dec(x_838);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_888 = !lean_is_exclusive(x_869);
if (x_888 == 0)
{
return x_869;
}
else
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_889 = lean_ctor_get(x_869, 0);
x_890 = lean_ctor_get(x_869, 1);
lean_inc(x_890);
lean_inc(x_889);
lean_dec(x_869);
x_891 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_891, 0, x_889);
lean_ctor_set(x_891, 1, x_890);
return x_891;
}
}
}
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; 
lean_dec(x_828);
x_892 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_839);
x_893 = lean_ctor_get(x_892, 1);
lean_inc(x_893);
lean_dec(x_892);
x_894 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_894, 0, x_3);
lean_closure_set(x_894, 1, x_4);
lean_closure_set(x_894, 2, x_5);
lean_closure_set(x_894, 3, x_27);
lean_closure_set(x_894, 4, x_24);
lean_closure_set(x_894, 5, x_26);
lean_closure_set(x_894, 6, x_2);
lean_closure_set(x_894, 7, x_23);
x_895 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_838, x_894, x_6, x_7, x_8, x_9, x_893);
if (lean_obj_tag(x_895) == 0)
{
uint8_t x_896; 
x_896 = !lean_is_exclusive(x_895);
if (x_896 == 0)
{
lean_object* x_897; lean_object* x_898; 
x_897 = lean_ctor_get(x_895, 0);
if (lean_is_scalar(x_22)) {
 x_898 = lean_alloc_ctor(1, 1, 0);
} else {
 x_898 = x_22;
}
lean_ctor_set(x_898, 0, x_897);
lean_ctor_set(x_895, 0, x_898);
return x_895;
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
x_899 = lean_ctor_get(x_895, 0);
x_900 = lean_ctor_get(x_895, 1);
lean_inc(x_900);
lean_inc(x_899);
lean_dec(x_895);
if (lean_is_scalar(x_22)) {
 x_901 = lean_alloc_ctor(1, 1, 0);
} else {
 x_901 = x_22;
}
lean_ctor_set(x_901, 0, x_899);
x_902 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_902, 0, x_901);
lean_ctor_set(x_902, 1, x_900);
return x_902;
}
}
else
{
uint8_t x_903; 
lean_dec(x_22);
x_903 = !lean_is_exclusive(x_895);
if (x_903 == 0)
{
return x_895;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_904 = lean_ctor_get(x_895, 0);
x_905 = lean_ctor_get(x_895, 1);
lean_inc(x_905);
lean_inc(x_904);
lean_dec(x_895);
x_906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_906, 0, x_904);
lean_ctor_set(x_906, 1, x_905);
return x_906;
}
}
}
}
else
{
uint8_t x_907; 
lean_dec(x_828);
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
x_907 = !lean_is_exclusive(x_837);
if (x_907 == 0)
{
return x_837;
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; 
x_908 = lean_ctor_get(x_837, 0);
x_909 = lean_ctor_get(x_837, 1);
lean_inc(x_909);
lean_inc(x_908);
lean_dec(x_837);
x_910 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_910, 0, x_908);
lean_ctor_set(x_910, 1, x_909);
return x_910;
}
}
}
}
else
{
uint8_t x_930; 
lean_dec(x_828);
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
x_930 = !lean_is_exclusive(x_833);
if (x_930 == 0)
{
return x_833;
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_931 = lean_ctor_get(x_833, 0);
x_932 = lean_ctor_get(x_833, 1);
lean_inc(x_932);
lean_inc(x_931);
lean_dec(x_833);
x_933 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_933, 0, x_931);
lean_ctor_set(x_933, 1, x_932);
return x_933;
}
}
}
else
{
uint8_t x_934; 
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
x_934 = !lean_is_exclusive(x_827);
if (x_934 == 0)
{
return x_827;
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; 
x_935 = lean_ctor_get(x_827, 0);
x_936 = lean_ctor_get(x_827, 1);
lean_inc(x_936);
lean_inc(x_935);
lean_dec(x_827);
x_937 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_937, 0, x_935);
lean_ctor_set(x_937, 1, x_936);
return x_937;
}
}
}
case 8:
{
lean_object* x_938; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_938 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_938) == 0)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; uint8_t x_943; lean_object* x_944; 
x_939 = lean_ctor_get(x_938, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_938, 1);
lean_inc(x_940);
lean_dec(x_938);
x_941 = lean_ctor_get(x_21, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_21, 1);
lean_inc(x_942);
lean_dec(x_21);
x_943 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_944 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_941, x_942, x_32, x_943, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_940);
lean_dec(x_941);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; uint8_t x_1023; 
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_944, 1);
lean_inc(x_946);
lean_dec(x_944);
x_1023 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1023 == 0)
{
lean_object* x_1024; 
x_1024 = lean_box(0);
x_947 = x_1024;
goto block_1022;
}
else
{
uint8_t x_1025; 
x_1025 = lean_nat_dec_eq(x_24, x_27);
if (x_1025 == 0)
{
lean_object* x_1026; 
x_1026 = lean_box(0);
x_947 = x_1026;
goto block_1022;
}
else
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_939);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_1027 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_946);
x_1028 = lean_ctor_get(x_1027, 1);
lean_inc(x_1028);
lean_dec(x_1027);
x_1029 = l_Lean_Compiler_LCNF_Simp_simp(x_945, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1028);
if (lean_obj_tag(x_1029) == 0)
{
uint8_t x_1030; 
x_1030 = !lean_is_exclusive(x_1029);
if (x_1030 == 0)
{
lean_object* x_1031; lean_object* x_1032; 
x_1031 = lean_ctor_get(x_1029, 0);
x_1032 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1032, 0, x_1031);
lean_ctor_set(x_1029, 0, x_1032);
return x_1029;
}
else
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
x_1033 = lean_ctor_get(x_1029, 0);
x_1034 = lean_ctor_get(x_1029, 1);
lean_inc(x_1034);
lean_inc(x_1033);
lean_dec(x_1029);
x_1035 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1035, 0, x_1033);
x_1036 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1036, 0, x_1035);
lean_ctor_set(x_1036, 1, x_1034);
return x_1036;
}
}
else
{
uint8_t x_1037; 
x_1037 = !lean_is_exclusive(x_1029);
if (x_1037 == 0)
{
return x_1029;
}
else
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1038 = lean_ctor_get(x_1029, 0);
x_1039 = lean_ctor_get(x_1029, 1);
lean_inc(x_1039);
lean_inc(x_1038);
lean_dec(x_1029);
x_1040 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1040, 0, x_1038);
lean_ctor_set(x_1040, 1, x_1039);
return x_1040;
}
}
}
}
block_1022:
{
lean_object* x_948; 
lean_dec(x_947);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_948 = l_Lean_Compiler_LCNF_Simp_simp(x_945, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_946);
if (lean_obj_tag(x_948) == 0)
{
lean_object* x_949; lean_object* x_950; uint8_t x_951; 
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
lean_dec(x_948);
lean_inc(x_949);
x_951 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_949);
if (x_951 == 0)
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; uint8_t x_957; 
lean_dec(x_22);
x_952 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_950);
x_953 = lean_ctor_get(x_952, 1);
lean_inc(x_953);
lean_dec(x_952);
x_954 = l_Lean_Compiler_LCNF_mkAuxParam(x_939, x_943, x_6, x_7, x_8, x_9, x_953);
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
lean_dec(x_954);
x_957 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_957 == 0)
{
lean_object* x_958; lean_object* x_959; 
lean_dec(x_27);
lean_dec(x_23);
x_958 = lean_ctor_get(x_955, 0);
lean_inc(x_958);
x_959 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_958, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_956);
if (lean_obj_tag(x_959) == 0)
{
lean_object* x_960; lean_object* x_961; 
x_960 = lean_ctor_get(x_959, 1);
lean_inc(x_960);
lean_dec(x_959);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_961 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_960);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
lean_dec(x_961);
x_964 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_955, x_949, x_962, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_963);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_964;
}
else
{
uint8_t x_965; 
lean_dec(x_955);
lean_dec(x_949);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_965 = !lean_is_exclusive(x_961);
if (x_965 == 0)
{
return x_961;
}
else
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_966 = lean_ctor_get(x_961, 0);
x_967 = lean_ctor_get(x_961, 1);
lean_inc(x_967);
lean_inc(x_966);
lean_dec(x_961);
x_968 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_968, 0, x_966);
lean_ctor_set(x_968, 1, x_967);
return x_968;
}
}
}
else
{
uint8_t x_969; 
lean_dec(x_955);
lean_dec(x_949);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_969 = !lean_is_exclusive(x_959);
if (x_969 == 0)
{
return x_959;
}
else
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; 
x_970 = lean_ctor_get(x_959, 0);
x_971 = lean_ctor_get(x_959, 1);
lean_inc(x_971);
lean_inc(x_970);
lean_dec(x_959);
x_972 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_972, 0, x_970);
lean_ctor_set(x_972, 1, x_971);
return x_972;
}
}
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_973 = lean_ctor_get(x_955, 0);
lean_inc(x_973);
x_974 = l_Lean_Expr_fvar___override(x_973);
x_975 = lean_array_get_size(x_23);
x_976 = l_Array_toSubarray___rarg(x_23, x_27, x_975);
x_977 = l_Array_ofSubarray___rarg(x_976);
x_978 = l_Lean_mkAppN(x_974, x_977);
x_979 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_980 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_978, x_979, x_6, x_7, x_8, x_9, x_956);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_981 = lean_ctor_get(x_980, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_980, 1);
lean_inc(x_982);
lean_dec(x_980);
x_983 = lean_ctor_get(x_981, 0);
lean_inc(x_983);
x_984 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_983, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_982);
if (lean_obj_tag(x_984) == 0)
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_985 = lean_ctor_get(x_984, 1);
lean_inc(x_985);
lean_dec(x_984);
x_986 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_986, 0, x_981);
lean_ctor_set(x_986, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_987 = l_Lean_Compiler_LCNF_Simp_simp(x_986, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_985);
if (lean_obj_tag(x_987) == 0)
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_988 = lean_ctor_get(x_987, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_987, 1);
lean_inc(x_989);
lean_dec(x_987);
x_990 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_955, x_949, x_988, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_989);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_990;
}
else
{
uint8_t x_991; 
lean_dec(x_955);
lean_dec(x_949);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_991 = !lean_is_exclusive(x_987);
if (x_991 == 0)
{
return x_987;
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; 
x_992 = lean_ctor_get(x_987, 0);
x_993 = lean_ctor_get(x_987, 1);
lean_inc(x_993);
lean_inc(x_992);
lean_dec(x_987);
x_994 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_994, 0, x_992);
lean_ctor_set(x_994, 1, x_993);
return x_994;
}
}
}
else
{
uint8_t x_995; 
lean_dec(x_981);
lean_dec(x_955);
lean_dec(x_949);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_995 = !lean_is_exclusive(x_984);
if (x_995 == 0)
{
return x_984;
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_996 = lean_ctor_get(x_984, 0);
x_997 = lean_ctor_get(x_984, 1);
lean_inc(x_997);
lean_inc(x_996);
lean_dec(x_984);
x_998 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_998, 0, x_996);
lean_ctor_set(x_998, 1, x_997);
return x_998;
}
}
}
else
{
uint8_t x_999; 
lean_dec(x_955);
lean_dec(x_949);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_999 = !lean_is_exclusive(x_980);
if (x_999 == 0)
{
return x_980;
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_1000 = lean_ctor_get(x_980, 0);
x_1001 = lean_ctor_get(x_980, 1);
lean_inc(x_1001);
lean_inc(x_1000);
lean_dec(x_980);
x_1002 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1002, 0, x_1000);
lean_ctor_set(x_1002, 1, x_1001);
return x_1002;
}
}
}
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_939);
x_1003 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_950);
x_1004 = lean_ctor_get(x_1003, 1);
lean_inc(x_1004);
lean_dec(x_1003);
x_1005 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_1005, 0, x_3);
lean_closure_set(x_1005, 1, x_4);
lean_closure_set(x_1005, 2, x_5);
lean_closure_set(x_1005, 3, x_27);
lean_closure_set(x_1005, 4, x_24);
lean_closure_set(x_1005, 5, x_26);
lean_closure_set(x_1005, 6, x_2);
lean_closure_set(x_1005, 7, x_23);
x_1006 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_949, x_1005, x_6, x_7, x_8, x_9, x_1004);
if (lean_obj_tag(x_1006) == 0)
{
uint8_t x_1007; 
x_1007 = !lean_is_exclusive(x_1006);
if (x_1007 == 0)
{
lean_object* x_1008; lean_object* x_1009; 
x_1008 = lean_ctor_get(x_1006, 0);
if (lean_is_scalar(x_22)) {
 x_1009 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1009 = x_22;
}
lean_ctor_set(x_1009, 0, x_1008);
lean_ctor_set(x_1006, 0, x_1009);
return x_1006;
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1010 = lean_ctor_get(x_1006, 0);
x_1011 = lean_ctor_get(x_1006, 1);
lean_inc(x_1011);
lean_inc(x_1010);
lean_dec(x_1006);
if (lean_is_scalar(x_22)) {
 x_1012 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1012 = x_22;
}
lean_ctor_set(x_1012, 0, x_1010);
x_1013 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1013, 0, x_1012);
lean_ctor_set(x_1013, 1, x_1011);
return x_1013;
}
}
else
{
uint8_t x_1014; 
lean_dec(x_22);
x_1014 = !lean_is_exclusive(x_1006);
if (x_1014 == 0)
{
return x_1006;
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1015 = lean_ctor_get(x_1006, 0);
x_1016 = lean_ctor_get(x_1006, 1);
lean_inc(x_1016);
lean_inc(x_1015);
lean_dec(x_1006);
x_1017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1017, 0, x_1015);
lean_ctor_set(x_1017, 1, x_1016);
return x_1017;
}
}
}
}
else
{
uint8_t x_1018; 
lean_dec(x_939);
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
x_1018 = !lean_is_exclusive(x_948);
if (x_1018 == 0)
{
return x_948;
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_948, 0);
x_1020 = lean_ctor_get(x_948, 1);
lean_inc(x_1020);
lean_inc(x_1019);
lean_dec(x_948);
x_1021 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1021, 0, x_1019);
lean_ctor_set(x_1021, 1, x_1020);
return x_1021;
}
}
}
}
else
{
uint8_t x_1041; 
lean_dec(x_939);
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
x_1041 = !lean_is_exclusive(x_944);
if (x_1041 == 0)
{
return x_944;
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1042 = lean_ctor_get(x_944, 0);
x_1043 = lean_ctor_get(x_944, 1);
lean_inc(x_1043);
lean_inc(x_1042);
lean_dec(x_944);
x_1044 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1044, 0, x_1042);
lean_ctor_set(x_1044, 1, x_1043);
return x_1044;
}
}
}
else
{
uint8_t x_1045; 
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
x_1045 = !lean_is_exclusive(x_938);
if (x_1045 == 0)
{
return x_938;
}
else
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
x_1046 = lean_ctor_get(x_938, 0);
x_1047 = lean_ctor_get(x_938, 1);
lean_inc(x_1047);
lean_inc(x_1046);
lean_dec(x_938);
x_1048 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1048, 0, x_1046);
lean_ctor_set(x_1048, 1, x_1047);
return x_1048;
}
}
}
case 9:
{
lean_object* x_1049; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1049 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1049) == 0)
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; uint8_t x_1054; lean_object* x_1055; 
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
lean_dec(x_1049);
x_1052 = lean_ctor_get(x_21, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_21, 1);
lean_inc(x_1053);
lean_dec(x_21);
x_1054 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1055 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1052, x_1053, x_32, x_1054, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1051);
lean_dec(x_1052);
if (lean_obj_tag(x_1055) == 0)
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; uint8_t x_1134; 
x_1056 = lean_ctor_get(x_1055, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1055, 1);
lean_inc(x_1057);
lean_dec(x_1055);
x_1134 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1134 == 0)
{
lean_object* x_1135; 
x_1135 = lean_box(0);
x_1058 = x_1135;
goto block_1133;
}
else
{
uint8_t x_1136; 
x_1136 = lean_nat_dec_eq(x_24, x_27);
if (x_1136 == 0)
{
lean_object* x_1137; 
x_1137 = lean_box(0);
x_1058 = x_1137;
goto block_1133;
}
else
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
lean_dec(x_1050);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_1138 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1057);
x_1139 = lean_ctor_get(x_1138, 1);
lean_inc(x_1139);
lean_dec(x_1138);
x_1140 = l_Lean_Compiler_LCNF_Simp_simp(x_1056, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1139);
if (lean_obj_tag(x_1140) == 0)
{
uint8_t x_1141; 
x_1141 = !lean_is_exclusive(x_1140);
if (x_1141 == 0)
{
lean_object* x_1142; lean_object* x_1143; 
x_1142 = lean_ctor_get(x_1140, 0);
x_1143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1143, 0, x_1142);
lean_ctor_set(x_1140, 0, x_1143);
return x_1140;
}
else
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1144 = lean_ctor_get(x_1140, 0);
x_1145 = lean_ctor_get(x_1140, 1);
lean_inc(x_1145);
lean_inc(x_1144);
lean_dec(x_1140);
x_1146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1146, 0, x_1144);
x_1147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1147, 0, x_1146);
lean_ctor_set(x_1147, 1, x_1145);
return x_1147;
}
}
else
{
uint8_t x_1148; 
x_1148 = !lean_is_exclusive(x_1140);
if (x_1148 == 0)
{
return x_1140;
}
else
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
x_1149 = lean_ctor_get(x_1140, 0);
x_1150 = lean_ctor_get(x_1140, 1);
lean_inc(x_1150);
lean_inc(x_1149);
lean_dec(x_1140);
x_1151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1151, 0, x_1149);
lean_ctor_set(x_1151, 1, x_1150);
return x_1151;
}
}
}
}
block_1133:
{
lean_object* x_1059; 
lean_dec(x_1058);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1059 = l_Lean_Compiler_LCNF_Simp_simp(x_1056, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1057);
if (lean_obj_tag(x_1059) == 0)
{
lean_object* x_1060; lean_object* x_1061; uint8_t x_1062; 
x_1060 = lean_ctor_get(x_1059, 0);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_1059, 1);
lean_inc(x_1061);
lean_dec(x_1059);
lean_inc(x_1060);
x_1062 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1060);
if (x_1062 == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; uint8_t x_1068; 
lean_dec(x_22);
x_1063 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1061);
x_1064 = lean_ctor_get(x_1063, 1);
lean_inc(x_1064);
lean_dec(x_1063);
x_1065 = l_Lean_Compiler_LCNF_mkAuxParam(x_1050, x_1054, x_6, x_7, x_8, x_9, x_1064);
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1065, 1);
lean_inc(x_1067);
lean_dec(x_1065);
x_1068 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1068 == 0)
{
lean_object* x_1069; lean_object* x_1070; 
lean_dec(x_27);
lean_dec(x_23);
x_1069 = lean_ctor_get(x_1066, 0);
lean_inc(x_1069);
x_1070 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1069, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1067);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; 
x_1071 = lean_ctor_get(x_1070, 1);
lean_inc(x_1071);
lean_dec(x_1070);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1072 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1071);
if (lean_obj_tag(x_1072) == 0)
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1072, 1);
lean_inc(x_1074);
lean_dec(x_1072);
x_1075 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1066, x_1060, x_1073, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1074);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1075;
}
else
{
uint8_t x_1076; 
lean_dec(x_1066);
lean_dec(x_1060);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1076 = !lean_is_exclusive(x_1072);
if (x_1076 == 0)
{
return x_1072;
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1077 = lean_ctor_get(x_1072, 0);
x_1078 = lean_ctor_get(x_1072, 1);
lean_inc(x_1078);
lean_inc(x_1077);
lean_dec(x_1072);
x_1079 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1079, 0, x_1077);
lean_ctor_set(x_1079, 1, x_1078);
return x_1079;
}
}
}
else
{
uint8_t x_1080; 
lean_dec(x_1066);
lean_dec(x_1060);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1080 = !lean_is_exclusive(x_1070);
if (x_1080 == 0)
{
return x_1070;
}
else
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1081 = lean_ctor_get(x_1070, 0);
x_1082 = lean_ctor_get(x_1070, 1);
lean_inc(x_1082);
lean_inc(x_1081);
lean_dec(x_1070);
x_1083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1083, 0, x_1081);
lean_ctor_set(x_1083, 1, x_1082);
return x_1083;
}
}
}
else
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
x_1084 = lean_ctor_get(x_1066, 0);
lean_inc(x_1084);
x_1085 = l_Lean_Expr_fvar___override(x_1084);
x_1086 = lean_array_get_size(x_23);
x_1087 = l_Array_toSubarray___rarg(x_23, x_27, x_1086);
x_1088 = l_Array_ofSubarray___rarg(x_1087);
x_1089 = l_Lean_mkAppN(x_1085, x_1088);
x_1090 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1091 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1089, x_1090, x_6, x_7, x_8, x_9, x_1067);
if (lean_obj_tag(x_1091) == 0)
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
x_1092 = lean_ctor_get(x_1091, 0);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_1091, 1);
lean_inc(x_1093);
lean_dec(x_1091);
x_1094 = lean_ctor_get(x_1092, 0);
lean_inc(x_1094);
x_1095 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1094, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1093);
if (lean_obj_tag(x_1095) == 0)
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1096 = lean_ctor_get(x_1095, 1);
lean_inc(x_1096);
lean_dec(x_1095);
x_1097 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1097, 0, x_1092);
lean_ctor_set(x_1097, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1098 = l_Lean_Compiler_LCNF_Simp_simp(x_1097, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1096);
if (lean_obj_tag(x_1098) == 0)
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
x_1099 = lean_ctor_get(x_1098, 0);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_1098, 1);
lean_inc(x_1100);
lean_dec(x_1098);
x_1101 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1066, x_1060, x_1099, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1100);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1101;
}
else
{
uint8_t x_1102; 
lean_dec(x_1066);
lean_dec(x_1060);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1102 = !lean_is_exclusive(x_1098);
if (x_1102 == 0)
{
return x_1098;
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
x_1103 = lean_ctor_get(x_1098, 0);
x_1104 = lean_ctor_get(x_1098, 1);
lean_inc(x_1104);
lean_inc(x_1103);
lean_dec(x_1098);
x_1105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1105, 0, x_1103);
lean_ctor_set(x_1105, 1, x_1104);
return x_1105;
}
}
}
else
{
uint8_t x_1106; 
lean_dec(x_1092);
lean_dec(x_1066);
lean_dec(x_1060);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1106 = !lean_is_exclusive(x_1095);
if (x_1106 == 0)
{
return x_1095;
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
x_1107 = lean_ctor_get(x_1095, 0);
x_1108 = lean_ctor_get(x_1095, 1);
lean_inc(x_1108);
lean_inc(x_1107);
lean_dec(x_1095);
x_1109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1109, 0, x_1107);
lean_ctor_set(x_1109, 1, x_1108);
return x_1109;
}
}
}
else
{
uint8_t x_1110; 
lean_dec(x_1066);
lean_dec(x_1060);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1110 = !lean_is_exclusive(x_1091);
if (x_1110 == 0)
{
return x_1091;
}
else
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; 
x_1111 = lean_ctor_get(x_1091, 0);
x_1112 = lean_ctor_get(x_1091, 1);
lean_inc(x_1112);
lean_inc(x_1111);
lean_dec(x_1091);
x_1113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1113, 0, x_1111);
lean_ctor_set(x_1113, 1, x_1112);
return x_1113;
}
}
}
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
lean_dec(x_1050);
x_1114 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1061);
x_1115 = lean_ctor_get(x_1114, 1);
lean_inc(x_1115);
lean_dec(x_1114);
x_1116 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_1116, 0, x_3);
lean_closure_set(x_1116, 1, x_4);
lean_closure_set(x_1116, 2, x_5);
lean_closure_set(x_1116, 3, x_27);
lean_closure_set(x_1116, 4, x_24);
lean_closure_set(x_1116, 5, x_26);
lean_closure_set(x_1116, 6, x_2);
lean_closure_set(x_1116, 7, x_23);
x_1117 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1060, x_1116, x_6, x_7, x_8, x_9, x_1115);
if (lean_obj_tag(x_1117) == 0)
{
uint8_t x_1118; 
x_1118 = !lean_is_exclusive(x_1117);
if (x_1118 == 0)
{
lean_object* x_1119; lean_object* x_1120; 
x_1119 = lean_ctor_get(x_1117, 0);
if (lean_is_scalar(x_22)) {
 x_1120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1120 = x_22;
}
lean_ctor_set(x_1120, 0, x_1119);
lean_ctor_set(x_1117, 0, x_1120);
return x_1117;
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
x_1121 = lean_ctor_get(x_1117, 0);
x_1122 = lean_ctor_get(x_1117, 1);
lean_inc(x_1122);
lean_inc(x_1121);
lean_dec(x_1117);
if (lean_is_scalar(x_22)) {
 x_1123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1123 = x_22;
}
lean_ctor_set(x_1123, 0, x_1121);
x_1124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1124, 0, x_1123);
lean_ctor_set(x_1124, 1, x_1122);
return x_1124;
}
}
else
{
uint8_t x_1125; 
lean_dec(x_22);
x_1125 = !lean_is_exclusive(x_1117);
if (x_1125 == 0)
{
return x_1117;
}
else
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1126 = lean_ctor_get(x_1117, 0);
x_1127 = lean_ctor_get(x_1117, 1);
lean_inc(x_1127);
lean_inc(x_1126);
lean_dec(x_1117);
x_1128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1128, 0, x_1126);
lean_ctor_set(x_1128, 1, x_1127);
return x_1128;
}
}
}
}
else
{
uint8_t x_1129; 
lean_dec(x_1050);
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
x_1129 = !lean_is_exclusive(x_1059);
if (x_1129 == 0)
{
return x_1059;
}
else
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1130 = lean_ctor_get(x_1059, 0);
x_1131 = lean_ctor_get(x_1059, 1);
lean_inc(x_1131);
lean_inc(x_1130);
lean_dec(x_1059);
x_1132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1132, 0, x_1130);
lean_ctor_set(x_1132, 1, x_1131);
return x_1132;
}
}
}
}
else
{
uint8_t x_1152; 
lean_dec(x_1050);
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
x_1152 = !lean_is_exclusive(x_1055);
if (x_1152 == 0)
{
return x_1055;
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1153 = lean_ctor_get(x_1055, 0);
x_1154 = lean_ctor_get(x_1055, 1);
lean_inc(x_1154);
lean_inc(x_1153);
lean_dec(x_1055);
x_1155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1155, 0, x_1153);
lean_ctor_set(x_1155, 1, x_1154);
return x_1155;
}
}
}
else
{
uint8_t x_1156; 
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
x_1156 = !lean_is_exclusive(x_1049);
if (x_1156 == 0)
{
return x_1049;
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
x_1157 = lean_ctor_get(x_1049, 0);
x_1158 = lean_ctor_get(x_1049, 1);
lean_inc(x_1158);
lean_inc(x_1157);
lean_dec(x_1049);
x_1159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1159, 0, x_1157);
lean_ctor_set(x_1159, 1, x_1158);
return x_1159;
}
}
}
case 10:
{
lean_object* x_1160; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1160 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1160) == 0)
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; uint8_t x_1165; lean_object* x_1166; 
x_1161 = lean_ctor_get(x_1160, 0);
lean_inc(x_1161);
x_1162 = lean_ctor_get(x_1160, 1);
lean_inc(x_1162);
lean_dec(x_1160);
x_1163 = lean_ctor_get(x_21, 0);
lean_inc(x_1163);
x_1164 = lean_ctor_get(x_21, 1);
lean_inc(x_1164);
lean_dec(x_21);
x_1165 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1166 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1163, x_1164, x_32, x_1165, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1162);
lean_dec(x_1163);
if (lean_obj_tag(x_1166) == 0)
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; uint8_t x_1245; 
x_1167 = lean_ctor_get(x_1166, 0);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_1166, 1);
lean_inc(x_1168);
lean_dec(x_1166);
x_1245 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1245 == 0)
{
lean_object* x_1246; 
x_1246 = lean_box(0);
x_1169 = x_1246;
goto block_1244;
}
else
{
uint8_t x_1247; 
x_1247 = lean_nat_dec_eq(x_24, x_27);
if (x_1247 == 0)
{
lean_object* x_1248; 
x_1248 = lean_box(0);
x_1169 = x_1248;
goto block_1244;
}
else
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
lean_dec(x_1161);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_1249 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1168);
x_1250 = lean_ctor_get(x_1249, 1);
lean_inc(x_1250);
lean_dec(x_1249);
x_1251 = l_Lean_Compiler_LCNF_Simp_simp(x_1167, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1250);
if (lean_obj_tag(x_1251) == 0)
{
uint8_t x_1252; 
x_1252 = !lean_is_exclusive(x_1251);
if (x_1252 == 0)
{
lean_object* x_1253; lean_object* x_1254; 
x_1253 = lean_ctor_get(x_1251, 0);
x_1254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1254, 0, x_1253);
lean_ctor_set(x_1251, 0, x_1254);
return x_1251;
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; 
x_1255 = lean_ctor_get(x_1251, 0);
x_1256 = lean_ctor_get(x_1251, 1);
lean_inc(x_1256);
lean_inc(x_1255);
lean_dec(x_1251);
x_1257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1257, 0, x_1255);
x_1258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1258, 0, x_1257);
lean_ctor_set(x_1258, 1, x_1256);
return x_1258;
}
}
else
{
uint8_t x_1259; 
x_1259 = !lean_is_exclusive(x_1251);
if (x_1259 == 0)
{
return x_1251;
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
x_1260 = lean_ctor_get(x_1251, 0);
x_1261 = lean_ctor_get(x_1251, 1);
lean_inc(x_1261);
lean_inc(x_1260);
lean_dec(x_1251);
x_1262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1262, 0, x_1260);
lean_ctor_set(x_1262, 1, x_1261);
return x_1262;
}
}
}
}
block_1244:
{
lean_object* x_1170; 
lean_dec(x_1169);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1170 = l_Lean_Compiler_LCNF_Simp_simp(x_1167, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1168);
if (lean_obj_tag(x_1170) == 0)
{
lean_object* x_1171; lean_object* x_1172; uint8_t x_1173; 
x_1171 = lean_ctor_get(x_1170, 0);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1170, 1);
lean_inc(x_1172);
lean_dec(x_1170);
lean_inc(x_1171);
x_1173 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1171);
if (x_1173 == 0)
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; uint8_t x_1179; 
lean_dec(x_22);
x_1174 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1172);
x_1175 = lean_ctor_get(x_1174, 1);
lean_inc(x_1175);
lean_dec(x_1174);
x_1176 = l_Lean_Compiler_LCNF_mkAuxParam(x_1161, x_1165, x_6, x_7, x_8, x_9, x_1175);
x_1177 = lean_ctor_get(x_1176, 0);
lean_inc(x_1177);
x_1178 = lean_ctor_get(x_1176, 1);
lean_inc(x_1178);
lean_dec(x_1176);
x_1179 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1179 == 0)
{
lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_27);
lean_dec(x_23);
x_1180 = lean_ctor_get(x_1177, 0);
lean_inc(x_1180);
x_1181 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1180, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1178);
if (lean_obj_tag(x_1181) == 0)
{
lean_object* x_1182; lean_object* x_1183; 
x_1182 = lean_ctor_get(x_1181, 1);
lean_inc(x_1182);
lean_dec(x_1181);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1183 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1182);
if (lean_obj_tag(x_1183) == 0)
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1183, 0);
lean_inc(x_1184);
x_1185 = lean_ctor_get(x_1183, 1);
lean_inc(x_1185);
lean_dec(x_1183);
x_1186 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1177, x_1171, x_1184, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1185);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1186;
}
else
{
uint8_t x_1187; 
lean_dec(x_1177);
lean_dec(x_1171);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1187 = !lean_is_exclusive(x_1183);
if (x_1187 == 0)
{
return x_1183;
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
x_1188 = lean_ctor_get(x_1183, 0);
x_1189 = lean_ctor_get(x_1183, 1);
lean_inc(x_1189);
lean_inc(x_1188);
lean_dec(x_1183);
x_1190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1190, 0, x_1188);
lean_ctor_set(x_1190, 1, x_1189);
return x_1190;
}
}
}
else
{
uint8_t x_1191; 
lean_dec(x_1177);
lean_dec(x_1171);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1191 = !lean_is_exclusive(x_1181);
if (x_1191 == 0)
{
return x_1181;
}
else
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
x_1192 = lean_ctor_get(x_1181, 0);
x_1193 = lean_ctor_get(x_1181, 1);
lean_inc(x_1193);
lean_inc(x_1192);
lean_dec(x_1181);
x_1194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1194, 0, x_1192);
lean_ctor_set(x_1194, 1, x_1193);
return x_1194;
}
}
}
else
{
lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1195 = lean_ctor_get(x_1177, 0);
lean_inc(x_1195);
x_1196 = l_Lean_Expr_fvar___override(x_1195);
x_1197 = lean_array_get_size(x_23);
x_1198 = l_Array_toSubarray___rarg(x_23, x_27, x_1197);
x_1199 = l_Array_ofSubarray___rarg(x_1198);
x_1200 = l_Lean_mkAppN(x_1196, x_1199);
x_1201 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1202 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1200, x_1201, x_6, x_7, x_8, x_9, x_1178);
if (lean_obj_tag(x_1202) == 0)
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; 
x_1203 = lean_ctor_get(x_1202, 0);
lean_inc(x_1203);
x_1204 = lean_ctor_get(x_1202, 1);
lean_inc(x_1204);
lean_dec(x_1202);
x_1205 = lean_ctor_get(x_1203, 0);
lean_inc(x_1205);
x_1206 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1205, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1204);
if (lean_obj_tag(x_1206) == 0)
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; 
x_1207 = lean_ctor_get(x_1206, 1);
lean_inc(x_1207);
lean_dec(x_1206);
x_1208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1208, 0, x_1203);
lean_ctor_set(x_1208, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1209 = l_Lean_Compiler_LCNF_Simp_simp(x_1208, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1207);
if (lean_obj_tag(x_1209) == 0)
{
lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
x_1210 = lean_ctor_get(x_1209, 0);
lean_inc(x_1210);
x_1211 = lean_ctor_get(x_1209, 1);
lean_inc(x_1211);
lean_dec(x_1209);
x_1212 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1177, x_1171, x_1210, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1211);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1212;
}
else
{
uint8_t x_1213; 
lean_dec(x_1177);
lean_dec(x_1171);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1213 = !lean_is_exclusive(x_1209);
if (x_1213 == 0)
{
return x_1209;
}
else
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
x_1214 = lean_ctor_get(x_1209, 0);
x_1215 = lean_ctor_get(x_1209, 1);
lean_inc(x_1215);
lean_inc(x_1214);
lean_dec(x_1209);
x_1216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1216, 0, x_1214);
lean_ctor_set(x_1216, 1, x_1215);
return x_1216;
}
}
}
else
{
uint8_t x_1217; 
lean_dec(x_1203);
lean_dec(x_1177);
lean_dec(x_1171);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1217 = !lean_is_exclusive(x_1206);
if (x_1217 == 0)
{
return x_1206;
}
else
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; 
x_1218 = lean_ctor_get(x_1206, 0);
x_1219 = lean_ctor_get(x_1206, 1);
lean_inc(x_1219);
lean_inc(x_1218);
lean_dec(x_1206);
x_1220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1220, 0, x_1218);
lean_ctor_set(x_1220, 1, x_1219);
return x_1220;
}
}
}
else
{
uint8_t x_1221; 
lean_dec(x_1177);
lean_dec(x_1171);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1221 = !lean_is_exclusive(x_1202);
if (x_1221 == 0)
{
return x_1202;
}
else
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
x_1222 = lean_ctor_get(x_1202, 0);
x_1223 = lean_ctor_get(x_1202, 1);
lean_inc(x_1223);
lean_inc(x_1222);
lean_dec(x_1202);
x_1224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1224, 0, x_1222);
lean_ctor_set(x_1224, 1, x_1223);
return x_1224;
}
}
}
}
else
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
lean_dec(x_1161);
x_1225 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1172);
x_1226 = lean_ctor_get(x_1225, 1);
lean_inc(x_1226);
lean_dec(x_1225);
x_1227 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_1227, 0, x_3);
lean_closure_set(x_1227, 1, x_4);
lean_closure_set(x_1227, 2, x_5);
lean_closure_set(x_1227, 3, x_27);
lean_closure_set(x_1227, 4, x_24);
lean_closure_set(x_1227, 5, x_26);
lean_closure_set(x_1227, 6, x_2);
lean_closure_set(x_1227, 7, x_23);
x_1228 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1171, x_1227, x_6, x_7, x_8, x_9, x_1226);
if (lean_obj_tag(x_1228) == 0)
{
uint8_t x_1229; 
x_1229 = !lean_is_exclusive(x_1228);
if (x_1229 == 0)
{
lean_object* x_1230; lean_object* x_1231; 
x_1230 = lean_ctor_get(x_1228, 0);
if (lean_is_scalar(x_22)) {
 x_1231 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1231 = x_22;
}
lean_ctor_set(x_1231, 0, x_1230);
lean_ctor_set(x_1228, 0, x_1231);
return x_1228;
}
else
{
lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
x_1232 = lean_ctor_get(x_1228, 0);
x_1233 = lean_ctor_get(x_1228, 1);
lean_inc(x_1233);
lean_inc(x_1232);
lean_dec(x_1228);
if (lean_is_scalar(x_22)) {
 x_1234 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1234 = x_22;
}
lean_ctor_set(x_1234, 0, x_1232);
x_1235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1235, 0, x_1234);
lean_ctor_set(x_1235, 1, x_1233);
return x_1235;
}
}
else
{
uint8_t x_1236; 
lean_dec(x_22);
x_1236 = !lean_is_exclusive(x_1228);
if (x_1236 == 0)
{
return x_1228;
}
else
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
x_1237 = lean_ctor_get(x_1228, 0);
x_1238 = lean_ctor_get(x_1228, 1);
lean_inc(x_1238);
lean_inc(x_1237);
lean_dec(x_1228);
x_1239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1239, 0, x_1237);
lean_ctor_set(x_1239, 1, x_1238);
return x_1239;
}
}
}
}
else
{
uint8_t x_1240; 
lean_dec(x_1161);
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
x_1240 = !lean_is_exclusive(x_1170);
if (x_1240 == 0)
{
return x_1170;
}
else
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; 
x_1241 = lean_ctor_get(x_1170, 0);
x_1242 = lean_ctor_get(x_1170, 1);
lean_inc(x_1242);
lean_inc(x_1241);
lean_dec(x_1170);
x_1243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1243, 0, x_1241);
lean_ctor_set(x_1243, 1, x_1242);
return x_1243;
}
}
}
}
else
{
uint8_t x_1263; 
lean_dec(x_1161);
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
x_1263 = !lean_is_exclusive(x_1166);
if (x_1263 == 0)
{
return x_1166;
}
else
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; 
x_1264 = lean_ctor_get(x_1166, 0);
x_1265 = lean_ctor_get(x_1166, 1);
lean_inc(x_1265);
lean_inc(x_1264);
lean_dec(x_1166);
x_1266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1266, 0, x_1264);
lean_ctor_set(x_1266, 1, x_1265);
return x_1266;
}
}
}
else
{
uint8_t x_1267; 
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
x_1267 = !lean_is_exclusive(x_1160);
if (x_1267 == 0)
{
return x_1160;
}
else
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; 
x_1268 = lean_ctor_get(x_1160, 0);
x_1269 = lean_ctor_get(x_1160, 1);
lean_inc(x_1269);
lean_inc(x_1268);
lean_dec(x_1160);
x_1270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1270, 0, x_1268);
lean_ctor_set(x_1270, 1, x_1269);
return x_1270;
}
}
}
default: 
{
lean_object* x_1271; 
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1271 = l_Lean_Compiler_LCNF_inferType(x_33, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1271) == 0)
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; uint8_t x_1276; lean_object* x_1277; 
x_1272 = lean_ctor_get(x_1271, 0);
lean_inc(x_1272);
x_1273 = lean_ctor_get(x_1271, 1);
lean_inc(x_1273);
lean_dec(x_1271);
x_1274 = lean_ctor_get(x_21, 0);
lean_inc(x_1274);
x_1275 = lean_ctor_get(x_21, 1);
lean_inc(x_1275);
lean_dec(x_21);
x_1276 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1277 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1274, x_1275, x_32, x_1276, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1273);
lean_dec(x_1274);
if (lean_obj_tag(x_1277) == 0)
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; uint8_t x_1356; 
x_1278 = lean_ctor_get(x_1277, 0);
lean_inc(x_1278);
x_1279 = lean_ctor_get(x_1277, 1);
lean_inc(x_1279);
lean_dec(x_1277);
x_1356 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1356 == 0)
{
lean_object* x_1357; 
x_1357 = lean_box(0);
x_1280 = x_1357;
goto block_1355;
}
else
{
uint8_t x_1358; 
x_1358 = lean_nat_dec_eq(x_24, x_27);
if (x_1358 == 0)
{
lean_object* x_1359; 
x_1359 = lean_box(0);
x_1280 = x_1359;
goto block_1355;
}
else
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; 
lean_dec(x_1272);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_1360 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1279);
x_1361 = lean_ctor_get(x_1360, 1);
lean_inc(x_1361);
lean_dec(x_1360);
x_1362 = l_Lean_Compiler_LCNF_Simp_simp(x_1278, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1361);
if (lean_obj_tag(x_1362) == 0)
{
uint8_t x_1363; 
x_1363 = !lean_is_exclusive(x_1362);
if (x_1363 == 0)
{
lean_object* x_1364; lean_object* x_1365; 
x_1364 = lean_ctor_get(x_1362, 0);
x_1365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1365, 0, x_1364);
lean_ctor_set(x_1362, 0, x_1365);
return x_1362;
}
else
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
x_1366 = lean_ctor_get(x_1362, 0);
x_1367 = lean_ctor_get(x_1362, 1);
lean_inc(x_1367);
lean_inc(x_1366);
lean_dec(x_1362);
x_1368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1368, 0, x_1366);
x_1369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1369, 0, x_1368);
lean_ctor_set(x_1369, 1, x_1367);
return x_1369;
}
}
else
{
uint8_t x_1370; 
x_1370 = !lean_is_exclusive(x_1362);
if (x_1370 == 0)
{
return x_1362;
}
else
{
lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; 
x_1371 = lean_ctor_get(x_1362, 0);
x_1372 = lean_ctor_get(x_1362, 1);
lean_inc(x_1372);
lean_inc(x_1371);
lean_dec(x_1362);
x_1373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1373, 0, x_1371);
lean_ctor_set(x_1373, 1, x_1372);
return x_1373;
}
}
}
}
block_1355:
{
lean_object* x_1281; 
lean_dec(x_1280);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1281 = l_Lean_Compiler_LCNF_Simp_simp(x_1278, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1279);
if (lean_obj_tag(x_1281) == 0)
{
lean_object* x_1282; lean_object* x_1283; uint8_t x_1284; 
x_1282 = lean_ctor_get(x_1281, 0);
lean_inc(x_1282);
x_1283 = lean_ctor_get(x_1281, 1);
lean_inc(x_1283);
lean_dec(x_1281);
lean_inc(x_1282);
x_1284 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1282);
if (x_1284 == 0)
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; uint8_t x_1290; 
lean_dec(x_22);
x_1285 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1283);
x_1286 = lean_ctor_get(x_1285, 1);
lean_inc(x_1286);
lean_dec(x_1285);
x_1287 = l_Lean_Compiler_LCNF_mkAuxParam(x_1272, x_1276, x_6, x_7, x_8, x_9, x_1286);
x_1288 = lean_ctor_get(x_1287, 0);
lean_inc(x_1288);
x_1289 = lean_ctor_get(x_1287, 1);
lean_inc(x_1289);
lean_dec(x_1287);
x_1290 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1290 == 0)
{
lean_object* x_1291; lean_object* x_1292; 
lean_dec(x_27);
lean_dec(x_23);
x_1291 = lean_ctor_get(x_1288, 0);
lean_inc(x_1291);
x_1292 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1291, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1289);
if (lean_obj_tag(x_1292) == 0)
{
lean_object* x_1293; lean_object* x_1294; 
x_1293 = lean_ctor_get(x_1292, 1);
lean_inc(x_1293);
lean_dec(x_1292);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1294 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1293);
if (lean_obj_tag(x_1294) == 0)
{
lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
x_1295 = lean_ctor_get(x_1294, 0);
lean_inc(x_1295);
x_1296 = lean_ctor_get(x_1294, 1);
lean_inc(x_1296);
lean_dec(x_1294);
x_1297 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1288, x_1282, x_1295, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1296);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1297;
}
else
{
uint8_t x_1298; 
lean_dec(x_1288);
lean_dec(x_1282);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1298 = !lean_is_exclusive(x_1294);
if (x_1298 == 0)
{
return x_1294;
}
else
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
x_1299 = lean_ctor_get(x_1294, 0);
x_1300 = lean_ctor_get(x_1294, 1);
lean_inc(x_1300);
lean_inc(x_1299);
lean_dec(x_1294);
x_1301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1301, 0, x_1299);
lean_ctor_set(x_1301, 1, x_1300);
return x_1301;
}
}
}
else
{
uint8_t x_1302; 
lean_dec(x_1288);
lean_dec(x_1282);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1302 = !lean_is_exclusive(x_1292);
if (x_1302 == 0)
{
return x_1292;
}
else
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; 
x_1303 = lean_ctor_get(x_1292, 0);
x_1304 = lean_ctor_get(x_1292, 1);
lean_inc(x_1304);
lean_inc(x_1303);
lean_dec(x_1292);
x_1305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1305, 0, x_1303);
lean_ctor_set(x_1305, 1, x_1304);
return x_1305;
}
}
}
else
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; 
x_1306 = lean_ctor_get(x_1288, 0);
lean_inc(x_1306);
x_1307 = l_Lean_Expr_fvar___override(x_1306);
x_1308 = lean_array_get_size(x_23);
x_1309 = l_Array_toSubarray___rarg(x_23, x_27, x_1308);
x_1310 = l_Array_ofSubarray___rarg(x_1309);
x_1311 = l_Lean_mkAppN(x_1307, x_1310);
x_1312 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1313 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1311, x_1312, x_6, x_7, x_8, x_9, x_1289);
if (lean_obj_tag(x_1313) == 0)
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; 
x_1314 = lean_ctor_get(x_1313, 0);
lean_inc(x_1314);
x_1315 = lean_ctor_get(x_1313, 1);
lean_inc(x_1315);
lean_dec(x_1313);
x_1316 = lean_ctor_get(x_1314, 0);
lean_inc(x_1316);
x_1317 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1316, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1315);
if (lean_obj_tag(x_1317) == 0)
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; 
x_1318 = lean_ctor_get(x_1317, 1);
lean_inc(x_1318);
lean_dec(x_1317);
x_1319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1319, 0, x_1314);
lean_ctor_set(x_1319, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1320 = l_Lean_Compiler_LCNF_Simp_simp(x_1319, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1318);
if (lean_obj_tag(x_1320) == 0)
{
lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; 
x_1321 = lean_ctor_get(x_1320, 0);
lean_inc(x_1321);
x_1322 = lean_ctor_get(x_1320, 1);
lean_inc(x_1322);
lean_dec(x_1320);
x_1323 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1288, x_1282, x_1321, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1322);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1323;
}
else
{
uint8_t x_1324; 
lean_dec(x_1288);
lean_dec(x_1282);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1324 = !lean_is_exclusive(x_1320);
if (x_1324 == 0)
{
return x_1320;
}
else
{
lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; 
x_1325 = lean_ctor_get(x_1320, 0);
x_1326 = lean_ctor_get(x_1320, 1);
lean_inc(x_1326);
lean_inc(x_1325);
lean_dec(x_1320);
x_1327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1327, 0, x_1325);
lean_ctor_set(x_1327, 1, x_1326);
return x_1327;
}
}
}
else
{
uint8_t x_1328; 
lean_dec(x_1314);
lean_dec(x_1288);
lean_dec(x_1282);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1328 = !lean_is_exclusive(x_1317);
if (x_1328 == 0)
{
return x_1317;
}
else
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; 
x_1329 = lean_ctor_get(x_1317, 0);
x_1330 = lean_ctor_get(x_1317, 1);
lean_inc(x_1330);
lean_inc(x_1329);
lean_dec(x_1317);
x_1331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1331, 0, x_1329);
lean_ctor_set(x_1331, 1, x_1330);
return x_1331;
}
}
}
else
{
uint8_t x_1332; 
lean_dec(x_1288);
lean_dec(x_1282);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1332 = !lean_is_exclusive(x_1313);
if (x_1332 == 0)
{
return x_1313;
}
else
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1333 = lean_ctor_get(x_1313, 0);
x_1334 = lean_ctor_get(x_1313, 1);
lean_inc(x_1334);
lean_inc(x_1333);
lean_dec(x_1313);
x_1335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1335, 0, x_1333);
lean_ctor_set(x_1335, 1, x_1334);
return x_1335;
}
}
}
}
else
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; 
lean_dec(x_1272);
x_1336 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1283);
x_1337 = lean_ctor_get(x_1336, 1);
lean_inc(x_1337);
lean_dec(x_1336);
x_1338 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 14, 8);
lean_closure_set(x_1338, 0, x_3);
lean_closure_set(x_1338, 1, x_4);
lean_closure_set(x_1338, 2, x_5);
lean_closure_set(x_1338, 3, x_27);
lean_closure_set(x_1338, 4, x_24);
lean_closure_set(x_1338, 5, x_26);
lean_closure_set(x_1338, 6, x_2);
lean_closure_set(x_1338, 7, x_23);
x_1339 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1282, x_1338, x_6, x_7, x_8, x_9, x_1337);
if (lean_obj_tag(x_1339) == 0)
{
uint8_t x_1340; 
x_1340 = !lean_is_exclusive(x_1339);
if (x_1340 == 0)
{
lean_object* x_1341; lean_object* x_1342; 
x_1341 = lean_ctor_get(x_1339, 0);
if (lean_is_scalar(x_22)) {
 x_1342 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1342 = x_22;
}
lean_ctor_set(x_1342, 0, x_1341);
lean_ctor_set(x_1339, 0, x_1342);
return x_1339;
}
else
{
lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; 
x_1343 = lean_ctor_get(x_1339, 0);
x_1344 = lean_ctor_get(x_1339, 1);
lean_inc(x_1344);
lean_inc(x_1343);
lean_dec(x_1339);
if (lean_is_scalar(x_22)) {
 x_1345 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1345 = x_22;
}
lean_ctor_set(x_1345, 0, x_1343);
x_1346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1346, 0, x_1345);
lean_ctor_set(x_1346, 1, x_1344);
return x_1346;
}
}
else
{
uint8_t x_1347; 
lean_dec(x_22);
x_1347 = !lean_is_exclusive(x_1339);
if (x_1347 == 0)
{
return x_1339;
}
else
{
lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1348 = lean_ctor_get(x_1339, 0);
x_1349 = lean_ctor_get(x_1339, 1);
lean_inc(x_1349);
lean_inc(x_1348);
lean_dec(x_1339);
x_1350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1350, 0, x_1348);
lean_ctor_set(x_1350, 1, x_1349);
return x_1350;
}
}
}
}
else
{
uint8_t x_1351; 
lean_dec(x_1272);
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
x_1351 = !lean_is_exclusive(x_1281);
if (x_1351 == 0)
{
return x_1281;
}
else
{
lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; 
x_1352 = lean_ctor_get(x_1281, 0);
x_1353 = lean_ctor_get(x_1281, 1);
lean_inc(x_1353);
lean_inc(x_1352);
lean_dec(x_1281);
x_1354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1354, 0, x_1352);
lean_ctor_set(x_1354, 1, x_1353);
return x_1354;
}
}
}
}
else
{
uint8_t x_1374; 
lean_dec(x_1272);
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
x_1374 = !lean_is_exclusive(x_1277);
if (x_1374 == 0)
{
return x_1277;
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1375 = lean_ctor_get(x_1277, 0);
x_1376 = lean_ctor_get(x_1277, 1);
lean_inc(x_1376);
lean_inc(x_1375);
lean_dec(x_1277);
x_1377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1377, 0, x_1375);
lean_ctor_set(x_1377, 1, x_1376);
return x_1377;
}
}
}
else
{
uint8_t x_1378; 
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
x_1378 = !lean_is_exclusive(x_1271);
if (x_1378 == 0)
{
return x_1271;
}
else
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
x_1379 = lean_ctor_get(x_1271, 0);
x_1380 = lean_ctor_get(x_1271, 1);
lean_inc(x_1380);
lean_inc(x_1379);
lean_dec(x_1271);
x_1381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1381, 0, x_1379);
lean_ctor_set(x_1381, 1, x_1380);
return x_1381;
}
}
}
}
}
else
{
lean_object* x_1382; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
x_1382 = l_Lean_Expr_getAppFn(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_1382) == 4)
{
lean_object* x_1383; lean_object* x_1384; 
x_1383 = lean_ctor_get(x_1382, 0);
lean_inc(x_1383);
lean_dec(x_1382);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1383);
x_1384 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_1383, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1384) == 0)
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; 
x_1385 = lean_ctor_get(x_1384, 0);
lean_inc(x_1385);
x_1386 = lean_ctor_get(x_1384, 1);
lean_inc(x_1386);
lean_dec(x_1384);
x_1387 = lean_ctor_get(x_3, 0);
lean_inc(x_1387);
x_1388 = lean_ctor_get(x_3, 1);
lean_inc(x_1388);
x_1389 = lean_ctor_get(x_3, 2);
lean_inc(x_1389);
lean_inc(x_1383);
x_1390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1390, 0, x_1383);
lean_ctor_set(x_1390, 1, x_1389);
x_1391 = lean_ctor_get(x_3, 3);
lean_inc(x_1391);
lean_dec(x_3);
x_1392 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_1391, x_1383, x_1385);
x_1393 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1393, 0, x_1387);
lean_ctor_set(x_1393, 1, x_1388);
lean_ctor_set(x_1393, 2, x_1390);
lean_ctor_set(x_1393, 3, x_1392);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1394 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_1393, x_4, x_5, x_6, x_7, x_8, x_9, x_1386);
if (lean_obj_tag(x_1394) == 0)
{
lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
x_1395 = lean_ctor_get(x_1394, 0);
lean_inc(x_1395);
x_1396 = lean_ctor_get(x_1394, 1);
lean_inc(x_1396);
lean_dec(x_1394);
x_1397 = lean_ctor_get(x_1395, 0);
lean_inc(x_1397);
x_1398 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1397, x_1393, x_4, x_5, x_6, x_7, x_8, x_9, x_1396);
if (lean_obj_tag(x_1398) == 0)
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1399 = lean_ctor_get(x_1398, 1);
lean_inc(x_1399);
lean_dec(x_1398);
x_1400 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1399);
x_1401 = lean_ctor_get(x_1400, 1);
lean_inc(x_1401);
lean_dec(x_1400);
x_1402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1402, 0, x_1395);
lean_ctor_set(x_1402, 1, x_2);
x_1403 = l_Lean_Compiler_LCNF_Simp_simp(x_1402, x_1393, x_4, x_5, x_6, x_7, x_8, x_9, x_1401);
if (lean_obj_tag(x_1403) == 0)
{
uint8_t x_1404; 
x_1404 = !lean_is_exclusive(x_1403);
if (x_1404 == 0)
{
lean_object* x_1405; lean_object* x_1406; 
x_1405 = lean_ctor_get(x_1403, 0);
if (lean_is_scalar(x_22)) {
 x_1406 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1406 = x_22;
}
lean_ctor_set(x_1406, 0, x_1405);
lean_ctor_set(x_1403, 0, x_1406);
return x_1403;
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; 
x_1407 = lean_ctor_get(x_1403, 0);
x_1408 = lean_ctor_get(x_1403, 1);
lean_inc(x_1408);
lean_inc(x_1407);
lean_dec(x_1403);
if (lean_is_scalar(x_22)) {
 x_1409 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1409 = x_22;
}
lean_ctor_set(x_1409, 0, x_1407);
x_1410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1410, 0, x_1409);
lean_ctor_set(x_1410, 1, x_1408);
return x_1410;
}
}
else
{
uint8_t x_1411; 
lean_dec(x_22);
x_1411 = !lean_is_exclusive(x_1403);
if (x_1411 == 0)
{
return x_1403;
}
else
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; 
x_1412 = lean_ctor_get(x_1403, 0);
x_1413 = lean_ctor_get(x_1403, 1);
lean_inc(x_1413);
lean_inc(x_1412);
lean_dec(x_1403);
x_1414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1414, 0, x_1412);
lean_ctor_set(x_1414, 1, x_1413);
return x_1414;
}
}
}
else
{
uint8_t x_1415; 
lean_dec(x_1395);
lean_dec(x_1393);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1415 = !lean_is_exclusive(x_1398);
if (x_1415 == 0)
{
return x_1398;
}
else
{
lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; 
x_1416 = lean_ctor_get(x_1398, 0);
x_1417 = lean_ctor_get(x_1398, 1);
lean_inc(x_1417);
lean_inc(x_1416);
lean_dec(x_1398);
x_1418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1418, 0, x_1416);
lean_ctor_set(x_1418, 1, x_1417);
return x_1418;
}
}
}
else
{
uint8_t x_1419; 
lean_dec(x_1393);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1419 = !lean_is_exclusive(x_1394);
if (x_1419 == 0)
{
return x_1394;
}
else
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; 
x_1420 = lean_ctor_get(x_1394, 0);
x_1421 = lean_ctor_get(x_1394, 1);
lean_inc(x_1421);
lean_inc(x_1420);
lean_dec(x_1394);
x_1422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1422, 0, x_1420);
lean_ctor_set(x_1422, 1, x_1421);
return x_1422;
}
}
}
else
{
uint8_t x_1423; 
lean_dec(x_1383);
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
x_1423 = !lean_is_exclusive(x_1384);
if (x_1423 == 0)
{
return x_1384;
}
else
{
lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; 
x_1424 = lean_ctor_get(x_1384, 0);
x_1425 = lean_ctor_get(x_1384, 1);
lean_inc(x_1425);
lean_inc(x_1424);
lean_dec(x_1384);
x_1426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1426, 0, x_1424);
lean_ctor_set(x_1426, 1, x_1425);
return x_1426;
}
}
}
else
{
lean_object* x_1427; 
lean_dec(x_1382);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1427 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1427) == 0)
{
lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; 
x_1428 = lean_ctor_get(x_1427, 0);
lean_inc(x_1428);
x_1429 = lean_ctor_get(x_1427, 1);
lean_inc(x_1429);
lean_dec(x_1427);
x_1430 = lean_ctor_get(x_1428, 0);
lean_inc(x_1430);
x_1431 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1430, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1429);
if (lean_obj_tag(x_1431) == 0)
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; 
x_1432 = lean_ctor_get(x_1431, 1);
lean_inc(x_1432);
lean_dec(x_1431);
x_1433 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1432);
x_1434 = lean_ctor_get(x_1433, 1);
lean_inc(x_1434);
lean_dec(x_1433);
x_1435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1435, 0, x_1428);
lean_ctor_set(x_1435, 1, x_2);
x_1436 = l_Lean_Compiler_LCNF_Simp_simp(x_1435, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1434);
if (lean_obj_tag(x_1436) == 0)
{
uint8_t x_1437; 
x_1437 = !lean_is_exclusive(x_1436);
if (x_1437 == 0)
{
lean_object* x_1438; lean_object* x_1439; 
x_1438 = lean_ctor_get(x_1436, 0);
if (lean_is_scalar(x_22)) {
 x_1439 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1439 = x_22;
}
lean_ctor_set(x_1439, 0, x_1438);
lean_ctor_set(x_1436, 0, x_1439);
return x_1436;
}
else
{
lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; 
x_1440 = lean_ctor_get(x_1436, 0);
x_1441 = lean_ctor_get(x_1436, 1);
lean_inc(x_1441);
lean_inc(x_1440);
lean_dec(x_1436);
if (lean_is_scalar(x_22)) {
 x_1442 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1442 = x_22;
}
lean_ctor_set(x_1442, 0, x_1440);
x_1443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1443, 0, x_1442);
lean_ctor_set(x_1443, 1, x_1441);
return x_1443;
}
}
else
{
uint8_t x_1444; 
lean_dec(x_22);
x_1444 = !lean_is_exclusive(x_1436);
if (x_1444 == 0)
{
return x_1436;
}
else
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; 
x_1445 = lean_ctor_get(x_1436, 0);
x_1446 = lean_ctor_get(x_1436, 1);
lean_inc(x_1446);
lean_inc(x_1445);
lean_dec(x_1436);
x_1447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1447, 0, x_1445);
lean_ctor_set(x_1447, 1, x_1446);
return x_1447;
}
}
}
else
{
uint8_t x_1448; 
lean_dec(x_1428);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1448 = !lean_is_exclusive(x_1431);
if (x_1448 == 0)
{
return x_1431;
}
else
{
lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
x_1449 = lean_ctor_get(x_1431, 0);
x_1450 = lean_ctor_get(x_1431, 1);
lean_inc(x_1450);
lean_inc(x_1449);
lean_dec(x_1431);
x_1451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1451, 0, x_1449);
lean_ctor_set(x_1451, 1, x_1450);
return x_1451;
}
}
}
else
{
uint8_t x_1452; 
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
x_1452 = !lean_is_exclusive(x_1427);
if (x_1452 == 0)
{
return x_1427;
}
else
{
lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; 
x_1453 = lean_ctor_get(x_1427, 0);
x_1454 = lean_ctor_get(x_1427, 1);
lean_inc(x_1454);
lean_inc(x_1453);
lean_dec(x_1427);
x_1455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1455, 0, x_1453);
lean_ctor_set(x_1455, 1, x_1454);
return x_1455;
}
}
}
}
}
}
else
{
uint8_t x_1456; 
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
x_1456 = !lean_is_exclusive(x_12);
if (x_1456 == 0)
{
return x_12;
}
else
{
lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; 
x_1457 = lean_ctor_get(x_12, 0);
x_1458 = lean_ctor_get(x_12, 1);
lean_inc(x_1458);
lean_inc(x_1457);
lean_dec(x_12);
x_1459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1459, 0, x_1457);
lean_ctor_set(x_1459, 1, x_1458);
return x_1459;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
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
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
