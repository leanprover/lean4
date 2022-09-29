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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2;
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_hasLocalInst(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4;
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3;
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_panic___at_Lean_Compiler_LCNF_CasesCore_extractAlt_x21___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2;
x_3 = lean_unsigned_to_nat(77u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
x_14 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4;
x_15 = l_panic___at_Lean_Compiler_LCNF_CasesCore_extractAlt_x21___spec__2(x_14);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_1, x_3);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_24 = lean_ctor_get(x_16, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_array_fget(x_18, x_19);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_19, x_28);
lean_dec(x_19);
lean_ctor_set(x_16, 1, x_29);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_17, x_30, x_27);
lean_ctor_set(x_4, 1, x_31);
x_32 = 1;
x_33 = lean_usize_add(x_3, x_32);
x_3 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
lean_dec(x_16);
x_35 = lean_array_fget(x_18, x_19);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_19, x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_20);
x_39 = lean_ctor_get(x_14, 0);
lean_inc(x_39);
lean_dec(x_14);
x_40 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_17, x_39, x_35);
lean_ctor_set(x_4, 1, x_40);
lean_ctor_set(x_4, 0, x_38);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_3 = x_42;
goto _start;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_4, 0);
x_45 = lean_ctor_get(x_4, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_4);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 2);
lean_inc(x_48);
x_49 = lean_nat_dec_lt(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_14);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_11);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; 
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
 x_52 = lean_box(0);
}
x_53 = lean_array_fget(x_46, x_47);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_47, x_54);
lean_dec(x_47);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(0, 3, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_48);
x_57 = lean_ctor_get(x_14, 0);
lean_inc(x_57);
lean_dec(x_14);
x_58 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_45, x_57, x_53);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = 1;
x_61 = lean_usize_add(x_3, x_60);
x_3 = x_61;
x_4 = x_59;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_array_uget(x_14, x_3);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = 1;
lean_inc(x_17);
x_20 = l_Lean_Compiler_LCNF_replaceExprFVars(x_18, x_17, x_19, x_7, x_8, x_9, x_10, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 0;
x_24 = l_Lean_Compiler_LCNF_mkAuxParam(x_21, x_23, x_7, x_8, x_9, x_10, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = lean_array_push(x_16, x_25);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Expr_fvar___override(x_29);
x_31 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_17, x_28, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
x_4 = x_32;
x_11 = x_26;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_12 = l_Array_toSubarray___rarg(x_9, x_11, x_10);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_get_size(x_13);
x_17 = lean_usize_of_nat(x_16);
x_18 = 0;
x_19 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_13, x_17, x_18, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_toSubarray___rarg(x_13, x_10, x_16);
x_25 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
lean_ctor_set(x_20, 0, x_25);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2(x_24, x_27, x_29, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_Compiler_LCNF_Code_internalize(x_35, x_34, x_4, x_5, x_6, x_7, x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_37);
x_40 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_37, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_43 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_33, x_37, x_42, x_4, x_5, x_6, x_7, x_41);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_dec(x_20);
x_49 = l_Array_toSubarray___rarg(x_13, x_10, x_16);
x_50 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
x_52 = lean_ctor_get(x_49, 2);
lean_inc(x_52);
x_53 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
x_55 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_56 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2(x_49, x_53, x_55, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_49);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_61);
lean_dec(x_1);
x_62 = l_Lean_Compiler_LCNF_Code_internalize(x_61, x_60, x_4, x_5, x_6, x_7, x_58);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_63);
x_66 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_63, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_69 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_59, x_63, x_68, x_4, x_5, x_6, x_7, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_72 = x_66;
} else {
 lean_dec_ref(x_66);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
lean_dec(x_1);
x_15 = 0;
x_16 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_13, x_14, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
lean_inc(x_19);
x_20 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_box(0);
x_31 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(x_19, x_2, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_4);
lean_dec(x_3);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_9, 0);
if (x_10 == 0)
{
lean_object* x_274; 
x_274 = lean_box(0);
x_11 = x_274;
x_12 = x_8;
goto block_273;
}
else
{
lean_object* x_275; 
x_275 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_11 = x_275;
x_12 = x_8;
goto block_273;
}
block_273:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = l_Lean_Expr_getAppFn(x_15);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_7, x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_17);
x_23 = lean_environment_find(x_22, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_box(0);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ConstantInfo_type(x_25);
lean_dec(x_25);
x_27 = l_Lean_Compiler_LCNF_hasLocalInst(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = lean_box(0);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_18);
lean_inc(x_17);
x_29 = l_Lean_Meta_isInstance(x_17, x_6, x_7, x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Lean_Compiler_LCNF_getDecl_x3f(x_17, x_4, x_5, x_6, x_7, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_33, 1);
x_43 = lean_ctor_get(x_33, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_34);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_34, 0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_15, x_46);
x_48 = l_Lean_Compiler_LCNF_Decl_getArity(x_45);
lean_dec(x_45);
x_49 = lean_nat_dec_lt(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
lean_free_object(x_34);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_50 = lean_box(0);
lean_ctor_set(x_33, 0, x_50);
return x_33;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_33);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
x_52 = l_Lean_Compiler_LCNF_mkNewParams(x_51, x_4, x_5, x_6, x_7, x_42);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_array_get_size(x_53);
x_56 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_57 = 0;
lean_inc(x_53);
x_58 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_56, x_57, x_53);
x_59 = l_Lean_mkAppN(x_15, x_58);
x_60 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_61 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_59, x_60, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_68 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_53, x_66, x_67, x_4, x_5, x_6, x_7, x_63);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_71, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set(x_34, 0, x_69);
lean_ctor_set(x_75, 0, x_34);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
lean_ctor_set(x_34, 0, x_69);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_34);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_69);
lean_free_object(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_73);
if (x_80 == 0)
{
return x_73;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_73, 0);
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_73);
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
lean_free_object(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_53);
lean_free_object(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_34, 0);
lean_inc(x_92);
lean_dec(x_34);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_15, x_93);
x_95 = l_Lean_Compiler_LCNF_Decl_getArity(x_92);
lean_dec(x_92);
x_96 = lean_nat_dec_lt(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_97 = lean_box(0);
lean_ctor_set(x_33, 0, x_97);
return x_33;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; size_t x_103; size_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_free_object(x_33);
x_98 = lean_ctor_get(x_1, 2);
lean_inc(x_98);
x_99 = l_Lean_Compiler_LCNF_mkNewParams(x_98, x_4, x_5, x_6, x_7, x_42);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_array_get_size(x_100);
x_103 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_104 = 0;
lean_inc(x_100);
x_105 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_103, x_104, x_100);
x_106 = l_Lean_mkAppN(x_15, x_105);
x_107 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_108 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_106, x_107, x_4, x_5, x_6, x_7, x_101);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_115 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_100, x_113, x_114, x_4, x_5, x_6, x_7, x_110);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_1, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
x_120 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_118, x_119, x_2, x_3, x_4, x_5, x_6, x_7, x_117);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_121);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_116);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_116);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_127 = lean_ctor_get(x_120, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_120, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_129 = x_120;
} else {
 lean_dec_ref(x_120);
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
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_131 = lean_ctor_get(x_115, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_115, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_133 = x_115;
} else {
 lean_dec_ref(x_115);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_100);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_135 = lean_ctor_get(x_108, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_108, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_137 = x_108;
} else {
 lean_dec_ref(x_108);
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
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_139 = lean_ctor_get(x_33, 1);
lean_inc(x_139);
lean_dec(x_33);
x_140 = lean_ctor_get(x_34, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_141 = x_34;
} else {
 lean_dec_ref(x_34);
 x_141 = lean_box(0);
}
x_142 = lean_unsigned_to_nat(0u);
x_143 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_15, x_142);
x_144 = l_Lean_Compiler_LCNF_Decl_getArity(x_140);
lean_dec(x_140);
x_145 = lean_nat_dec_lt(x_143, x_144);
lean_dec(x_144);
lean_dec(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_141);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_139);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; size_t x_153; size_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_148 = lean_ctor_get(x_1, 2);
lean_inc(x_148);
x_149 = l_Lean_Compiler_LCNF_mkNewParams(x_148, x_4, x_5, x_6, x_7, x_139);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_array_get_size(x_150);
x_153 = lean_usize_of_nat(x_152);
lean_dec(x_152);
x_154 = 0;
lean_inc(x_150);
x_155 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_153, x_154, x_150);
x_156 = l_Lean_mkAppN(x_15, x_155);
x_157 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_158 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_156, x_157, x_4, x_5, x_6, x_7, x_151);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_165 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_150, x_163, x_164, x_4, x_5, x_6, x_7, x_160);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_1, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
x_170 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_168, x_169, x_2, x_3, x_4, x_5, x_6, x_7, x_167);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_171);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_175 = lean_alloc_ctor(1, 1, 0);
} else {
 x_175 = x_141;
}
lean_ctor_set(x_175, 0, x_166);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_174;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_166);
lean_dec(x_141);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_177 = lean_ctor_get(x_170, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_170, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_179 = x_170;
} else {
 lean_dec_ref(x_170);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_141);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_181 = lean_ctor_get(x_165, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_165, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_183 = x_165;
} else {
 lean_dec_ref(x_165);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_150);
lean_dec(x_141);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_185 = lean_ctor_get(x_158, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_158, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_187 = x_158;
} else {
 lean_dec_ref(x_158);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_29);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_29, 0);
lean_dec(x_190);
x_191 = lean_box(0);
lean_ctor_set(x_29, 0, x_191);
return x_29;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_29, 1);
lean_inc(x_192);
lean_dec(x_29);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_ctor_get(x_18, 0);
x_196 = lean_ctor_get(x_18, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_18);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
lean_dec(x_195);
lean_inc(x_17);
x_198 = lean_environment_find(x_197, x_17);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_196);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_201 = lean_ctor_get(x_198, 0);
lean_inc(x_201);
lean_dec(x_198);
x_202 = l_Lean_ConstantInfo_type(x_201);
lean_dec(x_201);
x_203 = l_Lean_Compiler_LCNF_hasLocalInst(x_202);
lean_dec(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_204 = lean_box(0);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_196);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_inc(x_17);
x_206 = l_Lean_Meta_isInstance(x_17, x_6, x_7, x_196);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_unbox(x_207);
lean_dec(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
x_210 = l_Lean_Compiler_LCNF_getDecl_x3f(x_17, x_4, x_5, x_6, x_7, x_209);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
x_214 = lean_box(0);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_216 = lean_ctor_get(x_210, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_217 = x_210;
} else {
 lean_dec_ref(x_210);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_211, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_219 = x_211;
} else {
 lean_dec_ref(x_211);
 x_219 = lean_box(0);
}
x_220 = lean_unsigned_to_nat(0u);
x_221 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_15, x_220);
x_222 = l_Lean_Compiler_LCNF_Decl_getArity(x_218);
lean_dec(x_218);
x_223 = lean_nat_dec_lt(x_221, x_222);
lean_dec(x_222);
lean_dec(x_221);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_219);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_224 = lean_box(0);
if (lean_is_scalar(x_217)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_217;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_216);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; size_t x_231; size_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_217);
x_226 = lean_ctor_get(x_1, 2);
lean_inc(x_226);
x_227 = l_Lean_Compiler_LCNF_mkNewParams(x_226, x_4, x_5, x_6, x_7, x_216);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_array_get_size(x_228);
x_231 = lean_usize_of_nat(x_230);
lean_dec(x_230);
x_232 = 0;
lean_inc(x_228);
x_233 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_231, x_232, x_228);
x_234 = l_Lean_mkAppN(x_15, x_233);
x_235 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_236 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_234, x_235, x_4, x_5, x_6, x_7, x_229);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
x_240 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_237);
lean_ctor_set(x_241, 1, x_240);
x_242 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_243 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_228, x_241, x_242, x_4, x_5, x_6, x_7, x_238);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_ctor_get(x_1, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_244, 0);
lean_inc(x_247);
x_248 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_246, x_247, x_2, x_3, x_4, x_5, x_6, x_7, x_245);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_250 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_249);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_253 = lean_alloc_ctor(1, 1, 0);
} else {
 x_253 = x_219;
}
lean_ctor_set(x_253, 0, x_244);
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
lean_dec(x_244);
lean_dec(x_219);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_255 = lean_ctor_get(x_248, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_248, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_257 = x_248;
} else {
 lean_dec_ref(x_248);
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
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_219);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_259 = lean_ctor_get(x_243, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_243, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_261 = x_243;
} else {
 lean_dec_ref(x_243);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_228);
lean_dec(x_219);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_263 = lean_ctor_get(x_236, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_236, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_265 = x_236;
} else {
 lean_dec_ref(x_236);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_267 = lean_ctor_get(x_206, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_268 = x_206;
} else {
 lean_dec_ref(x_206);
 x_268 = lean_box(0);
}
x_269 = lean_box(0);
if (lean_is_scalar(x_268)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_268;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_267);
return x_270;
}
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_271 = lean_box(0);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_12);
return x_272;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 0;
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_16, x_10, x_17);
x_19 = lean_name_eq(x_18, x_2);
lean_dec(x_18);
x_20 = lean_box(x_19);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
x_25 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_23, x_10, x_24);
x_26 = lean_name_eq(x_25, x_2);
lean_dec(x_25);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_isReturnOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1;
x_12 = lean_array_push(x_11, x_1);
x_13 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_12, x_3, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_11);
x_18 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_2, x_17, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_8);
x_14 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_8, x_1, x_2, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_3);
x_17 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_5, x_8, x_1, x_2, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Compiler_LCNF_Simp_simp(x_6, x_1, x_2, x_9, x_10, x_11, x_12, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = l_Lean_Expr_fvar___override(x_8);
x_25 = lean_array_get_size(x_7);
x_26 = l_Array_toSubarray___rarg(x_7, x_3, x_25);
x_27 = l_Array_ofSubarray___rarg(x_26);
x_28 = l_Lean_mkAppN(x_24, x_27);
x_29 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_30 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_28, x_29, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_5, x_33, x_1, x_2, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_6);
x_37 = l_Lean_Compiler_LCNF_Simp_simp(x_36, x_1, x_2, x_9, x_10, x_11, x_12, x_35);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_102; 
x_102 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_6, x_5);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_box(0);
x_16 = x_103;
goto block_101;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_eq(x_4, x_3);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_box(0);
x_16 = x_105;
goto block_101;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = l_Lean_Compiler_LCNF_Simp_simp(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_107);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_108, 0, x_111);
return x_108;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_108, 0);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_108);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_108);
if (x_116 == 0)
{
return x_108;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_108, 0);
x_118 = lean_ctor_get(x_108, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_108);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
block_101:
{
lean_object* x_17; 
lean_dec(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Compiler_LCNF_Simp_simp(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_18);
x_20 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_10, x_11, x_12, x_13, x_14, x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_mkAppN(x_23, x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_25 = l_Lean_Compiler_LCNF_inferType(x_24, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 0;
x_29 = l_Lean_Compiler_LCNF_mkAuxParam(x_26, x_28, x_11, x_12, x_13, x_14, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_3);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_5, x_33, x_9, x_10, x_11, x_12, x_13, x_14, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_36 = l_Lean_Compiler_LCNF_Simp_simp(x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_30, x_18, x_37, x_9, x_10, x_11, x_12, x_13, x_14, x_38);
lean_dec(x_10);
lean_dec(x_9);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_34);
if (x_44 == 0)
{
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_34, 0);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_34);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_30, 0);
lean_inc(x_48);
x_49 = l_Lean_Expr_fvar___override(x_48);
x_50 = lean_array_get_size(x_7);
x_51 = l_Array_toSubarray___rarg(x_7, x_3, x_50);
x_52 = l_Array_ofSubarray___rarg(x_51);
x_53 = l_Lean_mkAppN(x_49, x_52);
x_54 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_55 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_53, x_54, x_11, x_12, x_13, x_14, x_31);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_5, x_58, x_9, x_10, x_11, x_12, x_13, x_14, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_62 = l_Lean_Compiler_LCNF_Simp_simp(x_61, x_9, x_10, x_11, x_12, x_13, x_14, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_30, x_18, x_63, x_9, x_10, x_11, x_12, x_13, x_14, x_64);
lean_dec(x_10);
lean_dec(x_9);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 0);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_62);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_56);
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
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
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
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
}
else
{
uint8_t x_78; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_25);
if (x_78 == 0)
{
return x_25;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_25, 0);
x_80 = lean_ctor_get(x_25, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_25);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_82 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_10, x_11, x_12, x_13, x_14, x_19);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3), 13, 7);
lean_closure_set(x_84, 0, x_9);
lean_closure_set(x_84, 1, x_10);
lean_closure_set(x_84, 2, x_3);
lean_closure_set(x_84, 3, x_4);
lean_closure_set(x_84, 4, x_5);
lean_closure_set(x_84, 5, x_6);
lean_closure_set(x_84, 6, x_7);
x_85 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_18, x_84, x_11, x_12, x_13, x_14, x_83);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_85, 0);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_85);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_85);
if (x_93 == 0)
{
return x_85;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_85, 0);
x_95 = lean_ctor_get(x_85, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_85);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_17);
if (x_97 == 0)
{
return x_17;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_17, 0);
x_99 = lean_ctor_get(x_17, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_17);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_5, x_6, x_7, x_8, x_9, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_2);
x_17 = l_Lean_Compiler_LCNF_Simp_simp(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
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
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
x_11 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
x_23 = lean_ctor_get_uint8(x_20, sizeof(void*)*4 + 2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_20);
x_26 = lean_nat_dec_lt(x_22, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
x_29 = lean_unsigned_to_nat(0u);
lean_inc(x_25);
lean_inc(x_21);
x_30 = l_Array_toSubarray___rarg(x_21, x_29, x_25);
x_31 = l_Array_ofSubarray___rarg(x_30);
x_32 = 0;
x_33 = lean_box(x_32);
lean_inc(x_31);
x_34 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_betaReduce___boxed), 11, 4);
lean_closure_set(x_34, 0, x_27);
lean_closure_set(x_34, 1, x_28);
lean_closure_set(x_34, 2, x_31);
lean_closure_set(x_34, 3, x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4), 15, 7);
lean_closure_set(x_35, 0, x_20);
lean_closure_set(x_35, 1, x_31);
lean_closure_set(x_35, 2, x_25);
lean_closure_set(x_35, 3, x_22);
lean_closure_set(x_35, 4, x_24);
lean_closure_set(x_35, 5, x_2);
lean_closure_set(x_35, 6, x_21);
x_36 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___spec__1___rarg), 9, 2);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_35);
x_37 = l_Lean_Compiler_LCNF_Simp_withInlining___rarg(x_10, x_23, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
x_38 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed), 8, 1);
lean_closure_set(x_38, 0, x_20);
x_39 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5), 10, 2);
lean_closure_set(x_39, 0, x_24);
lean_closure_set(x_39, 1, x_2);
x_40 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___spec__1___rarg), 9, 2);
lean_closure_set(x_40, 0, x_38);
lean_closure_set(x_40, 1, x_39);
x_41 = l_Lean_Compiler_LCNF_Simp_withInlining___rarg(x_10, x_23, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
return x_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_16, x_1, x_10);
x_18 = lean_ctor_get(x_2, 3);
lean_inc(x_18);
x_19 = lean_st_ref_get(x_8, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_4, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_24, x_1, x_18);
x_26 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(x_2, x_17, x_25, x_5, x_6, x_7, x_8, x_23);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_4, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_15, x_1, x_2);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_19, x_1, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_15 = lean_apply_8(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ptr_addr(x_14);
lean_dec(x_14);
x_19 = lean_ptr_addr(x_16);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
x_23 = lean_array_fset(x_3, x_2, x_16);
lean_dec(x_2);
x_2 = x_22;
x_3 = x_23;
x_10 = x_17;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_16);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_2 = x_26;
x_10 = x_17;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(x_2, x_10, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed), 9, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_15 = lean_apply_8(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ptr_addr(x_14);
lean_dec(x_14);
x_19 = lean_ptr_addr(x_16);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
x_23 = lean_array_fset(x_3, x_2, x_16);
lean_dec(x_2);
x_2 = x_22;
x_3 = x_23;
x_10 = x_17;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_16);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_2 = x_26;
x_10 = x_17;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7(x_2, x_10, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_13 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_16 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 3);
lean_inc(x_19);
x_20 = l_Lean_Expr_isFVar(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_4);
x_21 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_4, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_27 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_4, 0);
lean_inc(x_30);
x_31 = l_Lean_Compiler_LCNF_Simp_isUsed(x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_28);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
lean_inc(x_4);
x_41 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; size_t x_44; size_t x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_45 = lean_ptr_addr(x_28);
x_46 = lean_usize_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_28);
lean_ctor_set(x_41, 0, x_47);
return x_41;
}
else
{
size_t x_48; size_t x_49; uint8_t x_50; 
x_48 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_49 = lean_ptr_addr(x_4);
x_50 = lean_usize_dec_eq(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_3);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_28);
lean_ctor_set(x_41, 0, x_51);
return x_41;
}
else
{
lean_dec(x_28);
lean_dec(x_4);
lean_ctor_set(x_41, 0, x_3);
return x_41;
}
}
}
else
{
lean_object* x_52; size_t x_53; size_t x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_dec(x_41);
x_53 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_54 = lean_ptr_addr(x_28);
x_55 = lean_usize_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_4);
lean_ctor_set(x_56, 1, x_28);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
size_t x_58; size_t x_59; uint8_t x_60; 
x_58 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_59 = lean_ptr_addr(x_4);
x_60 = lean_usize_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_3);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_28);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_52);
return x_62;
}
else
{
lean_object* x_63; 
lean_dec(x_28);
lean_dec(x_4);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_52);
return x_63;
}
}
}
}
}
else
{
uint8_t x_64; 
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
x_64 = !lean_is_exclusive(x_27);
if (x_64 == 0)
{
return x_27;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_27, 0);
x_66 = lean_ctor_get(x_27, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_27);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_ctor_get(x_25, 0);
lean_inc(x_68);
lean_dec(x_25);
x_69 = lean_ctor_get(x_24, 1);
lean_inc(x_69);
lean_dec(x_24);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_4, 0);
lean_inc(x_72);
x_73 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_72, x_71, x_6, x_7, x_8, x_9, x_10, x_11, x_69);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_74);
lean_dec(x_4);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_77 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_70, x_78, x_6, x_7, x_8, x_9, x_10, x_11, x_79);
lean_dec(x_70);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_70);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_81 = !lean_is_exclusive(x_77);
if (x_81 == 0)
{
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_77, 0);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_77);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_70);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_73);
if (x_85 == 0)
{
return x_73;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_73, 0);
x_87 = lean_ctor_get(x_73, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_73);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
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
x_89 = !lean_is_exclusive(x_24);
if (x_89 == 0)
{
return x_24;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_24, 0);
x_91 = lean_ctor_get(x_24, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_24);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_21, 1);
lean_inc(x_93);
lean_dec(x_21);
x_94 = lean_ctor_get(x_22, 0);
lean_inc(x_94);
lean_dec(x_22);
x_95 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_93);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_19);
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
x_100 = !lean_is_exclusive(x_21);
if (x_100 == 0)
{
return x_21;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_21, 0);
x_102 = lean_ctor_get(x_21, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_21);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_ctor_get(x_4, 0);
lean_inc(x_104);
x_105 = l_Lean_Expr_fvarId_x21(x_19);
x_106 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_104, x_105, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_107);
lean_dec(x_4);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_109);
return x_110;
}
else
{
uint8_t x_111; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_106);
if (x_111 == 0)
{
return x_106;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_106, 0);
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_106);
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
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_115 = lean_ctor_get(x_16, 1);
lean_inc(x_115);
lean_dec(x_16);
x_116 = lean_ctor_get(x_17, 0);
lean_inc(x_116);
lean_dec(x_17);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_1);
x_118 = l_Lean_Compiler_LCNF_Simp_simp(x_117, x_6, x_7, x_8, x_9, x_10, x_11, x_115);
return x_118;
}
}
else
{
uint8_t x_119; 
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
x_119 = !lean_is_exclusive(x_16);
if (x_119 == 0)
{
return x_16;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_16, 0);
x_121 = lean_ctor_get(x_16, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_16);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = lean_ctor_get(x_13, 1);
lean_inc(x_123);
lean_dec(x_13);
x_124 = lean_ctor_get(x_14, 0);
lean_inc(x_124);
lean_dec(x_14);
x_125 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_7, x_8, x_9, x_10, x_11, x_123);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_127 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_124, x_128, x_6, x_7, x_8, x_9, x_10, x_11, x_129);
lean_dec(x_124);
return x_130;
}
else
{
uint8_t x_131; 
lean_dec(x_124);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_131 = !lean_is_exclusive(x_127);
if (x_131 == 0)
{
return x_127;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_127, 0);
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_127);
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
x_135 = !lean_is_exclusive(x_13);
if (x_135 == 0)
{
return x_13;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_13, 0);
x_137 = lean_ctor_get(x_13, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_13);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_ptr_addr(x_1);
x_15 = lean_ptr_addr(x_2);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_4);
x_20 = lean_ptr_addr(x_3);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_14 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_Simp_isUsed(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_15, x_5, x_2, x_3, x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_31 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_15, x_5, x_2, x_3, x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_32);
lean_dec(x_2);
lean_dec(x_1);
return x_34;
}
}
}
else
{
uint8_t x_35; 
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
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_apply_9(x_1, x_12, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_ptr_addr(x_1);
x_15 = lean_ptr_addr(x_2);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_4);
x_20 = lean_ptr_addr(x_3);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_14 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_Simp_isUsed(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_15, x_5, x_2, x_3, x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_31 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_15, x_5, x_2, x_3, x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_32);
lean_dec(x_2);
lean_dec(x_1);
return x_34;
}
}
}
else
{
uint8_t x_35; 
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
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp), 8, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed), 9, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___spec__1___rarg), 9, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg(x_1, x_10, x_11, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_Simp_simp(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 8);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 9);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 10);
lean_inc(x_19);
x_20 = lean_nat_dec_eq(x_12, x_13);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_6, 10);
lean_dec(x_22);
x_23 = lean_ctor_get(x_6, 9);
lean_dec(x_23);
x_24 = lean_ctor_get(x_6, 8);
lean_dec(x_24);
x_25 = lean_ctor_get(x_6, 7);
lean_dec(x_25);
x_26 = lean_ctor_get(x_6, 6);
lean_dec(x_26);
x_27 = lean_ctor_get(x_6, 5);
lean_dec(x_27);
x_28 = lean_ctor_get(x_6, 4);
lean_dec(x_28);
x_29 = lean_ctor_get(x_6, 3);
lean_dec(x_29);
x_30 = lean_ctor_get(x_6, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_6, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_6, 0);
lean_dec(x_32);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_12, x_33);
lean_dec(x_12);
lean_ctor_set(x_6, 3, x_34);
x_35 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = 0;
lean_inc(x_37);
x_40 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_39, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_44 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_38, x_37, x_1, x_41, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
x_51 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_41, x_50, x_4, x_5, x_6, x_7, x_49);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_box(0);
x_55 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_38, x_37, x_1, x_52, x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_44);
if (x_56 == 0)
{
return x_44;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_44, 0);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_44);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
case 1:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_35, 1);
lean_inc(x_60);
lean_dec(x_35);
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_60);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_1);
lean_inc(x_61);
x_68 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed), 13, 4);
lean_closure_set(x_68, 0, x_62);
lean_closure_set(x_68, 1, x_61);
lean_closure_set(x_68, 2, x_1);
lean_closure_set(x_68, 3, x_65);
x_69 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
x_71 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_68, x_61, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_61, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_61, 2);
lean_inc(x_73);
x_74 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_72, x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_box(0);
x_76 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_68, x_61, x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_77 = lean_st_ref_get(x_7, x_67);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_st_ref_get(x_3, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_84 = l_Lean_Compiler_LCNF_normFunDeclImp(x_83, x_61, x_82, x_4, x_5, x_6, x_7, x_81);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_87 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_85, x_4, x_5, x_6, x_7, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_68, x_88, x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_92);
lean_dec(x_91);
return x_93;
}
else
{
uint8_t x_94; 
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_87);
if (x_94 == 0)
{
return x_87;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_87, 0);
x_96 = lean_ctor_get(x_87, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_87);
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
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_84);
if (x_98 == 0)
{
return x_84;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_84, 0);
x_100 = lean_ctor_get(x_84, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_84);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_64, 1);
lean_inc(x_102);
lean_dec(x_64);
x_103 = lean_st_ref_get(x_7, x_102);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_st_ref_get(x_3, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_61);
x_110 = l_Lean_Compiler_LCNF_normFunDeclImp(x_109, x_61, x_108, x_4, x_5, x_6, x_7, x_107);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_box(0);
x_114 = lean_unbox(x_65);
lean_dec(x_65);
x_115 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_62, x_61, x_1, x_114, x_111, x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_112);
return x_115;
}
else
{
uint8_t x_116; 
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_110);
if (x_116 == 0)
{
return x_110;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_110, 0);
x_118 = lean_ctor_get(x_110, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_110);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
case 2:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_120 = lean_ctor_get(x_35, 1);
lean_inc(x_120);
lean_dec(x_35);
x_121 = lean_ctor_get(x_1, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_1, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
x_124 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_123, x_2, x_3, x_4, x_5, x_6, x_7, x_120);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
lean_inc(x_1);
lean_inc(x_121);
x_128 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 13, 4);
lean_closure_set(x_128, 0, x_122);
lean_closure_set(x_128, 1, x_121);
lean_closure_set(x_128, 2, x_1);
lean_closure_set(x_128, 3, x_125);
x_129 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_box(0);
x_131 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_128, x_121, x_130, x_2, x_3, x_4, x_5, x_6, x_7, x_127);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_121, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_121, 2);
lean_inc(x_133);
x_134 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_132, x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_box(0);
x_136 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_128, x_121, x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_127);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
x_137 = lean_st_ref_get(x_7, x_127);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_st_ref_get(x_3, x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
x_143 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_144 = l_Lean_Compiler_LCNF_normFunDeclImp(x_143, x_121, x_142, x_4, x_5, x_6, x_7, x_141);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_147 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_145, x_4, x_5, x_6, x_7, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_149);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_128, x_148, x_151, x_2, x_3, x_4, x_5, x_6, x_7, x_152);
lean_dec(x_151);
return x_153;
}
else
{
uint8_t x_154; 
lean_dec(x_128);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_154 = !lean_is_exclusive(x_147);
if (x_154 == 0)
{
return x_147;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_147, 0);
x_156 = lean_ctor_get(x_147, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_147);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_128);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_144);
if (x_158 == 0)
{
return x_144;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_144, 0);
x_160 = lean_ctor_get(x_144, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_144);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_162 = lean_ctor_get(x_124, 1);
lean_inc(x_162);
lean_dec(x_124);
x_163 = lean_st_ref_get(x_7, x_162);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_st_ref_get(x_3, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
lean_dec(x_166);
x_169 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_121);
x_170 = l_Lean_Compiler_LCNF_normFunDeclImp(x_169, x_121, x_168, x_4, x_5, x_6, x_7, x_167);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_box(0);
x_174 = lean_unbox(x_125);
lean_dec(x_125);
x_175 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_122, x_121, x_1, x_174, x_171, x_173, x_2, x_3, x_4, x_5, x_6, x_7, x_172);
return x_175;
}
else
{
uint8_t x_176; 
lean_dec(x_125);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_170);
if (x_176 == 0)
{
return x_170;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_170, 0);
x_178 = lean_ctor_get(x_170, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_170);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
case 3:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; 
x_180 = lean_ctor_get(x_35, 1);
lean_inc(x_180);
lean_dec(x_35);
x_181 = lean_ctor_get(x_1, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_1, 1);
lean_inc(x_182);
x_183 = lean_st_ref_get(x_7, x_180);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_st_ref_get(x_3, x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
lean_dec(x_186);
x_189 = 0;
lean_inc(x_181);
x_190 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_188, x_181, x_189);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_182);
x_191 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_189, x_182, x_2, x_3, x_4, x_5, x_6, x_7, x_187);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_214; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_194 = x_191;
} else {
 lean_dec_ref(x_191);
 x_194 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_192);
lean_inc(x_190);
x_214 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_190, x_192, x_2, x_3, x_4, x_5, x_6, x_7, x_193);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
lean_inc(x_190);
x_217 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_190, x_2, x_3, x_4, x_5, x_6, x_7, x_216);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_219 = lean_array_get_size(x_192);
x_220 = lean_unsigned_to_nat(0u);
x_221 = lean_nat_dec_lt(x_220, x_219);
if (x_221 == 0)
{
lean_dec(x_219);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_195 = x_218;
goto block_213;
}
else
{
uint8_t x_222; 
x_222 = lean_nat_dec_le(x_219, x_219);
if (x_222 == 0)
{
lean_dec(x_219);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_195 = x_218;
goto block_213;
}
else
{
size_t x_223; size_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = 0;
x_224 = lean_usize_of_nat(x_219);
lean_dec(x_219);
x_225 = lean_box(0);
x_226 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_192, x_223, x_224, x_225, x_2, x_3, x_4, x_5, x_6, x_7, x_218);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_195 = x_227;
goto block_213;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_1);
x_228 = lean_ctor_get(x_214, 1);
lean_inc(x_228);
lean_dec(x_214);
x_229 = lean_ctor_get(x_215, 0);
lean_inc(x_229);
lean_dec(x_215);
x_1 = x_229;
x_8 = x_228;
goto _start;
}
}
else
{
uint8_t x_231; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_214);
if (x_231 == 0)
{
return x_214;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_214, 0);
x_233 = lean_ctor_get(x_214, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_214);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
block_213:
{
uint8_t x_196; 
x_196 = lean_name_eq(x_181, x_190);
lean_dec(x_181);
if (x_196 == 0)
{
uint8_t x_197; 
lean_dec(x_182);
x_197 = !lean_is_exclusive(x_1);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_1, 1);
lean_dec(x_198);
x_199 = lean_ctor_get(x_1, 0);
lean_dec(x_199);
lean_ctor_set(x_1, 1, x_192);
lean_ctor_set(x_1, 0, x_190);
if (lean_is_scalar(x_194)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_194;
}
lean_ctor_set(x_200, 0, x_1);
lean_ctor_set(x_200, 1, x_195);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_1);
x_201 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_201, 0, x_190);
lean_ctor_set(x_201, 1, x_192);
if (lean_is_scalar(x_194)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_194;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_195);
return x_202;
}
}
else
{
size_t x_203; size_t x_204; uint8_t x_205; 
x_203 = lean_ptr_addr(x_182);
lean_dec(x_182);
x_204 = lean_ptr_addr(x_192);
x_205 = lean_usize_dec_eq(x_203, x_204);
if (x_205 == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_1);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_1, 1);
lean_dec(x_207);
x_208 = lean_ctor_get(x_1, 0);
lean_dec(x_208);
lean_ctor_set(x_1, 1, x_192);
lean_ctor_set(x_1, 0, x_190);
if (lean_is_scalar(x_194)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_194;
}
lean_ctor_set(x_209, 0, x_1);
lean_ctor_set(x_209, 1, x_195);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_1);
x_210 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_210, 0, x_190);
lean_ctor_set(x_210, 1, x_192);
if (lean_is_scalar(x_194)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_194;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_195);
return x_211;
}
}
else
{
lean_object* x_212; 
lean_dec(x_192);
lean_dec(x_190);
if (lean_is_scalar(x_194)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_194;
}
lean_ctor_set(x_212, 0, x_1);
lean_ctor_set(x_212, 1, x_195);
return x_212;
}
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_190);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_191);
if (x_235 == 0)
{
return x_191;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_191, 0);
x_237 = lean_ctor_get(x_191, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_191);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
case 4:
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_35, 1);
lean_inc(x_239);
lean_dec(x_35);
x_240 = lean_ctor_get(x_1, 0);
lean_inc(x_240);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_240);
x_241 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_240, x_2, x_3, x_4, x_5, x_6, x_7, x_239);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_240, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_240, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_240, 2);
lean_inc(x_246);
x_247 = lean_ctor_get(x_240, 3);
lean_inc(x_247);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 lean_ctor_release(x_240, 3);
 x_248 = x_240;
} else {
 lean_dec_ref(x_240);
 x_248 = lean_box(0);
}
x_249 = lean_st_ref_get(x_7, x_243);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
lean_dec(x_249);
x_251 = lean_st_ref_get(x_3, x_250);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_ctor_get(x_252, 0);
lean_inc(x_254);
lean_dec(x_252);
x_255 = 0;
lean_inc(x_246);
x_256 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_254, x_246, x_255);
x_257 = lean_st_ref_get(x_7, x_253);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec(x_257);
x_259 = lean_st_ref_get(x_3, x_258);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
lean_dec(x_260);
lean_inc(x_245);
x_263 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_262, x_255, x_245);
lean_inc(x_256);
x_264 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_256, x_2, x_3, x_4, x_5, x_6, x_7, x_261);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
lean_inc(x_256);
x_266 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__8), 9, 1);
lean_closure_set(x_266, 0, x_256);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_247);
x_267 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_247, x_266, x_2, x_3, x_4, x_5, x_6, x_7, x_265);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_270 = x_267;
} else {
 lean_dec_ref(x_267);
 x_270 = lean_box(0);
}
x_271 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_268, x_2, x_3, x_4, x_5, x_6, x_7, x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_306; lean_object* x_307; uint8_t x_318; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_274 = x_271;
} else {
 lean_dec_ref(x_271);
 x_274 = lean_box(0);
}
x_306 = lean_array_get_size(x_272);
x_318 = lean_nat_dec_eq(x_306, x_33);
if (x_318 == 0)
{
lean_object* x_319; 
lean_dec(x_306);
lean_dec(x_270);
x_319 = lean_box(0);
x_275 = x_319;
goto block_305;
}
else
{
lean_object* x_320; uint8_t x_321; 
x_320 = lean_unsigned_to_nat(0u);
x_321 = lean_nat_dec_lt(x_320, x_306);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4;
x_323 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; 
lean_dec(x_323);
lean_dec(x_306);
lean_dec(x_270);
x_324 = lean_box(0);
x_275 = x_324;
goto block_305;
}
else
{
lean_object* x_325; 
lean_dec(x_323);
lean_dec(x_274);
lean_dec(x_263);
lean_dec(x_256);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_1);
x_325 = lean_box(0);
x_307 = x_325;
goto block_317;
}
}
else
{
lean_object* x_326; 
x_326 = lean_array_fget(x_272, x_320);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
lean_dec(x_326);
lean_dec(x_306);
lean_dec(x_270);
x_327 = lean_box(0);
x_275 = x_327;
goto block_305;
}
else
{
lean_object* x_328; 
lean_dec(x_326);
lean_dec(x_274);
lean_dec(x_263);
lean_dec(x_256);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_1);
x_328 = lean_box(0);
x_307 = x_328;
goto block_317;
}
}
}
block_305:
{
size_t x_276; size_t x_277; uint8_t x_278; 
lean_dec(x_275);
x_276 = lean_ptr_addr(x_247);
lean_dec(x_247);
x_277 = lean_ptr_addr(x_272);
x_278 = lean_usize_dec_eq(x_276, x_277);
if (x_278 == 0)
{
uint8_t x_279; 
lean_dec(x_246);
lean_dec(x_245);
x_279 = !lean_is_exclusive(x_1);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_1, 0);
lean_dec(x_280);
if (lean_is_scalar(x_248)) {
 x_281 = lean_alloc_ctor(0, 4, 0);
} else {
 x_281 = x_248;
}
lean_ctor_set(x_281, 0, x_244);
lean_ctor_set(x_281, 1, x_263);
lean_ctor_set(x_281, 2, x_256);
lean_ctor_set(x_281, 3, x_272);
lean_ctor_set(x_1, 0, x_281);
if (lean_is_scalar(x_274)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_274;
}
lean_ctor_set(x_282, 0, x_1);
lean_ctor_set(x_282, 1, x_273);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_1);
if (lean_is_scalar(x_248)) {
 x_283 = lean_alloc_ctor(0, 4, 0);
} else {
 x_283 = x_248;
}
lean_ctor_set(x_283, 0, x_244);
lean_ctor_set(x_283, 1, x_263);
lean_ctor_set(x_283, 2, x_256);
lean_ctor_set(x_283, 3, x_272);
x_284 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_284, 0, x_283);
if (lean_is_scalar(x_274)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_274;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_273);
return x_285;
}
}
else
{
size_t x_286; size_t x_287; uint8_t x_288; 
x_286 = lean_ptr_addr(x_245);
lean_dec(x_245);
x_287 = lean_ptr_addr(x_263);
x_288 = lean_usize_dec_eq(x_286, x_287);
if (x_288 == 0)
{
uint8_t x_289; 
lean_dec(x_246);
x_289 = !lean_is_exclusive(x_1);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_1, 0);
lean_dec(x_290);
if (lean_is_scalar(x_248)) {
 x_291 = lean_alloc_ctor(0, 4, 0);
} else {
 x_291 = x_248;
}
lean_ctor_set(x_291, 0, x_244);
lean_ctor_set(x_291, 1, x_263);
lean_ctor_set(x_291, 2, x_256);
lean_ctor_set(x_291, 3, x_272);
lean_ctor_set(x_1, 0, x_291);
if (lean_is_scalar(x_274)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_274;
}
lean_ctor_set(x_292, 0, x_1);
lean_ctor_set(x_292, 1, x_273);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_1);
if (lean_is_scalar(x_248)) {
 x_293 = lean_alloc_ctor(0, 4, 0);
} else {
 x_293 = x_248;
}
lean_ctor_set(x_293, 0, x_244);
lean_ctor_set(x_293, 1, x_263);
lean_ctor_set(x_293, 2, x_256);
lean_ctor_set(x_293, 3, x_272);
x_294 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_294, 0, x_293);
if (lean_is_scalar(x_274)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_274;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_273);
return x_295;
}
}
else
{
uint8_t x_296; 
x_296 = lean_name_eq(x_246, x_256);
lean_dec(x_246);
if (x_296 == 0)
{
uint8_t x_297; 
x_297 = !lean_is_exclusive(x_1);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_1, 0);
lean_dec(x_298);
if (lean_is_scalar(x_248)) {
 x_299 = lean_alloc_ctor(0, 4, 0);
} else {
 x_299 = x_248;
}
lean_ctor_set(x_299, 0, x_244);
lean_ctor_set(x_299, 1, x_263);
lean_ctor_set(x_299, 2, x_256);
lean_ctor_set(x_299, 3, x_272);
lean_ctor_set(x_1, 0, x_299);
if (lean_is_scalar(x_274)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_274;
}
lean_ctor_set(x_300, 0, x_1);
lean_ctor_set(x_300, 1, x_273);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_1);
if (lean_is_scalar(x_248)) {
 x_301 = lean_alloc_ctor(0, 4, 0);
} else {
 x_301 = x_248;
}
lean_ctor_set(x_301, 0, x_244);
lean_ctor_set(x_301, 1, x_263);
lean_ctor_set(x_301, 2, x_256);
lean_ctor_set(x_301, 3, x_272);
x_302 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_302, 0, x_301);
if (lean_is_scalar(x_274)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_274;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_273);
return x_303;
}
}
else
{
lean_object* x_304; 
lean_dec(x_272);
lean_dec(x_263);
lean_dec(x_256);
lean_dec(x_248);
lean_dec(x_244);
if (lean_is_scalar(x_274)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_274;
}
lean_ctor_set(x_304, 0, x_1);
lean_ctor_set(x_304, 1, x_273);
return x_304;
}
}
}
}
block_317:
{
lean_object* x_308; uint8_t x_309; 
lean_dec(x_307);
x_308 = lean_unsigned_to_nat(0u);
x_309 = lean_nat_dec_lt(x_308, x_306);
lean_dec(x_306);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_272);
x_310 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4;
x_311 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_310);
x_312 = l_Lean_Compiler_LCNF_AltCore_getCode(x_311);
lean_dec(x_311);
if (lean_is_scalar(x_270)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_270;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_273);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_array_fget(x_272, x_308);
lean_dec(x_272);
x_315 = l_Lean_Compiler_LCNF_AltCore_getCode(x_314);
lean_dec(x_314);
if (lean_is_scalar(x_270)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_270;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_273);
return x_316;
}
}
}
else
{
uint8_t x_329; 
lean_dec(x_270);
lean_dec(x_263);
lean_dec(x_256);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_1);
x_329 = !lean_is_exclusive(x_271);
if (x_329 == 0)
{
return x_271;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_271, 0);
x_331 = lean_ctor_get(x_271, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_271);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
else
{
uint8_t x_333; 
lean_dec(x_263);
lean_dec(x_256);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_333 = !lean_is_exclusive(x_267);
if (x_333 == 0)
{
return x_267;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_267, 0);
x_335 = lean_ctor_get(x_267, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_267);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
uint8_t x_337; 
lean_dec(x_240);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_337 = !lean_is_exclusive(x_241);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_ctor_get(x_241, 0);
lean_dec(x_338);
x_339 = lean_ctor_get(x_242, 0);
lean_inc(x_339);
lean_dec(x_242);
lean_ctor_set(x_241, 0, x_339);
return x_241;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_241, 1);
lean_inc(x_340);
lean_dec(x_241);
x_341 = lean_ctor_get(x_242, 0);
lean_inc(x_341);
lean_dec(x_242);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
}
else
{
uint8_t x_343; 
lean_dec(x_240);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_343 = !lean_is_exclusive(x_241);
if (x_343 == 0)
{
return x_241;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_241, 0);
x_345 = lean_ctor_get(x_241, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_241);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
}
}
case 5:
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_347 = lean_ctor_get(x_35, 1);
lean_inc(x_347);
lean_dec(x_35);
x_348 = lean_ctor_get(x_1, 0);
lean_inc(x_348);
x_349 = lean_st_ref_get(x_7, x_347);
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
lean_dec(x_349);
x_351 = lean_st_ref_get(x_3, x_350);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
lean_dec(x_352);
x_355 = 0;
lean_inc(x_348);
x_356 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_354, x_348, x_355);
lean_inc(x_356);
x_357 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_356, x_2, x_3, x_4, x_5, x_6, x_7, x_353);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_358 = !lean_is_exclusive(x_357);
if (x_358 == 0)
{
lean_object* x_359; uint8_t x_360; 
x_359 = lean_ctor_get(x_357, 0);
lean_dec(x_359);
x_360 = lean_name_eq(x_348, x_356);
lean_dec(x_348);
if (x_360 == 0)
{
uint8_t x_361; 
x_361 = !lean_is_exclusive(x_1);
if (x_361 == 0)
{
lean_object* x_362; 
x_362 = lean_ctor_get(x_1, 0);
lean_dec(x_362);
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set(x_357, 0, x_1);
return x_357;
}
else
{
lean_object* x_363; 
lean_dec(x_1);
x_363 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_363, 0, x_356);
lean_ctor_set(x_357, 0, x_363);
return x_357;
}
}
else
{
lean_dec(x_356);
lean_ctor_set(x_357, 0, x_1);
return x_357;
}
}
else
{
lean_object* x_364; uint8_t x_365; 
x_364 = lean_ctor_get(x_357, 1);
lean_inc(x_364);
lean_dec(x_357);
x_365 = lean_name_eq(x_348, x_356);
lean_dec(x_348);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_366 = x_1;
} else {
 lean_dec_ref(x_1);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(5, 1, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_356);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_364);
return x_368;
}
else
{
lean_object* x_369; 
lean_dec(x_356);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_1);
lean_ctor_set(x_369, 1, x_364);
return x_369;
}
}
}
default: 
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_370 = lean_ctor_get(x_35, 1);
lean_inc(x_370);
lean_dec(x_35);
x_371 = lean_ctor_get(x_1, 0);
lean_inc(x_371);
x_372 = lean_st_ref_get(x_7, x_370);
lean_dec(x_7);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
lean_dec(x_372);
x_374 = lean_st_ref_get(x_3, x_373);
lean_dec(x_3);
x_375 = !lean_is_exclusive(x_374);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; lean_object* x_379; size_t x_380; size_t x_381; uint8_t x_382; 
x_376 = lean_ctor_get(x_374, 0);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
lean_dec(x_376);
x_378 = 0;
lean_inc(x_371);
x_379 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_377, x_378, x_371);
x_380 = lean_ptr_addr(x_371);
lean_dec(x_371);
x_381 = lean_ptr_addr(x_379);
x_382 = lean_usize_dec_eq(x_380, x_381);
if (x_382 == 0)
{
uint8_t x_383; 
x_383 = !lean_is_exclusive(x_1);
if (x_383 == 0)
{
lean_object* x_384; 
x_384 = lean_ctor_get(x_1, 0);
lean_dec(x_384);
lean_ctor_set(x_1, 0, x_379);
lean_ctor_set(x_374, 0, x_1);
return x_374;
}
else
{
lean_object* x_385; 
lean_dec(x_1);
x_385 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_385, 0, x_379);
lean_ctor_set(x_374, 0, x_385);
return x_374;
}
}
else
{
lean_dec(x_379);
lean_ctor_set(x_374, 0, x_1);
return x_374;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; size_t x_391; size_t x_392; uint8_t x_393; 
x_386 = lean_ctor_get(x_374, 0);
x_387 = lean_ctor_get(x_374, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_374);
x_388 = lean_ctor_get(x_386, 0);
lean_inc(x_388);
lean_dec(x_386);
x_389 = 0;
lean_inc(x_371);
x_390 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_388, x_389, x_371);
x_391 = lean_ptr_addr(x_371);
lean_dec(x_371);
x_392 = lean_ptr_addr(x_390);
x_393 = lean_usize_dec_eq(x_391, x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_394 = x_1;
} else {
 lean_dec_ref(x_1);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(6, 1, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_390);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_387);
return x_396;
}
else
{
lean_object* x_397; 
lean_dec(x_390);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_1);
lean_ctor_set(x_397, 1, x_387);
return x_397;
}
}
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_6);
x_398 = lean_unsigned_to_nat(1u);
x_399 = lean_nat_add(x_12, x_398);
lean_dec(x_12);
x_400 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_400, 0, x_9);
lean_ctor_set(x_400, 1, x_10);
lean_ctor_set(x_400, 2, x_11);
lean_ctor_set(x_400, 3, x_399);
lean_ctor_set(x_400, 4, x_13);
lean_ctor_set(x_400, 5, x_14);
lean_ctor_set(x_400, 6, x_15);
lean_ctor_set(x_400, 7, x_16);
lean_ctor_set(x_400, 8, x_17);
lean_ctor_set(x_400, 9, x_18);
lean_ctor_set(x_400, 10, x_19);
x_401 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_5, x_400, x_7, x_8);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
lean_dec(x_401);
x_403 = lean_ctor_get(x_1, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_1, 1);
lean_inc(x_404);
x_405 = 0;
lean_inc(x_403);
x_406 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_405, x_403, x_2, x_3, x_4, x_5, x_400, x_7, x_402);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_409 = lean_ctor_get(x_407, 3);
lean_inc(x_409);
lean_inc(x_7);
lean_inc(x_400);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_410 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_409, x_2, x_3, x_4, x_5, x_400, x_7, x_408);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = lean_box(0);
x_414 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_404, x_403, x_1, x_407, x_413, x_2, x_3, x_4, x_5, x_400, x_7, x_412);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_415 = lean_ctor_get(x_410, 1);
lean_inc(x_415);
lean_dec(x_410);
x_416 = lean_ctor_get(x_411, 0);
lean_inc(x_416);
lean_dec(x_411);
x_417 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_407, x_416, x_4, x_5, x_400, x_7, x_415);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_box(0);
x_421 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_404, x_403, x_1, x_418, x_420, x_2, x_3, x_4, x_5, x_400, x_7, x_419);
return x_421;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_407);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_422 = lean_ctor_get(x_410, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_410, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_424 = x_410;
} else {
 lean_dec_ref(x_410);
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
case 1:
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; 
x_426 = lean_ctor_get(x_401, 1);
lean_inc(x_426);
lean_dec(x_401);
x_427 = lean_ctor_get(x_1, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_1, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 0);
lean_inc(x_429);
x_430 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_429, x_2, x_3, x_4, x_5, x_400, x_7, x_426);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_unbox(x_431);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_433 = lean_ctor_get(x_430, 1);
lean_inc(x_433);
lean_dec(x_430);
lean_inc(x_1);
lean_inc(x_427);
x_434 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed), 13, 4);
lean_closure_set(x_434, 0, x_428);
lean_closure_set(x_434, 1, x_427);
lean_closure_set(x_434, 2, x_1);
lean_closure_set(x_434, 3, x_431);
x_435 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; 
x_436 = lean_box(0);
x_437 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_434, x_427, x_436, x_2, x_3, x_4, x_5, x_400, x_7, x_433);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; uint8_t x_440; 
x_438 = lean_ctor_get(x_427, 3);
lean_inc(x_438);
x_439 = lean_ctor_get(x_427, 2);
lean_inc(x_439);
x_440 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_438, x_439);
lean_dec(x_439);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_box(0);
x_442 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_434, x_427, x_441, x_2, x_3, x_4, x_5, x_400, x_7, x_433);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; 
x_443 = lean_st_ref_get(x_7, x_433);
x_444 = lean_ctor_get(x_443, 1);
lean_inc(x_444);
lean_dec(x_443);
x_445 = lean_st_ref_get(x_3, x_444);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
x_448 = lean_ctor_get(x_446, 0);
lean_inc(x_448);
lean_dec(x_446);
x_449 = 0;
lean_inc(x_7);
lean_inc(x_400);
lean_inc(x_5);
lean_inc(x_4);
x_450 = l_Lean_Compiler_LCNF_normFunDeclImp(x_449, x_427, x_448, x_4, x_5, x_400, x_7, x_447);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
lean_inc(x_7);
lean_inc(x_400);
lean_inc(x_5);
lean_inc(x_4);
x_453 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_451, x_4, x_5, x_400, x_7, x_452);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_456 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_400, x_7, x_455);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_434, x_454, x_457, x_2, x_3, x_4, x_5, x_400, x_7, x_458);
lean_dec(x_457);
return x_459;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_434);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_460 = lean_ctor_get(x_453, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_453, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_462 = x_453;
} else {
 lean_dec_ref(x_453);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_461);
return x_463;
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_434);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_464 = lean_ctor_get(x_450, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_450, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_466 = x_450;
} else {
 lean_dec_ref(x_450);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_467 = x_466;
}
lean_ctor_set(x_467, 0, x_464);
lean_ctor_set(x_467, 1, x_465);
return x_467;
}
}
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; 
x_468 = lean_ctor_get(x_430, 1);
lean_inc(x_468);
lean_dec(x_430);
x_469 = lean_st_ref_get(x_7, x_468);
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
lean_dec(x_469);
x_471 = lean_st_ref_get(x_3, x_470);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec(x_471);
x_474 = lean_ctor_get(x_472, 0);
lean_inc(x_474);
lean_dec(x_472);
x_475 = 0;
lean_inc(x_7);
lean_inc(x_400);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_427);
x_476 = l_Lean_Compiler_LCNF_normFunDeclImp(x_475, x_427, x_474, x_4, x_5, x_400, x_7, x_473);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
x_479 = lean_box(0);
x_480 = lean_unbox(x_431);
lean_dec(x_431);
x_481 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_428, x_427, x_1, x_480, x_477, x_479, x_2, x_3, x_4, x_5, x_400, x_7, x_478);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_431);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_482 = lean_ctor_get(x_476, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_476, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_484 = x_476;
} else {
 lean_dec_ref(x_476);
 x_484 = lean_box(0);
}
if (lean_is_scalar(x_484)) {
 x_485 = lean_alloc_ctor(1, 2, 0);
} else {
 x_485 = x_484;
}
lean_ctor_set(x_485, 0, x_482);
lean_ctor_set(x_485, 1, x_483);
return x_485;
}
}
}
case 2:
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; 
x_486 = lean_ctor_get(x_401, 1);
lean_inc(x_486);
lean_dec(x_401);
x_487 = lean_ctor_get(x_1, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_1, 1);
lean_inc(x_488);
x_489 = lean_ctor_get(x_487, 0);
lean_inc(x_489);
x_490 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_489, x_2, x_3, x_4, x_5, x_400, x_7, x_486);
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_unbox(x_491);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; uint8_t x_495; 
x_493 = lean_ctor_get(x_490, 1);
lean_inc(x_493);
lean_dec(x_490);
lean_inc(x_1);
lean_inc(x_487);
x_494 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 13, 4);
lean_closure_set(x_494, 0, x_488);
lean_closure_set(x_494, 1, x_487);
lean_closure_set(x_494, 2, x_1);
lean_closure_set(x_494, 3, x_491);
x_495 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_495 == 0)
{
lean_object* x_496; lean_object* x_497; 
x_496 = lean_box(0);
x_497 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_494, x_487, x_496, x_2, x_3, x_4, x_5, x_400, x_7, x_493);
return x_497;
}
else
{
lean_object* x_498; lean_object* x_499; uint8_t x_500; 
x_498 = lean_ctor_get(x_487, 3);
lean_inc(x_498);
x_499 = lean_ctor_get(x_487, 2);
lean_inc(x_499);
x_500 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_498, x_499);
lean_dec(x_499);
if (x_500 == 0)
{
lean_object* x_501; lean_object* x_502; 
x_501 = lean_box(0);
x_502 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_494, x_487, x_501, x_2, x_3, x_4, x_5, x_400, x_7, x_493);
return x_502;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; 
x_503 = lean_st_ref_get(x_7, x_493);
x_504 = lean_ctor_get(x_503, 1);
lean_inc(x_504);
lean_dec(x_503);
x_505 = lean_st_ref_get(x_3, x_504);
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_ctor_get(x_506, 0);
lean_inc(x_508);
lean_dec(x_506);
x_509 = 0;
lean_inc(x_7);
lean_inc(x_400);
lean_inc(x_5);
lean_inc(x_4);
x_510 = l_Lean_Compiler_LCNF_normFunDeclImp(x_509, x_487, x_508, x_4, x_5, x_400, x_7, x_507);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
lean_inc(x_7);
lean_inc(x_400);
lean_inc(x_5);
lean_inc(x_4);
x_513 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_511, x_4, x_5, x_400, x_7, x_512);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_400, x_7, x_515);
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_516, 1);
lean_inc(x_518);
lean_dec(x_516);
x_519 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_494, x_514, x_517, x_2, x_3, x_4, x_5, x_400, x_7, x_518);
lean_dec(x_517);
return x_519;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_494);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_520 = lean_ctor_get(x_513, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_513, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_522 = x_513;
} else {
 lean_dec_ref(x_513);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_522;
}
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_521);
return x_523;
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_494);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_524 = lean_ctor_get(x_510, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_510, 1);
lean_inc(x_525);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 lean_ctor_release(x_510, 1);
 x_526 = x_510;
} else {
 lean_dec_ref(x_510);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(1, 2, 0);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_524);
lean_ctor_set(x_527, 1, x_525);
return x_527;
}
}
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; lean_object* x_536; 
x_528 = lean_ctor_get(x_490, 1);
lean_inc(x_528);
lean_dec(x_490);
x_529 = lean_st_ref_get(x_7, x_528);
x_530 = lean_ctor_get(x_529, 1);
lean_inc(x_530);
lean_dec(x_529);
x_531 = lean_st_ref_get(x_3, x_530);
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec(x_531);
x_534 = lean_ctor_get(x_532, 0);
lean_inc(x_534);
lean_dec(x_532);
x_535 = 0;
lean_inc(x_7);
lean_inc(x_400);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_487);
x_536 = l_Lean_Compiler_LCNF_normFunDeclImp(x_535, x_487, x_534, x_4, x_5, x_400, x_7, x_533);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; lean_object* x_541; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = lean_box(0);
x_540 = lean_unbox(x_491);
lean_dec(x_491);
x_541 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_488, x_487, x_1, x_540, x_537, x_539, x_2, x_3, x_4, x_5, x_400, x_7, x_538);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_491);
lean_dec(x_488);
lean_dec(x_487);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_542 = lean_ctor_get(x_536, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_536, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 lean_ctor_release(x_536, 1);
 x_544 = x_536;
} else {
 lean_dec_ref(x_536);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 2, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_542);
lean_ctor_set(x_545, 1, x_543);
return x_545;
}
}
}
case 3:
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; lean_object* x_556; lean_object* x_557; 
x_546 = lean_ctor_get(x_401, 1);
lean_inc(x_546);
lean_dec(x_401);
x_547 = lean_ctor_get(x_1, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_1, 1);
lean_inc(x_548);
x_549 = lean_st_ref_get(x_7, x_546);
x_550 = lean_ctor_get(x_549, 1);
lean_inc(x_550);
lean_dec(x_549);
x_551 = lean_st_ref_get(x_3, x_550);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_554 = lean_ctor_get(x_552, 0);
lean_inc(x_554);
lean_dec(x_552);
x_555 = 0;
lean_inc(x_547);
x_556 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_554, x_547, x_555);
lean_inc(x_7);
lean_inc(x_400);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_548);
x_557 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_555, x_548, x_2, x_3, x_4, x_5, x_400, x_7, x_553);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_574; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_560 = x_557;
} else {
 lean_dec_ref(x_557);
 x_560 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_400);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_558);
lean_inc(x_556);
x_574 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_556, x_558, x_2, x_3, x_4, x_5, x_400, x_7, x_559);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; 
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec(x_574);
lean_inc(x_556);
x_577 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_556, x_2, x_3, x_4, x_5, x_400, x_7, x_576);
x_578 = lean_ctor_get(x_577, 1);
lean_inc(x_578);
lean_dec(x_577);
x_579 = lean_array_get_size(x_558);
x_580 = lean_unsigned_to_nat(0u);
x_581 = lean_nat_dec_lt(x_580, x_579);
if (x_581 == 0)
{
lean_dec(x_579);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_561 = x_578;
goto block_573;
}
else
{
uint8_t x_582; 
x_582 = lean_nat_dec_le(x_579, x_579);
if (x_582 == 0)
{
lean_dec(x_579);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_561 = x_578;
goto block_573;
}
else
{
size_t x_583; size_t x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_583 = 0;
x_584 = lean_usize_of_nat(x_579);
lean_dec(x_579);
x_585 = lean_box(0);
x_586 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_558, x_583, x_584, x_585, x_2, x_3, x_4, x_5, x_400, x_7, x_578);
lean_dec(x_7);
lean_dec(x_400);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
lean_dec(x_586);
x_561 = x_587;
goto block_573;
}
}
}
else
{
lean_object* x_588; lean_object* x_589; 
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_556);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_1);
x_588 = lean_ctor_get(x_574, 1);
lean_inc(x_588);
lean_dec(x_574);
x_589 = lean_ctor_get(x_575, 0);
lean_inc(x_589);
lean_dec(x_575);
x_1 = x_589;
x_6 = x_400;
x_8 = x_588;
goto _start;
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_556);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_591 = lean_ctor_get(x_574, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_574, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_593 = x_574;
} else {
 lean_dec_ref(x_574);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(1, 2, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_592);
return x_594;
}
block_573:
{
uint8_t x_562; 
x_562 = lean_name_eq(x_547, x_556);
lean_dec(x_547);
if (x_562 == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_548);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_563 = x_1;
} else {
 lean_dec_ref(x_1);
 x_563 = lean_box(0);
}
if (lean_is_scalar(x_563)) {
 x_564 = lean_alloc_ctor(3, 2, 0);
} else {
 x_564 = x_563;
}
lean_ctor_set(x_564, 0, x_556);
lean_ctor_set(x_564, 1, x_558);
if (lean_is_scalar(x_560)) {
 x_565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_565 = x_560;
}
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_561);
return x_565;
}
else
{
size_t x_566; size_t x_567; uint8_t x_568; 
x_566 = lean_ptr_addr(x_548);
lean_dec(x_548);
x_567 = lean_ptr_addr(x_558);
x_568 = lean_usize_dec_eq(x_566, x_567);
if (x_568 == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_569 = x_1;
} else {
 lean_dec_ref(x_1);
 x_569 = lean_box(0);
}
if (lean_is_scalar(x_569)) {
 x_570 = lean_alloc_ctor(3, 2, 0);
} else {
 x_570 = x_569;
}
lean_ctor_set(x_570, 0, x_556);
lean_ctor_set(x_570, 1, x_558);
if (lean_is_scalar(x_560)) {
 x_571 = lean_alloc_ctor(0, 2, 0);
} else {
 x_571 = x_560;
}
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_561);
return x_571;
}
else
{
lean_object* x_572; 
lean_dec(x_558);
lean_dec(x_556);
if (lean_is_scalar(x_560)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_560;
}
lean_ctor_set(x_572, 0, x_1);
lean_ctor_set(x_572, 1, x_561);
return x_572;
}
}
}
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
lean_dec(x_556);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_595 = lean_ctor_get(x_557, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_557, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_597 = x_557;
} else {
 lean_dec_ref(x_557);
 x_597 = lean_box(0);
}
if (lean_is_scalar(x_597)) {
 x_598 = lean_alloc_ctor(1, 2, 0);
} else {
 x_598 = x_597;
}
lean_ctor_set(x_598, 0, x_595);
lean_ctor_set(x_598, 1, x_596);
return x_598;
}
}
case 4:
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = lean_ctor_get(x_401, 1);
lean_inc(x_599);
lean_dec(x_401);
x_600 = lean_ctor_get(x_1, 0);
lean_inc(x_600);
lean_inc(x_7);
lean_inc(x_400);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_600);
x_601 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_600, x_2, x_3, x_4, x_5, x_400, x_7, x_599);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec(x_601);
x_604 = lean_ctor_get(x_600, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_600, 1);
lean_inc(x_605);
x_606 = lean_ctor_get(x_600, 2);
lean_inc(x_606);
x_607 = lean_ctor_get(x_600, 3);
lean_inc(x_607);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 lean_ctor_release(x_600, 2);
 lean_ctor_release(x_600, 3);
 x_608 = x_600;
} else {
 lean_dec_ref(x_600);
 x_608 = lean_box(0);
}
x_609 = lean_st_ref_get(x_7, x_603);
x_610 = lean_ctor_get(x_609, 1);
lean_inc(x_610);
lean_dec(x_609);
x_611 = lean_st_ref_get(x_3, x_610);
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_614 = lean_ctor_get(x_612, 0);
lean_inc(x_614);
lean_dec(x_612);
x_615 = 0;
lean_inc(x_606);
x_616 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_614, x_606, x_615);
x_617 = lean_st_ref_get(x_7, x_613);
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
lean_dec(x_617);
x_619 = lean_st_ref_get(x_3, x_618);
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
x_622 = lean_ctor_get(x_620, 0);
lean_inc(x_622);
lean_dec(x_620);
lean_inc(x_605);
x_623 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_622, x_615, x_605);
lean_inc(x_616);
x_624 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_616, x_2, x_3, x_4, x_5, x_400, x_7, x_621);
x_625 = lean_ctor_get(x_624, 1);
lean_inc(x_625);
lean_dec(x_624);
lean_inc(x_616);
x_626 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__8), 9, 1);
lean_closure_set(x_626, 0, x_616);
lean_inc(x_7);
lean_inc(x_400);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_607);
x_627 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_607, x_626, x_2, x_3, x_4, x_5, x_400, x_7, x_625);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_627, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_630 = x_627;
} else {
 lean_dec_ref(x_627);
 x_630 = lean_box(0);
}
x_631 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_628, x_2, x_3, x_4, x_5, x_400, x_7, x_629);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_657; lean_object* x_658; uint8_t x_669; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_634 = x_631;
} else {
 lean_dec_ref(x_631);
 x_634 = lean_box(0);
}
x_657 = lean_array_get_size(x_632);
x_669 = lean_nat_dec_eq(x_657, x_398);
if (x_669 == 0)
{
lean_object* x_670; 
lean_dec(x_657);
lean_dec(x_630);
x_670 = lean_box(0);
x_635 = x_670;
goto block_656;
}
else
{
lean_object* x_671; uint8_t x_672; 
x_671 = lean_unsigned_to_nat(0u);
x_672 = lean_nat_dec_lt(x_671, x_657);
if (x_672 == 0)
{
lean_object* x_673; lean_object* x_674; 
x_673 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4;
x_674 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_673);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; 
lean_dec(x_674);
lean_dec(x_657);
lean_dec(x_630);
x_675 = lean_box(0);
x_635 = x_675;
goto block_656;
}
else
{
lean_object* x_676; 
lean_dec(x_674);
lean_dec(x_634);
lean_dec(x_623);
lean_dec(x_616);
lean_dec(x_608);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_1);
x_676 = lean_box(0);
x_658 = x_676;
goto block_668;
}
}
else
{
lean_object* x_677; 
x_677 = lean_array_fget(x_632, x_671);
if (lean_obj_tag(x_677) == 0)
{
lean_object* x_678; 
lean_dec(x_677);
lean_dec(x_657);
lean_dec(x_630);
x_678 = lean_box(0);
x_635 = x_678;
goto block_656;
}
else
{
lean_object* x_679; 
lean_dec(x_677);
lean_dec(x_634);
lean_dec(x_623);
lean_dec(x_616);
lean_dec(x_608);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_1);
x_679 = lean_box(0);
x_658 = x_679;
goto block_668;
}
}
}
block_656:
{
size_t x_636; size_t x_637; uint8_t x_638; 
lean_dec(x_635);
x_636 = lean_ptr_addr(x_607);
lean_dec(x_607);
x_637 = lean_ptr_addr(x_632);
x_638 = lean_usize_dec_eq(x_636, x_637);
if (x_638 == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_606);
lean_dec(x_605);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_639 = x_1;
} else {
 lean_dec_ref(x_1);
 x_639 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_640 = lean_alloc_ctor(0, 4, 0);
} else {
 x_640 = x_608;
}
lean_ctor_set(x_640, 0, x_604);
lean_ctor_set(x_640, 1, x_623);
lean_ctor_set(x_640, 2, x_616);
lean_ctor_set(x_640, 3, x_632);
if (lean_is_scalar(x_639)) {
 x_641 = lean_alloc_ctor(4, 1, 0);
} else {
 x_641 = x_639;
}
lean_ctor_set(x_641, 0, x_640);
if (lean_is_scalar(x_634)) {
 x_642 = lean_alloc_ctor(0, 2, 0);
} else {
 x_642 = x_634;
}
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_633);
return x_642;
}
else
{
size_t x_643; size_t x_644; uint8_t x_645; 
x_643 = lean_ptr_addr(x_605);
lean_dec(x_605);
x_644 = lean_ptr_addr(x_623);
x_645 = lean_usize_dec_eq(x_643, x_644);
if (x_645 == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_606);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_646 = x_1;
} else {
 lean_dec_ref(x_1);
 x_646 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_647 = lean_alloc_ctor(0, 4, 0);
} else {
 x_647 = x_608;
}
lean_ctor_set(x_647, 0, x_604);
lean_ctor_set(x_647, 1, x_623);
lean_ctor_set(x_647, 2, x_616);
lean_ctor_set(x_647, 3, x_632);
if (lean_is_scalar(x_646)) {
 x_648 = lean_alloc_ctor(4, 1, 0);
} else {
 x_648 = x_646;
}
lean_ctor_set(x_648, 0, x_647);
if (lean_is_scalar(x_634)) {
 x_649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_649 = x_634;
}
lean_ctor_set(x_649, 0, x_648);
lean_ctor_set(x_649, 1, x_633);
return x_649;
}
else
{
uint8_t x_650; 
x_650 = lean_name_eq(x_606, x_616);
lean_dec(x_606);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_651 = x_1;
} else {
 lean_dec_ref(x_1);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_652 = lean_alloc_ctor(0, 4, 0);
} else {
 x_652 = x_608;
}
lean_ctor_set(x_652, 0, x_604);
lean_ctor_set(x_652, 1, x_623);
lean_ctor_set(x_652, 2, x_616);
lean_ctor_set(x_652, 3, x_632);
if (lean_is_scalar(x_651)) {
 x_653 = lean_alloc_ctor(4, 1, 0);
} else {
 x_653 = x_651;
}
lean_ctor_set(x_653, 0, x_652);
if (lean_is_scalar(x_634)) {
 x_654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_654 = x_634;
}
lean_ctor_set(x_654, 0, x_653);
lean_ctor_set(x_654, 1, x_633);
return x_654;
}
else
{
lean_object* x_655; 
lean_dec(x_632);
lean_dec(x_623);
lean_dec(x_616);
lean_dec(x_608);
lean_dec(x_604);
if (lean_is_scalar(x_634)) {
 x_655 = lean_alloc_ctor(0, 2, 0);
} else {
 x_655 = x_634;
}
lean_ctor_set(x_655, 0, x_1);
lean_ctor_set(x_655, 1, x_633);
return x_655;
}
}
}
}
block_668:
{
lean_object* x_659; uint8_t x_660; 
lean_dec(x_658);
x_659 = lean_unsigned_to_nat(0u);
x_660 = lean_nat_dec_lt(x_659, x_657);
lean_dec(x_657);
if (x_660 == 0)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_632);
x_661 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4;
x_662 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_661);
x_663 = l_Lean_Compiler_LCNF_AltCore_getCode(x_662);
lean_dec(x_662);
if (lean_is_scalar(x_630)) {
 x_664 = lean_alloc_ctor(0, 2, 0);
} else {
 x_664 = x_630;
}
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_633);
return x_664;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_array_fget(x_632, x_659);
lean_dec(x_632);
x_666 = l_Lean_Compiler_LCNF_AltCore_getCode(x_665);
lean_dec(x_665);
if (lean_is_scalar(x_630)) {
 x_667 = lean_alloc_ctor(0, 2, 0);
} else {
 x_667 = x_630;
}
lean_ctor_set(x_667, 0, x_666);
lean_ctor_set(x_667, 1, x_633);
return x_667;
}
}
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec(x_630);
lean_dec(x_623);
lean_dec(x_616);
lean_dec(x_608);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_1);
x_680 = lean_ctor_get(x_631, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_631, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_682 = x_631;
} else {
 lean_dec_ref(x_631);
 x_682 = lean_box(0);
}
if (lean_is_scalar(x_682)) {
 x_683 = lean_alloc_ctor(1, 2, 0);
} else {
 x_683 = x_682;
}
lean_ctor_set(x_683, 0, x_680);
lean_ctor_set(x_683, 1, x_681);
return x_683;
}
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
lean_dec(x_623);
lean_dec(x_616);
lean_dec(x_608);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_684 = lean_ctor_get(x_627, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_627, 1);
lean_inc(x_685);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_686 = x_627;
} else {
 lean_dec_ref(x_627);
 x_686 = lean_box(0);
}
if (lean_is_scalar(x_686)) {
 x_687 = lean_alloc_ctor(1, 2, 0);
} else {
 x_687 = x_686;
}
lean_ctor_set(x_687, 0, x_684);
lean_ctor_set(x_687, 1, x_685);
return x_687;
}
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
lean_dec(x_600);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_688 = lean_ctor_get(x_601, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_689 = x_601;
} else {
 lean_dec_ref(x_601);
 x_689 = lean_box(0);
}
x_690 = lean_ctor_get(x_602, 0);
lean_inc(x_690);
lean_dec(x_602);
if (lean_is_scalar(x_689)) {
 x_691 = lean_alloc_ctor(0, 2, 0);
} else {
 x_691 = x_689;
}
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_688);
return x_691;
}
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_600);
lean_dec(x_400);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_692 = lean_ctor_get(x_601, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_601, 1);
lean_inc(x_693);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_694 = x_601;
} else {
 lean_dec_ref(x_601);
 x_694 = lean_box(0);
}
if (lean_is_scalar(x_694)) {
 x_695 = lean_alloc_ctor(1, 2, 0);
} else {
 x_695 = x_694;
}
lean_ctor_set(x_695, 0, x_692);
lean_ctor_set(x_695, 1, x_693);
return x_695;
}
}
case 5:
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; uint8_t x_709; 
x_696 = lean_ctor_get(x_401, 1);
lean_inc(x_696);
lean_dec(x_401);
x_697 = lean_ctor_get(x_1, 0);
lean_inc(x_697);
x_698 = lean_st_ref_get(x_7, x_696);
x_699 = lean_ctor_get(x_698, 1);
lean_inc(x_699);
lean_dec(x_698);
x_700 = lean_st_ref_get(x_3, x_699);
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec(x_700);
x_703 = lean_ctor_get(x_701, 0);
lean_inc(x_703);
lean_dec(x_701);
x_704 = 0;
lean_inc(x_697);
x_705 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_703, x_697, x_704);
lean_inc(x_705);
x_706 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_705, x_2, x_3, x_4, x_5, x_400, x_7, x_702);
lean_dec(x_7);
lean_dec(x_400);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_707 = lean_ctor_get(x_706, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_706)) {
 lean_ctor_release(x_706, 0);
 lean_ctor_release(x_706, 1);
 x_708 = x_706;
} else {
 lean_dec_ref(x_706);
 x_708 = lean_box(0);
}
x_709 = lean_name_eq(x_697, x_705);
lean_dec(x_697);
if (x_709 == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_710 = x_1;
} else {
 lean_dec_ref(x_1);
 x_710 = lean_box(0);
}
if (lean_is_scalar(x_710)) {
 x_711 = lean_alloc_ctor(5, 1, 0);
} else {
 x_711 = x_710;
}
lean_ctor_set(x_711, 0, x_705);
if (lean_is_scalar(x_708)) {
 x_712 = lean_alloc_ctor(0, 2, 0);
} else {
 x_712 = x_708;
}
lean_ctor_set(x_712, 0, x_711);
lean_ctor_set(x_712, 1, x_707);
return x_712;
}
else
{
lean_object* x_713; 
lean_dec(x_705);
if (lean_is_scalar(x_708)) {
 x_713 = lean_alloc_ctor(0, 2, 0);
} else {
 x_713 = x_708;
}
lean_ctor_set(x_713, 0, x_1);
lean_ctor_set(x_713, 1, x_707);
return x_713;
}
}
default: 
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; uint8_t x_723; lean_object* x_724; size_t x_725; size_t x_726; uint8_t x_727; 
lean_dec(x_400);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_714 = lean_ctor_get(x_401, 1);
lean_inc(x_714);
lean_dec(x_401);
x_715 = lean_ctor_get(x_1, 0);
lean_inc(x_715);
x_716 = lean_st_ref_get(x_7, x_714);
lean_dec(x_7);
x_717 = lean_ctor_get(x_716, 1);
lean_inc(x_717);
lean_dec(x_716);
x_718 = lean_st_ref_get(x_3, x_717);
lean_dec(x_3);
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
if (lean_is_exclusive(x_718)) {
 lean_ctor_release(x_718, 0);
 lean_ctor_release(x_718, 1);
 x_721 = x_718;
} else {
 lean_dec_ref(x_718);
 x_721 = lean_box(0);
}
x_722 = lean_ctor_get(x_719, 0);
lean_inc(x_722);
lean_dec(x_719);
x_723 = 0;
lean_inc(x_715);
x_724 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_722, x_723, x_715);
x_725 = lean_ptr_addr(x_715);
lean_dec(x_715);
x_726 = lean_ptr_addr(x_724);
x_727 = lean_usize_dec_eq(x_725, x_726);
if (x_727 == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_728 = x_1;
} else {
 lean_dec_ref(x_1);
 x_728 = lean_box(0);
}
if (lean_is_scalar(x_728)) {
 x_729 = lean_alloc_ctor(6, 1, 0);
} else {
 x_729 = x_728;
}
lean_ctor_set(x_729, 0, x_724);
if (lean_is_scalar(x_721)) {
 x_730 = lean_alloc_ctor(0, 2, 0);
} else {
 x_730 = x_721;
}
lean_ctor_set(x_730, 0, x_729);
lean_ctor_set(x_730, 1, x_720);
return x_730;
}
else
{
lean_object* x_731; 
lean_dec(x_724);
if (lean_is_scalar(x_721)) {
 x_731 = lean_alloc_ctor(0, 2, 0);
} else {
 x_731 = x_721;
}
lean_ctor_set(x_731, 0, x_1);
lean_ctor_set(x_731, 1, x_720);
return x_731;
}
}
}
}
}
else
{
lean_object* x_732; 
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
lean_dec(x_9);
lean_dec(x_1);
x_732 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_732;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_24; 
x_14 = lean_array_uget(x_1, x_3);
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 2);
lean_inc(x_29);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_14);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_4);
x_15 = x_31;
x_16 = x_11;
goto block_23;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_25, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = lean_array_fget(x_27, x_28);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_28, x_37);
lean_dec(x_28);
lean_ctor_set(x_25, 1, x_38);
x_39 = l_Lean_Expr_isFVar(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_41 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_36, x_40, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_array_push(x_26, x_44);
x_46 = lean_ctor_get(x_14, 0);
lean_inc(x_46);
lean_dec(x_14);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_46, x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_ctor_set(x_4, 1, x_45);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_4);
x_15 = x_50;
x_16 = x_49;
goto block_23;
}
else
{
uint8_t x_51; 
lean_dec(x_45);
lean_dec(x_25);
lean_free_object(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_25);
lean_free_object(x_4);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
return x_41;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_41, 0);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_41);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_14, 0);
lean_inc(x_59);
lean_dec(x_14);
x_60 = l_Lean_Expr_fvarId_x21(x_36);
x_61 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_59, x_60, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_4);
x_15 = x_63;
x_16 = x_62;
goto block_23;
}
else
{
uint8_t x_64; 
lean_dec(x_25);
lean_free_object(x_4);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
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
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_25);
x_68 = lean_array_fget(x_27, x_28);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_28, x_69);
lean_dec(x_28);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_27);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_29);
x_72 = l_Lean_Expr_isFVar(x_68);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_74 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_68, x_73, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_75);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_75);
x_78 = lean_array_push(x_26, x_77);
x_79 = lean_ctor_get(x_14, 0);
lean_inc(x_79);
lean_dec(x_14);
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
lean_dec(x_75);
x_81 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_79, x_80, x_5, x_6, x_7, x_8, x_9, x_10, x_76);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
lean_ctor_set(x_4, 1, x_78);
lean_ctor_set(x_4, 0, x_71);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_4);
x_15 = x_83;
x_16 = x_82;
goto block_23;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_78);
lean_dec(x_71);
lean_free_object(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_71);
lean_free_object(x_4);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_88 = lean_ctor_get(x_74, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_90 = x_74;
} else {
 lean_dec_ref(x_74);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_14, 0);
lean_inc(x_92);
lean_dec(x_14);
x_93 = l_Lean_Expr_fvarId_x21(x_68);
x_94 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_92, x_93, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
lean_ctor_set(x_4, 0, x_71);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_4);
x_15 = x_96;
x_16 = x_95;
goto block_23;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_71);
lean_free_object(x_4);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_99 = x_94;
} else {
 lean_dec_ref(x_94);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_4, 0);
x_102 = lean_ctor_get(x_4, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_4);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_101, 2);
lean_inc(x_105);
x_106 = lean_nat_dec_lt(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_14);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_101);
lean_ctor_set(x_107, 1, x_102);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_15 = x_108;
x_16 = x_11;
goto block_23;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 x_109 = x_101;
} else {
 lean_dec_ref(x_101);
 x_109 = lean_box(0);
}
x_110 = lean_array_fget(x_103, x_104);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_add(x_104, x_111);
lean_dec(x_104);
if (lean_is_scalar(x_109)) {
 x_113 = lean_alloc_ctor(0, 3, 0);
} else {
 x_113 = x_109;
}
lean_ctor_set(x_113, 0, x_103);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_105);
x_114 = l_Lean_Expr_isFVar(x_110);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_116 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_110, x_115, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_117);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_117);
x_120 = lean_array_push(x_102, x_119);
x_121 = lean_ctor_get(x_14, 0);
lean_inc(x_121);
lean_dec(x_14);
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
lean_dec(x_117);
x_123 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_121, x_122, x_5, x_6, x_7, x_8, x_9, x_10, x_118);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_113);
lean_ctor_set(x_125, 1, x_120);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_15 = x_126;
x_16 = x_124;
goto block_23;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_120);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_127 = lean_ctor_get(x_123, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_129 = x_123;
} else {
 lean_dec_ref(x_123);
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
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_113);
lean_dec(x_102);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_131 = lean_ctor_get(x_116, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_116, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_133 = x_116;
} else {
 lean_dec_ref(x_116);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_14, 0);
lean_inc(x_135);
lean_dec(x_14);
x_136 = l_Lean_Expr_fvarId_x21(x_110);
x_137 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_135, x_136, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_113);
lean_ctor_set(x_139, 1, x_102);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_15 = x_140;
x_16 = x_138;
goto block_23;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_113);
lean_dec(x_102);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_141 = lean_ctor_get(x_137, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_143 = x_137;
} else {
 lean_dec_ref(x_137);
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
}
}
block_23:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_4 = x_19;
x_11 = x_16;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_15, x_9, x_16);
x_18 = l_Lean_Expr_fvar___override(x_17);
x_19 = l_Lean_Compiler_LCNF_Simp_findCtor(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_7, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = l_Lean_Expr_constructorApp_x3f(x_26, x_20, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_box(0);
lean_ctor_set(x_22, 0, x_29);
return x_22;
}
else
{
uint8_t x_30; 
lean_free_object(x_22);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_Compiler_LCNF_eraseCode(x_39, x_4, x_5, x_6, x_7, x_25);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_37, 2);
lean_inc(x_45);
lean_dec(x_37);
x_46 = lean_ctor_get(x_32, 3);
lean_inc(x_46);
lean_dec(x_32);
x_47 = lean_array_get_size(x_33);
x_48 = l_Array_toSubarray___rarg(x_33, x_46, x_47);
x_49 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_get_size(x_44);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_54 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_44, x_52, x_53, x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_58 = l_Lean_Compiler_LCNF_Simp_simp(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Compiler_LCNF_eraseParams(x_44, x_4, x_5, x_6, x_7, x_60);
lean_dec(x_44);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_57, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_62);
lean_dec(x_57);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_ctor_set(x_28, 0, x_65);
lean_ctor_set(x_63, 0, x_28);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
lean_ctor_set(x_28, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_28);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_57);
lean_dec(x_44);
lean_free_object(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_58);
if (x_69 == 0)
{
return x_58;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_58, 0);
x_71 = lean_ctor_get(x_58, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_58);
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
lean_dec(x_45);
lean_dec(x_44);
lean_free_object(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_54);
if (x_73 == 0)
{
return x_54;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_54, 0);
x_75 = lean_ctor_get(x_54, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_54);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_33);
lean_dec(x_32);
x_77 = lean_ctor_get(x_42, 1);
lean_inc(x_77);
lean_dec(x_42);
x_78 = lean_ctor_get(x_37, 0);
lean_inc(x_78);
lean_dec(x_37);
x_79 = l_Lean_Compiler_LCNF_Simp_simp(x_78, x_2, x_3, x_4, x_5, x_6, x_7, x_77);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_ctor_set(x_28, 0, x_81);
lean_ctor_set(x_79, 0, x_28);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_79, 0);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_79);
lean_ctor_set(x_28, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_28);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_free_object(x_28);
x_85 = !lean_is_exclusive(x_79);
if (x_85 == 0)
{
return x_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_79, 0);
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_79);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_89 = lean_ctor_get(x_28, 0);
lean_inc(x_89);
lean_dec(x_28);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Lean_Compiler_LCNF_eraseCode(x_97, x_4, x_5, x_6, x_7, x_25);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_99);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; lean_object* x_112; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_95, 2);
lean_inc(x_103);
lean_dec(x_95);
x_104 = lean_ctor_get(x_90, 3);
lean_inc(x_104);
lean_dec(x_90);
x_105 = lean_array_get_size(x_91);
x_106 = l_Array_toSubarray___rarg(x_91, x_104, x_105);
x_107 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_array_get_size(x_102);
x_110 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_111 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_112 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_102, x_110, x_111, x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_101);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_116 = l_Lean_Compiler_LCNF_Simp_simp(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Compiler_LCNF_eraseParams(x_102, x_4, x_5, x_6, x_7, x_118);
lean_dec(x_102);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_115, x_117, x_2, x_3, x_4, x_5, x_6, x_7, x_120);
lean_dec(x_115);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_122);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_115);
lean_dec(x_102);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_ctor_get(x_116, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_116, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_129 = x_116;
} else {
 lean_dec_ref(x_116);
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
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_131 = lean_ctor_get(x_112, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_112, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_133 = x_112;
} else {
 lean_dec_ref(x_112);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_91);
lean_dec(x_90);
x_135 = lean_ctor_get(x_100, 1);
lean_inc(x_135);
lean_dec(x_100);
x_136 = lean_ctor_get(x_95, 0);
lean_inc(x_136);
lean_dec(x_95);
x_137 = l_Lean_Compiler_LCNF_Simp_simp(x_136, x_2, x_3, x_4, x_5, x_6, x_7, x_135);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_138);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_137, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_137, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_145 = x_137;
} else {
 lean_dec_ref(x_137);
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
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_22, 0);
x_148 = lean_ctor_get(x_22, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_22);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec(x_147);
x_150 = 1;
x_151 = l_Lean_Expr_constructorApp_x3f(x_149, x_20, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_148);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_155 = x_151;
} else {
 lean_dec_ref(x_151);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec(x_158);
x_160 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = l_Lean_Compiler_LCNF_eraseCode(x_163, x_4, x_5, x_6, x_7, x_148);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_165);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; size_t x_176; size_t x_177; lean_object* x_178; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_ctor_get(x_161, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_161, 2);
lean_inc(x_169);
lean_dec(x_161);
x_170 = lean_ctor_get(x_156, 3);
lean_inc(x_170);
lean_dec(x_156);
x_171 = lean_array_get_size(x_157);
x_172 = l_Array_toSubarray___rarg(x_157, x_170, x_171);
x_173 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_array_get_size(x_168);
x_176 = lean_usize_of_nat(x_175);
lean_dec(x_175);
x_177 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_178 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_168, x_176, x_177, x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_167);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_182 = l_Lean_Compiler_LCNF_Simp_simp(x_169, x_2, x_3, x_4, x_5, x_6, x_7, x_180);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Lean_Compiler_LCNF_eraseParams(x_168, x_4, x_5, x_6, x_7, x_184);
lean_dec(x_168);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_181, x_183, x_2, x_3, x_4, x_5, x_6, x_7, x_186);
lean_dec(x_181);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_155;
}
lean_ctor_set(x_191, 0, x_188);
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_189);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_181);
lean_dec(x_168);
lean_dec(x_155);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_193 = lean_ctor_get(x_182, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_182, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_195 = x_182;
} else {
 lean_dec_ref(x_182);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_155);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_197 = lean_ctor_get(x_178, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_178, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_199 = x_178;
} else {
 lean_dec_ref(x_178);
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
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_157);
lean_dec(x_156);
x_201 = lean_ctor_get(x_166, 1);
lean_inc(x_201);
lean_dec(x_166);
x_202 = lean_ctor_get(x_161, 0);
lean_inc(x_202);
lean_dec(x_161);
x_203 = l_Lean_Compiler_LCNF_Simp_simp(x_202, x_2, x_3, x_4, x_5, x_6, x_7, x_201);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_206 = x_203;
} else {
 lean_dec_ref(x_203);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_155;
}
lean_ctor_set(x_207, 0, x_204);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_155);
x_209 = lean_ctor_get(x_203, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_203, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_211 = x_203;
} else {
 lean_dec_ref(x_203);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_16, x_1, x_10);
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(x_2, x_17, x_5, x_6, x_7, x_8, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_15 = lean_apply_8(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ptr_addr(x_14);
lean_dec(x_14);
x_19 = lean_ptr_addr(x_16);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
x_23 = lean_array_fset(x_3, x_2, x_16);
lean_dec(x_2);
x_2 = x_22;
x_3 = x_23;
x_10 = x_17;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_16);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_2 = x_26;
x_10 = x_17;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(x_2, x_10, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed), 9, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_15, x_16, x_9);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(x_16, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_1, 4);
lean_inc(x_22);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Compiler_LCNF_Simp_simp(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_17, x_20, x_24, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
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
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simp___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2);
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3);
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4);
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
