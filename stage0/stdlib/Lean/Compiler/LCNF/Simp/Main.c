// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Main
// Imports: Init Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.ElimDead Lean.Compiler.LCNF.AlphaEqv Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.Simp.FunDeclInfo Lean.Compiler.LCNF.Simp.InlineCandidate Lean.Compiler.LCNF.Simp.InlineProj Lean.Compiler.LCNF.Simp.Used Lean.Compiler.LCNF.Simp.DefaultAlt Lean.Compiler.LCNF.Simp.SimpValue
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2;
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__8;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__7;
uint8_t l_Lean_Compiler_LCNF_hasLocalInst(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4;
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__5;
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__9;
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__5;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__6;
lean_object* l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__10;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3;
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__4;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__7;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_panic___at_Lean_Compiler_LCNF_CasesCore_extractAlt_x21___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_CallerInfo_mkPanicMessage(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__6;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.PanicAux", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(47u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2;
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__5;
x_3 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__7;
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__8;
x_3 = l_CallerInfo_mkPanicMessage(x_1, x_2);
return x_3;
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
x_14 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__9;
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_19 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(x_13, x_17, x_18, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_30 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_24, x_27, x_29, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
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
x_56 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_49, x_53, x_55, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
if (x_10 == 0)
{
lean_object* x_318; 
x_318 = lean_box(0);
x_11 = x_318;
x_12 = x_8;
goto block_317;
}
else
{
lean_object* x_319; 
x_319 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_11 = x_319;
x_12 = x_8;
goto block_317;
}
block_317:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_33 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_17, x_4, x_6, x_7, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_68 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_53, x_66, x_67, x_4, x_5, x_6, x_7, x_63);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_st_ref_get(x_7, x_70);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_st_ref_take(x_3, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = l_Lean_Expr_fvar___override(x_72);
x_80 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_78, x_71, x_79);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 2);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_76, sizeof(void*)*6);
x_84 = lean_ctor_get(x_76, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_76, 5);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_84);
lean_ctor_set(x_87, 4, x_85);
lean_ctor_set(x_87, 5, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*6, x_83);
x_88 = lean_st_ref_set(x_3, x_87, x_77);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_89);
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
lean_ctor_set(x_34, 0, x_69);
lean_ctor_set(x_90, 0, x_34);
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
lean_ctor_set(x_34, 0, x_69);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_34);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_free_object(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_68);
if (x_95 == 0)
{
return x_68;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_68, 0);
x_97 = lean_ctor_get(x_68, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_68);
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
lean_dec(x_53);
lean_free_object(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_61);
if (x_99 == 0)
{
return x_61;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_61, 0);
x_101 = lean_ctor_get(x_61, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_61);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_103 = lean_ctor_get(x_34, 0);
lean_inc(x_103);
lean_dec(x_34);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_15, x_104);
x_106 = l_Lean_Compiler_LCNF_Decl_getArity(x_103);
lean_dec(x_103);
x_107 = lean_nat_dec_lt(x_105, x_106);
lean_dec(x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_108 = lean_box(0);
lean_ctor_set(x_33, 0, x_108);
return x_33;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_free_object(x_33);
x_109 = lean_ctor_get(x_1, 2);
lean_inc(x_109);
x_110 = l_Lean_Compiler_LCNF_mkNewParams(x_109, x_4, x_5, x_6, x_7, x_42);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_array_get_size(x_111);
x_114 = lean_usize_of_nat(x_113);
lean_dec(x_113);
x_115 = 0;
lean_inc(x_111);
x_116 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_114, x_115, x_111);
x_117 = l_Lean_mkAppN(x_15, x_116);
x_118 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_119 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_117, x_118, x_4, x_5, x_6, x_7, x_112);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_126 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_111, x_124, x_125, x_4, x_5, x_6, x_7, x_121);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_1, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
x_131 = lean_st_ref_get(x_7, x_128);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_st_ref_take(x_3, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = l_Lean_Expr_fvar___override(x_130);
x_138 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_136, x_129, x_137);
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_134, 2);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_134, sizeof(void*)*6);
x_142 = lean_ctor_get(x_134, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_134, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_134, 5);
lean_inc(x_144);
lean_dec(x_134);
x_145 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_145, 0, x_138);
lean_ctor_set(x_145, 1, x_139);
lean_ctor_set(x_145, 2, x_140);
lean_ctor_set(x_145, 3, x_142);
lean_ctor_set(x_145, 4, x_143);
lean_ctor_set(x_145, 5, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*6, x_141);
x_146 = lean_st_ref_set(x_3, x_145, x_135);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_148 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_127);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_153 = lean_ctor_get(x_126, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_126, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_155 = x_126;
} else {
 lean_dec_ref(x_126);
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
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_157 = lean_ctor_get(x_119, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_119, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_159 = x_119;
} else {
 lean_dec_ref(x_119);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_161 = lean_ctor_get(x_33, 1);
lean_inc(x_161);
lean_dec(x_33);
x_162 = lean_ctor_get(x_34, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_163 = x_34;
} else {
 lean_dec_ref(x_34);
 x_163 = lean_box(0);
}
x_164 = lean_unsigned_to_nat(0u);
x_165 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_15, x_164);
x_166 = l_Lean_Compiler_LCNF_Decl_getArity(x_162);
lean_dec(x_162);
x_167 = lean_nat_dec_lt(x_165, x_166);
lean_dec(x_166);
lean_dec(x_165);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_163);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_168 = lean_box(0);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_161);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; size_t x_175; size_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_170 = lean_ctor_get(x_1, 2);
lean_inc(x_170);
x_171 = l_Lean_Compiler_LCNF_mkNewParams(x_170, x_4, x_5, x_6, x_7, x_161);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_array_get_size(x_172);
x_175 = lean_usize_of_nat(x_174);
lean_dec(x_174);
x_176 = 0;
lean_inc(x_172);
x_177 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_175, x_176, x_172);
x_178 = l_Lean_mkAppN(x_15, x_177);
x_179 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_180 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_178, x_179, x_4, x_5, x_6, x_7, x_173);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
x_184 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_184, 0, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_181);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_187 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_172, x_185, x_186, x_4, x_5, x_6, x_7, x_182);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_1, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
x_192 = lean_st_ref_get(x_7, x_189);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_st_ref_take(x_3, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
x_198 = l_Lean_Expr_fvar___override(x_191);
x_199 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_197, x_190, x_198);
x_200 = lean_ctor_get(x_195, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_195, 2);
lean_inc(x_201);
x_202 = lean_ctor_get_uint8(x_195, sizeof(void*)*6);
x_203 = lean_ctor_get(x_195, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_195, 4);
lean_inc(x_204);
x_205 = lean_ctor_get(x_195, 5);
lean_inc(x_205);
lean_dec(x_195);
x_206 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_206, 0, x_199);
lean_ctor_set(x_206, 1, x_200);
lean_ctor_set(x_206, 2, x_201);
lean_ctor_set(x_206, 3, x_203);
lean_ctor_set(x_206, 4, x_204);
lean_ctor_set(x_206, 5, x_205);
lean_ctor_set_uint8(x_206, sizeof(void*)*6, x_202);
x_207 = lean_st_ref_set(x_3, x_206, x_196);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_208);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_212 = lean_alloc_ctor(1, 1, 0);
} else {
 x_212 = x_163;
}
lean_ctor_set(x_212, 0, x_188);
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_211;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_210);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_163);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_214 = lean_ctor_get(x_187, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_187, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_216 = x_187;
} else {
 lean_dec_ref(x_187);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_172);
lean_dec(x_163);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_218 = lean_ctor_get(x_180, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_180, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_220 = x_180;
} else {
 lean_dec_ref(x_180);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_29);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_29, 0);
lean_dec(x_223);
x_224 = lean_box(0);
lean_ctor_set(x_29, 0, x_224);
return x_29;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_29, 1);
lean_inc(x_225);
lean_dec(x_29);
x_226 = lean_box(0);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_18, 0);
x_229 = lean_ctor_get(x_18, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_18);
x_230 = lean_ctor_get(x_228, 0);
lean_inc(x_230);
lean_dec(x_228);
lean_inc(x_17);
x_231 = lean_environment_find(x_230, x_17);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_232 = lean_box(0);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_229);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = lean_ctor_get(x_231, 0);
lean_inc(x_234);
lean_dec(x_231);
x_235 = l_Lean_ConstantInfo_type(x_234);
lean_dec(x_234);
x_236 = l_Lean_Compiler_LCNF_hasLocalInst(x_235);
lean_dec(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_237 = lean_box(0);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_229);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
lean_inc(x_17);
x_239 = l_Lean_Meta_isInstance(x_17, x_6, x_7, x_229);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_unbox(x_240);
lean_dec(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
lean_dec(x_239);
x_243 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_17, x_4, x_6, x_7, x_242);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
x_247 = lean_box(0);
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
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_249 = lean_ctor_get(x_243, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_250 = x_243;
} else {
 lean_dec_ref(x_243);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_244, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_252 = x_244;
} else {
 lean_dec_ref(x_244);
 x_252 = lean_box(0);
}
x_253 = lean_unsigned_to_nat(0u);
x_254 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_15, x_253);
x_255 = l_Lean_Compiler_LCNF_Decl_getArity(x_251);
lean_dec(x_251);
x_256 = lean_nat_dec_lt(x_254, x_255);
lean_dec(x_255);
lean_dec(x_254);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_252);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_257 = lean_box(0);
if (lean_is_scalar(x_250)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_250;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_249);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; size_t x_264; size_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_250);
x_259 = lean_ctor_get(x_1, 2);
lean_inc(x_259);
x_260 = l_Lean_Compiler_LCNF_mkNewParams(x_259, x_4, x_5, x_6, x_7, x_249);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_array_get_size(x_261);
x_264 = lean_usize_of_nat(x_263);
lean_dec(x_263);
x_265 = 0;
lean_inc(x_261);
x_266 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_264, x_265, x_261);
x_267 = l_Lean_mkAppN(x_15, x_266);
x_268 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_269 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_267, x_268, x_4, x_5, x_6, x_7, x_262);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
x_273 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_273, 0, x_272);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_270);
lean_ctor_set(x_274, 1, x_273);
x_275 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_276 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_261, x_274, x_275, x_4, x_5, x_6, x_7, x_271);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_ctor_get(x_1, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_277, 0);
lean_inc(x_280);
x_281 = lean_st_ref_get(x_7, x_278);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec(x_281);
x_283 = lean_st_ref_take(x_3, x_282);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
x_287 = l_Lean_Expr_fvar___override(x_280);
x_288 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_286, x_279, x_287);
x_289 = lean_ctor_get(x_284, 1);
lean_inc(x_289);
x_290 = lean_ctor_get(x_284, 2);
lean_inc(x_290);
x_291 = lean_ctor_get_uint8(x_284, sizeof(void*)*6);
x_292 = lean_ctor_get(x_284, 3);
lean_inc(x_292);
x_293 = lean_ctor_get(x_284, 4);
lean_inc(x_293);
x_294 = lean_ctor_get(x_284, 5);
lean_inc(x_294);
lean_dec(x_284);
x_295 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_295, 0, x_288);
lean_ctor_set(x_295, 1, x_289);
lean_ctor_set(x_295, 2, x_290);
lean_ctor_set(x_295, 3, x_292);
lean_ctor_set(x_295, 4, x_293);
lean_ctor_set(x_295, 5, x_294);
lean_ctor_set_uint8(x_295, sizeof(void*)*6, x_291);
x_296 = lean_st_ref_set(x_3, x_295, x_285);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
x_298 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_297);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_300 = x_298;
} else {
 lean_dec_ref(x_298);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_252;
}
lean_ctor_set(x_301, 0, x_277);
if (lean_is_scalar(x_300)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_300;
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_299);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_252);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_303 = lean_ctor_get(x_276, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_276, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_305 = x_276;
} else {
 lean_dec_ref(x_276);
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
lean_dec(x_261);
lean_dec(x_252);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_307 = lean_ctor_get(x_269, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_269, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_309 = x_269;
} else {
 lean_dec_ref(x_269);
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
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_311 = lean_ctor_get(x_239, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_312 = x_239;
} else {
 lean_dec_ref(x_239);
 x_312 = lean_box(0);
}
x_313 = lean_box(0);
if (lean_is_scalar(x_312)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_312;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_311);
return x_314;
}
}
}
}
}
else
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_315 = lean_box(0);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_12);
return x_316;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_Compiler_LCNF_Simp_isReturnOf(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1;
x_12 = lean_array_push(x_11, x_1);
x_13 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_3);
x_17 = lean_st_ref_get(x_12, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_2, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = l_Lean_Expr_fvar___override(x_8);
x_24 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_22, x_5, x_23);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_20, 2);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_20, sizeof(void*)*6);
x_28 = lean_ctor_get(x_20, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_20, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 5);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*6, x_27);
x_32 = lean_st_ref_set(x_2, x_31, x_21);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Compiler_LCNF_Simp_simp(x_6, x_1, x_2, x_9, x_10, x_11, x_12, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = l_Lean_Expr_fvar___override(x_8);
x_36 = lean_array_get_size(x_7);
x_37 = l_Array_toSubarray___rarg(x_7, x_3, x_36);
x_38 = l_Array_ofSubarray___rarg(x_37);
x_39 = l_Lean_mkAppN(x_35, x_38);
x_40 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_41 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_39, x_40, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_st_ref_get(x_12, x_43);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_take(x_2, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = l_Lean_Expr_fvar___override(x_44);
x_52 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_50, x_5, x_51);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 2);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_48, sizeof(void*)*6);
x_56 = lean_ctor_get(x_48, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_48, 5);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_53);
lean_ctor_set(x_59, 2, x_54);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_57);
lean_ctor_set(x_59, 5, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*6, x_55);
x_60 = lean_st_ref_set(x_2, x_59, x_49);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_6);
x_63 = l_Lean_Compiler_LCNF_Simp_simp(x_62, x_1, x_2, x_9, x_10, x_11, x_12, x_61);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_41);
if (x_64 == 0)
{
return x_41;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_41, 0);
x_66 = lean_ctor_get(x_41, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_41);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
lean_dec(x_19);
x_20 = lean_ctor_get(x_12, 3);
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
x_23 = lean_ctor_get(x_12, 2);
lean_inc(x_20);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_20);
x_25 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_26 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_25, x_24, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_136; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_136 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_box(0);
x_29 = x_137;
goto block_135;
}
else
{
uint8_t x_138; 
x_138 = lean_nat_dec_eq(x_7, x_6);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = lean_box(0);
x_29 = x_139;
goto block_135;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_140 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_28);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = l_Lean_Compiler_LCNF_Simp_simp(x_27, x_24, x_13, x_14, x_15, x_16, x_17, x_141);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_alloc_ctor(1, 1, 0);
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
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_146);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_142);
if (x_150 == 0)
{
return x_142;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_142, 0);
x_152 = lean_ctor_get(x_142, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_142);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
block_135:
{
lean_object* x_30; 
lean_dec(x_29);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_24);
x_30 = l_Lean_Compiler_LCNF_Simp_simp(x_27, x_24, x_13, x_14, x_15, x_16, x_17, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_31);
x_33 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_32);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_5, 2);
lean_inc(x_36);
lean_dec(x_5);
x_37 = l_Lean_mkAppN(x_36, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_38 = l_Lean_Compiler_LCNF_inferType(x_37, x_14, x_15, x_16, x_17, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Compiler_LCNF_mkAuxParam(x_39, x_25, x_14, x_15, x_16, x_17, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_10);
lean_dec(x_6);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_st_ref_get(x_17, x_43);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_st_ref_take(x_13, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = l_Lean_Expr_fvar___override(x_45);
x_53 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_51, x_8, x_52);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 2);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_49, sizeof(void*)*6);
x_57 = lean_ctor_get(x_49, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_49, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_49, 5);
lean_inc(x_59);
lean_dec(x_49);
x_60 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_54);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_57);
lean_ctor_set(x_60, 4, x_58);
lean_ctor_set(x_60, 5, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*6, x_56);
x_61 = lean_st_ref_set(x_13, x_60, x_50);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_24);
x_63 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_24, x_13, x_14, x_15, x_16, x_17, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_42, x_31, x_64, x_24, x_13, x_14, x_15, x_16, x_17, x_65);
lean_dec(x_13);
lean_dec(x_24);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_42);
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
return x_63;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 0);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_42, 0);
lean_inc(x_71);
x_72 = l_Lean_Expr_fvar___override(x_71);
x_73 = lean_array_get_size(x_10);
x_74 = l_Array_toSubarray___rarg(x_10, x_6, x_73);
x_75 = l_Array_ofSubarray___rarg(x_74);
x_76 = l_Lean_mkAppN(x_72, x_75);
x_77 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_78 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_76, x_77, x_14, x_15, x_16, x_17, x_43);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_st_ref_get(x_17, x_80);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_st_ref_take(x_13, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = l_Lean_Expr_fvar___override(x_81);
x_89 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_87, x_8, x_88);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 2);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_85, sizeof(void*)*6);
x_93 = lean_ctor_get(x_85, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 4);
lean_inc(x_94);
x_95 = lean_ctor_get(x_85, 5);
lean_inc(x_95);
lean_dec(x_85);
x_96 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_93);
lean_ctor_set(x_96, 4, x_94);
lean_ctor_set(x_96, 5, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*6, x_92);
x_97 = lean_st_ref_set(x_13, x_96, x_86);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_79);
lean_ctor_set(x_99, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_24);
x_100 = l_Lean_Compiler_LCNF_Simp_simp(x_99, x_24, x_13, x_14, x_15, x_16, x_17, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_42, x_31, x_101, x_24, x_13, x_14, x_15, x_16, x_17, x_102);
lean_dec(x_13);
lean_dec(x_24);
return x_103;
}
else
{
uint8_t x_104; 
lean_dec(x_42);
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_104 = !lean_is_exclusive(x_100);
if (x_104 == 0)
{
return x_100;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_100, 0);
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_100);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_42);
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_108 = !lean_is_exclusive(x_78);
if (x_108 == 0)
{
return x_78;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_78, 0);
x_110 = lean_ctor_get(x_78, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_78);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_112 = !lean_is_exclusive(x_38);
if (x_112 == 0)
{
return x_38;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_38, 0);
x_114 = lean_ctor_get(x_38, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_38);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_5);
lean_dec(x_4);
x_116 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_32);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_118, 0, x_24);
lean_closure_set(x_118, 1, x_13);
lean_closure_set(x_118, 2, x_6);
lean_closure_set(x_118, 3, x_7);
lean_closure_set(x_118, 4, x_8);
lean_closure_set(x_118, 5, x_9);
lean_closure_set(x_118, 6, x_10);
x_119 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_31, x_118, x_14, x_15, x_16, x_17, x_117);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_119, 0, x_122);
return x_119;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_119);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_123);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_119);
if (x_127 == 0)
{
return x_119;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_119, 0);
x_129 = lean_ctor_get(x_119, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_119);
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
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_131 = !lean_is_exclusive(x_30);
if (x_131 == 0)
{
return x_30;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_30, 0);
x_133 = lean_ctor_get(x_30, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_30);
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
uint8_t x_154; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_154 = !lean_is_exclusive(x_26);
if (x_154 == 0)
{
return x_26;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_26, 0);
x_156 = lean_ctor_get(x_26, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_26);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
case 1:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; 
lean_dec(x_19);
x_158 = lean_ctor_get(x_12, 3);
x_159 = lean_ctor_get(x_12, 0);
x_160 = lean_ctor_get(x_12, 1);
x_161 = lean_ctor_get(x_12, 2);
lean_inc(x_158);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
x_162 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
lean_ctor_set(x_162, 2, x_161);
lean_ctor_set(x_162, 3, x_158);
x_163 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_164 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_163, x_162, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_274; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_274 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_274 == 0)
{
lean_object* x_275; 
x_275 = lean_box(0);
x_167 = x_275;
goto block_273;
}
else
{
uint8_t x_276; 
x_276 = lean_nat_dec_eq(x_7, x_6);
if (x_276 == 0)
{
lean_object* x_277; 
x_277 = lean_box(0);
x_167 = x_277;
goto block_273;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_278 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_166);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_280 = l_Lean_Compiler_LCNF_Simp_simp(x_165, x_162, x_13, x_14, x_15, x_16, x_17, x_279);
if (lean_obj_tag(x_280) == 0)
{
uint8_t x_281; 
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_280, 0);
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_280, 0, x_283);
return x_280;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_ctor_get(x_280, 0);
x_285 = lean_ctor_get(x_280, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_280);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_284);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
else
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_280);
if (x_288 == 0)
{
return x_280;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_280, 0);
x_290 = lean_ctor_get(x_280, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_280);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
}
}
block_273:
{
lean_object* x_168; 
lean_dec(x_167);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_162);
x_168 = l_Lean_Compiler_LCNF_Simp_simp(x_165, x_162, x_13, x_14, x_15, x_16, x_17, x_166);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_169);
x_171 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_169);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_170);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_174 = lean_ctor_get(x_5, 2);
lean_inc(x_174);
lean_dec(x_5);
x_175 = l_Lean_mkAppN(x_174, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_176 = l_Lean_Compiler_LCNF_inferType(x_175, x_14, x_15, x_16, x_17, x_173);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = l_Lean_Compiler_LCNF_mkAuxParam(x_177, x_163, x_14, x_15, x_16, x_17, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_10);
lean_dec(x_6);
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
x_184 = lean_st_ref_get(x_17, x_181);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_st_ref_take(x_13, x_185);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = l_Lean_Expr_fvar___override(x_183);
x_191 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_189, x_8, x_190);
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_187, 2);
lean_inc(x_193);
x_194 = lean_ctor_get_uint8(x_187, sizeof(void*)*6);
x_195 = lean_ctor_get(x_187, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_187, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_187, 5);
lean_inc(x_197);
lean_dec(x_187);
x_198 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_198, 0, x_191);
lean_ctor_set(x_198, 1, x_192);
lean_ctor_set(x_198, 2, x_193);
lean_ctor_set(x_198, 3, x_195);
lean_ctor_set(x_198, 4, x_196);
lean_ctor_set(x_198, 5, x_197);
lean_ctor_set_uint8(x_198, sizeof(void*)*6, x_194);
x_199 = lean_st_ref_set(x_13, x_198, x_188);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_162);
x_201 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_162, x_13, x_14, x_15, x_16, x_17, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_180, x_169, x_202, x_162, x_13, x_14, x_15, x_16, x_17, x_203);
lean_dec(x_13);
lean_dec(x_162);
return x_204;
}
else
{
uint8_t x_205; 
lean_dec(x_180);
lean_dec(x_169);
lean_dec(x_162);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_205 = !lean_is_exclusive(x_201);
if (x_205 == 0)
{
return x_201;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_201, 0);
x_207 = lean_ctor_get(x_201, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_201);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_209 = lean_ctor_get(x_180, 0);
lean_inc(x_209);
x_210 = l_Lean_Expr_fvar___override(x_209);
x_211 = lean_array_get_size(x_10);
x_212 = l_Array_toSubarray___rarg(x_10, x_6, x_211);
x_213 = l_Array_ofSubarray___rarg(x_212);
x_214 = l_Lean_mkAppN(x_210, x_213);
x_215 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_216 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_214, x_215, x_14, x_15, x_16, x_17, x_181);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
x_220 = lean_st_ref_get(x_17, x_218);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_st_ref_take(x_13, x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_ctor_get(x_223, 0);
lean_inc(x_225);
x_226 = l_Lean_Expr_fvar___override(x_219);
x_227 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_225, x_8, x_226);
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_223, 2);
lean_inc(x_229);
x_230 = lean_ctor_get_uint8(x_223, sizeof(void*)*6);
x_231 = lean_ctor_get(x_223, 3);
lean_inc(x_231);
x_232 = lean_ctor_get(x_223, 4);
lean_inc(x_232);
x_233 = lean_ctor_get(x_223, 5);
lean_inc(x_233);
lean_dec(x_223);
x_234 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_234, 0, x_227);
lean_ctor_set(x_234, 1, x_228);
lean_ctor_set(x_234, 2, x_229);
lean_ctor_set(x_234, 3, x_231);
lean_ctor_set(x_234, 4, x_232);
lean_ctor_set(x_234, 5, x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*6, x_230);
x_235 = lean_st_ref_set(x_13, x_234, x_224);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_217);
lean_ctor_set(x_237, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_162);
x_238 = l_Lean_Compiler_LCNF_Simp_simp(x_237, x_162, x_13, x_14, x_15, x_16, x_17, x_236);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_180, x_169, x_239, x_162, x_13, x_14, x_15, x_16, x_17, x_240);
lean_dec(x_13);
lean_dec(x_162);
return x_241;
}
else
{
uint8_t x_242; 
lean_dec(x_180);
lean_dec(x_169);
lean_dec(x_162);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_242 = !lean_is_exclusive(x_238);
if (x_242 == 0)
{
return x_238;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_238, 0);
x_244 = lean_ctor_get(x_238, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_238);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_180);
lean_dec(x_169);
lean_dec(x_162);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_246 = !lean_is_exclusive(x_216);
if (x_246 == 0)
{
return x_216;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_216, 0);
x_248 = lean_ctor_get(x_216, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_216);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_169);
lean_dec(x_162);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_250 = !lean_is_exclusive(x_176);
if (x_250 == 0)
{
return x_176;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_176, 0);
x_252 = lean_ctor_get(x_176, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_176);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_5);
lean_dec(x_4);
x_254 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_170);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_256 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_256, 0, x_162);
lean_closure_set(x_256, 1, x_13);
lean_closure_set(x_256, 2, x_6);
lean_closure_set(x_256, 3, x_7);
lean_closure_set(x_256, 4, x_8);
lean_closure_set(x_256, 5, x_9);
lean_closure_set(x_256, 6, x_10);
x_257 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_169, x_256, x_14, x_15, x_16, x_17, x_255);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_257, 0);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_257, 0, x_260);
return x_257;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_257, 0);
x_262 = lean_ctor_get(x_257, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_257);
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_261);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
else
{
uint8_t x_265; 
x_265 = !lean_is_exclusive(x_257);
if (x_265 == 0)
{
return x_257;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_257, 0);
x_267 = lean_ctor_get(x_257, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_257);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
}
else
{
uint8_t x_269; 
lean_dec(x_162);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_269 = !lean_is_exclusive(x_168);
if (x_269 == 0)
{
return x_168;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_168, 0);
x_271 = lean_ctor_get(x_168, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_168);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_162);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_292 = !lean_is_exclusive(x_164);
if (x_292 == 0)
{
return x_164;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_164, 0);
x_294 = lean_ctor_get(x_164, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_164);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
case 2:
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; 
lean_dec(x_19);
x_296 = lean_ctor_get(x_12, 3);
x_297 = lean_ctor_get(x_12, 0);
x_298 = lean_ctor_get(x_12, 1);
x_299 = lean_ctor_get(x_12, 2);
lean_inc(x_296);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
x_300 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
lean_ctor_set(x_300, 2, x_299);
lean_ctor_set(x_300, 3, x_296);
x_301 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_302 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_301, x_300, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_412; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_412 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_412 == 0)
{
lean_object* x_413; 
x_413 = lean_box(0);
x_305 = x_413;
goto block_411;
}
else
{
uint8_t x_414; 
x_414 = lean_nat_dec_eq(x_7, x_6);
if (x_414 == 0)
{
lean_object* x_415; 
x_415 = lean_box(0);
x_305 = x_415;
goto block_411;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_416 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_304);
x_417 = lean_ctor_get(x_416, 1);
lean_inc(x_417);
lean_dec(x_416);
x_418 = l_Lean_Compiler_LCNF_Simp_simp(x_303, x_300, x_13, x_14, x_15, x_16, x_17, x_417);
if (lean_obj_tag(x_418) == 0)
{
uint8_t x_419; 
x_419 = !lean_is_exclusive(x_418);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_418, 0);
x_421 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_418, 0, x_421);
return x_418;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_422 = lean_ctor_get(x_418, 0);
x_423 = lean_ctor_get(x_418, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_418);
x_424 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_424, 0, x_422);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
else
{
uint8_t x_426; 
x_426 = !lean_is_exclusive(x_418);
if (x_426 == 0)
{
return x_418;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_418, 0);
x_428 = lean_ctor_get(x_418, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_418);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
}
block_411:
{
lean_object* x_306; 
lean_dec(x_305);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_300);
x_306 = l_Lean_Compiler_LCNF_Simp_simp(x_303, x_300, x_13, x_14, x_15, x_16, x_17, x_304);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
lean_inc(x_307);
x_309 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_307);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_310 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_308);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
x_312 = lean_ctor_get(x_5, 2);
lean_inc(x_312);
lean_dec(x_5);
x_313 = l_Lean_mkAppN(x_312, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_314 = l_Lean_Compiler_LCNF_inferType(x_313, x_14, x_15, x_16, x_17, x_311);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = l_Lean_Compiler_LCNF_mkAuxParam(x_315, x_301, x_14, x_15, x_16, x_17, x_316);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_10);
lean_dec(x_6);
x_321 = lean_ctor_get(x_318, 0);
lean_inc(x_321);
x_322 = lean_st_ref_get(x_17, x_319);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec(x_322);
x_324 = lean_st_ref_take(x_13, x_323);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_ctor_get(x_325, 0);
lean_inc(x_327);
x_328 = l_Lean_Expr_fvar___override(x_321);
x_329 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_327, x_8, x_328);
x_330 = lean_ctor_get(x_325, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_325, 2);
lean_inc(x_331);
x_332 = lean_ctor_get_uint8(x_325, sizeof(void*)*6);
x_333 = lean_ctor_get(x_325, 3);
lean_inc(x_333);
x_334 = lean_ctor_get(x_325, 4);
lean_inc(x_334);
x_335 = lean_ctor_get(x_325, 5);
lean_inc(x_335);
lean_dec(x_325);
x_336 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_336, 0, x_329);
lean_ctor_set(x_336, 1, x_330);
lean_ctor_set(x_336, 2, x_331);
lean_ctor_set(x_336, 3, x_333);
lean_ctor_set(x_336, 4, x_334);
lean_ctor_set(x_336, 5, x_335);
lean_ctor_set_uint8(x_336, sizeof(void*)*6, x_332);
x_337 = lean_st_ref_set(x_13, x_336, x_326);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
lean_dec(x_337);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_300);
x_339 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_300, x_13, x_14, x_15, x_16, x_17, x_338);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_342 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_318, x_307, x_340, x_300, x_13, x_14, x_15, x_16, x_17, x_341);
lean_dec(x_13);
lean_dec(x_300);
return x_342;
}
else
{
uint8_t x_343; 
lean_dec(x_318);
lean_dec(x_307);
lean_dec(x_300);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_343 = !lean_is_exclusive(x_339);
if (x_343 == 0)
{
return x_339;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_339, 0);
x_345 = lean_ctor_get(x_339, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_339);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_347 = lean_ctor_get(x_318, 0);
lean_inc(x_347);
x_348 = l_Lean_Expr_fvar___override(x_347);
x_349 = lean_array_get_size(x_10);
x_350 = l_Array_toSubarray___rarg(x_10, x_6, x_349);
x_351 = l_Array_ofSubarray___rarg(x_350);
x_352 = l_Lean_mkAppN(x_348, x_351);
x_353 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_354 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_352, x_353, x_14, x_15, x_16, x_17, x_319);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
x_357 = lean_ctor_get(x_355, 0);
lean_inc(x_357);
x_358 = lean_st_ref_get(x_17, x_356);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
lean_dec(x_358);
x_360 = lean_st_ref_take(x_13, x_359);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_ctor_get(x_361, 0);
lean_inc(x_363);
x_364 = l_Lean_Expr_fvar___override(x_357);
x_365 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_363, x_8, x_364);
x_366 = lean_ctor_get(x_361, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_361, 2);
lean_inc(x_367);
x_368 = lean_ctor_get_uint8(x_361, sizeof(void*)*6);
x_369 = lean_ctor_get(x_361, 3);
lean_inc(x_369);
x_370 = lean_ctor_get(x_361, 4);
lean_inc(x_370);
x_371 = lean_ctor_get(x_361, 5);
lean_inc(x_371);
lean_dec(x_361);
x_372 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_366);
lean_ctor_set(x_372, 2, x_367);
lean_ctor_set(x_372, 3, x_369);
lean_ctor_set(x_372, 4, x_370);
lean_ctor_set(x_372, 5, x_371);
lean_ctor_set_uint8(x_372, sizeof(void*)*6, x_368);
x_373 = lean_st_ref_set(x_13, x_372, x_362);
x_374 = lean_ctor_get(x_373, 1);
lean_inc(x_374);
lean_dec(x_373);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_355);
lean_ctor_set(x_375, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_300);
x_376 = l_Lean_Compiler_LCNF_Simp_simp(x_375, x_300, x_13, x_14, x_15, x_16, x_17, x_374);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_379 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_318, x_307, x_377, x_300, x_13, x_14, x_15, x_16, x_17, x_378);
lean_dec(x_13);
lean_dec(x_300);
return x_379;
}
else
{
uint8_t x_380; 
lean_dec(x_318);
lean_dec(x_307);
lean_dec(x_300);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_380 = !lean_is_exclusive(x_376);
if (x_380 == 0)
{
return x_376;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_376, 0);
x_382 = lean_ctor_get(x_376, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_376);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
}
else
{
uint8_t x_384; 
lean_dec(x_318);
lean_dec(x_307);
lean_dec(x_300);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_384 = !lean_is_exclusive(x_354);
if (x_384 == 0)
{
return x_354;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_354, 0);
x_386 = lean_ctor_get(x_354, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_354);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
}
}
else
{
uint8_t x_388; 
lean_dec(x_307);
lean_dec(x_300);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_388 = !lean_is_exclusive(x_314);
if (x_388 == 0)
{
return x_314;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_314, 0);
x_390 = lean_ctor_get(x_314, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_314);
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_5);
lean_dec(x_4);
x_392 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_308);
x_393 = lean_ctor_get(x_392, 1);
lean_inc(x_393);
lean_dec(x_392);
x_394 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_394, 0, x_300);
lean_closure_set(x_394, 1, x_13);
lean_closure_set(x_394, 2, x_6);
lean_closure_set(x_394, 3, x_7);
lean_closure_set(x_394, 4, x_8);
lean_closure_set(x_394, 5, x_9);
lean_closure_set(x_394, 6, x_10);
x_395 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_307, x_394, x_14, x_15, x_16, x_17, x_393);
if (lean_obj_tag(x_395) == 0)
{
uint8_t x_396; 
x_396 = !lean_is_exclusive(x_395);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = lean_ctor_get(x_395, 0);
x_398 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_395, 0, x_398);
return x_395;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_399 = lean_ctor_get(x_395, 0);
x_400 = lean_ctor_get(x_395, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_395);
x_401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_401, 0, x_399);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
}
else
{
uint8_t x_403; 
x_403 = !lean_is_exclusive(x_395);
if (x_403 == 0)
{
return x_395;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_395, 0);
x_405 = lean_ctor_get(x_395, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_395);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
return x_406;
}
}
}
}
else
{
uint8_t x_407; 
lean_dec(x_300);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_407 = !lean_is_exclusive(x_306);
if (x_407 == 0)
{
return x_306;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_306, 0);
x_409 = lean_ctor_get(x_306, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_306);
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
uint8_t x_430; 
lean_dec(x_300);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_430 = !lean_is_exclusive(x_302);
if (x_430 == 0)
{
return x_302;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_302, 0);
x_432 = lean_ctor_get(x_302, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_302);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
case 3:
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; lean_object* x_440; 
lean_dec(x_19);
x_434 = lean_ctor_get(x_12, 3);
x_435 = lean_ctor_get(x_12, 0);
x_436 = lean_ctor_get(x_12, 1);
x_437 = lean_ctor_get(x_12, 2);
lean_inc(x_434);
lean_inc(x_437);
lean_inc(x_436);
lean_inc(x_435);
x_438 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_438, 0, x_435);
lean_ctor_set(x_438, 1, x_436);
lean_ctor_set(x_438, 2, x_437);
lean_ctor_set(x_438, 3, x_434);
x_439 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_440 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_439, x_438, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_550; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_550 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_550 == 0)
{
lean_object* x_551; 
x_551 = lean_box(0);
x_443 = x_551;
goto block_549;
}
else
{
uint8_t x_552; 
x_552 = lean_nat_dec_eq(x_7, x_6);
if (x_552 == 0)
{
lean_object* x_553; 
x_553 = lean_box(0);
x_443 = x_553;
goto block_549;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_554 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_442);
x_555 = lean_ctor_get(x_554, 1);
lean_inc(x_555);
lean_dec(x_554);
x_556 = l_Lean_Compiler_LCNF_Simp_simp(x_441, x_438, x_13, x_14, x_15, x_16, x_17, x_555);
if (lean_obj_tag(x_556) == 0)
{
uint8_t x_557; 
x_557 = !lean_is_exclusive(x_556);
if (x_557 == 0)
{
lean_object* x_558; lean_object* x_559; 
x_558 = lean_ctor_get(x_556, 0);
x_559 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_556, 0, x_559);
return x_556;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_560 = lean_ctor_get(x_556, 0);
x_561 = lean_ctor_get(x_556, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_556);
x_562 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_562, 0, x_560);
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_561);
return x_563;
}
}
else
{
uint8_t x_564; 
x_564 = !lean_is_exclusive(x_556);
if (x_564 == 0)
{
return x_556;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_556, 0);
x_566 = lean_ctor_get(x_556, 1);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_556);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_566);
return x_567;
}
}
}
}
block_549:
{
lean_object* x_444; 
lean_dec(x_443);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_438);
x_444 = l_Lean_Compiler_LCNF_Simp_simp(x_441, x_438, x_13, x_14, x_15, x_16, x_17, x_442);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec(x_444);
lean_inc(x_445);
x_447 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_445);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_448 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_446);
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
lean_dec(x_448);
x_450 = lean_ctor_get(x_5, 2);
lean_inc(x_450);
lean_dec(x_5);
x_451 = l_Lean_mkAppN(x_450, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_452 = l_Lean_Compiler_LCNF_inferType(x_451, x_14, x_15, x_16, x_17, x_449);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = l_Lean_Compiler_LCNF_mkAuxParam(x_453, x_439, x_14, x_15, x_16, x_17, x_454);
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_458 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
lean_dec(x_10);
lean_dec(x_6);
x_459 = lean_ctor_get(x_456, 0);
lean_inc(x_459);
x_460 = lean_st_ref_get(x_17, x_457);
x_461 = lean_ctor_get(x_460, 1);
lean_inc(x_461);
lean_dec(x_460);
x_462 = lean_st_ref_take(x_13, x_461);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_ctor_get(x_463, 0);
lean_inc(x_465);
x_466 = l_Lean_Expr_fvar___override(x_459);
x_467 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_465, x_8, x_466);
x_468 = lean_ctor_get(x_463, 1);
lean_inc(x_468);
x_469 = lean_ctor_get(x_463, 2);
lean_inc(x_469);
x_470 = lean_ctor_get_uint8(x_463, sizeof(void*)*6);
x_471 = lean_ctor_get(x_463, 3);
lean_inc(x_471);
x_472 = lean_ctor_get(x_463, 4);
lean_inc(x_472);
x_473 = lean_ctor_get(x_463, 5);
lean_inc(x_473);
lean_dec(x_463);
x_474 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_474, 0, x_467);
lean_ctor_set(x_474, 1, x_468);
lean_ctor_set(x_474, 2, x_469);
lean_ctor_set(x_474, 3, x_471);
lean_ctor_set(x_474, 4, x_472);
lean_ctor_set(x_474, 5, x_473);
lean_ctor_set_uint8(x_474, sizeof(void*)*6, x_470);
x_475 = lean_st_ref_set(x_13, x_474, x_464);
x_476 = lean_ctor_get(x_475, 1);
lean_inc(x_476);
lean_dec(x_475);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_438);
x_477 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_438, x_13, x_14, x_15, x_16, x_17, x_476);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_477, 1);
lean_inc(x_479);
lean_dec(x_477);
x_480 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_456, x_445, x_478, x_438, x_13, x_14, x_15, x_16, x_17, x_479);
lean_dec(x_13);
lean_dec(x_438);
return x_480;
}
else
{
uint8_t x_481; 
lean_dec(x_456);
lean_dec(x_445);
lean_dec(x_438);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_481 = !lean_is_exclusive(x_477);
if (x_481 == 0)
{
return x_477;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_477, 0);
x_483 = lean_ctor_get(x_477, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_477);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_485 = lean_ctor_get(x_456, 0);
lean_inc(x_485);
x_486 = l_Lean_Expr_fvar___override(x_485);
x_487 = lean_array_get_size(x_10);
x_488 = l_Array_toSubarray___rarg(x_10, x_6, x_487);
x_489 = l_Array_ofSubarray___rarg(x_488);
x_490 = l_Lean_mkAppN(x_486, x_489);
x_491 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_492 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_490, x_491, x_14, x_15, x_16, x_17, x_457);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
lean_dec(x_492);
x_495 = lean_ctor_get(x_493, 0);
lean_inc(x_495);
x_496 = lean_st_ref_get(x_17, x_494);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
lean_dec(x_496);
x_498 = lean_st_ref_take(x_13, x_497);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
x_501 = lean_ctor_get(x_499, 0);
lean_inc(x_501);
x_502 = l_Lean_Expr_fvar___override(x_495);
x_503 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_501, x_8, x_502);
x_504 = lean_ctor_get(x_499, 1);
lean_inc(x_504);
x_505 = lean_ctor_get(x_499, 2);
lean_inc(x_505);
x_506 = lean_ctor_get_uint8(x_499, sizeof(void*)*6);
x_507 = lean_ctor_get(x_499, 3);
lean_inc(x_507);
x_508 = lean_ctor_get(x_499, 4);
lean_inc(x_508);
x_509 = lean_ctor_get(x_499, 5);
lean_inc(x_509);
lean_dec(x_499);
x_510 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_510, 0, x_503);
lean_ctor_set(x_510, 1, x_504);
lean_ctor_set(x_510, 2, x_505);
lean_ctor_set(x_510, 3, x_507);
lean_ctor_set(x_510, 4, x_508);
lean_ctor_set(x_510, 5, x_509);
lean_ctor_set_uint8(x_510, sizeof(void*)*6, x_506);
x_511 = lean_st_ref_set(x_13, x_510, x_500);
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
lean_dec(x_511);
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_493);
lean_ctor_set(x_513, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_438);
x_514 = l_Lean_Compiler_LCNF_Simp_simp(x_513, x_438, x_13, x_14, x_15, x_16, x_17, x_512);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
lean_dec(x_514);
x_517 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_456, x_445, x_515, x_438, x_13, x_14, x_15, x_16, x_17, x_516);
lean_dec(x_13);
lean_dec(x_438);
return x_517;
}
else
{
uint8_t x_518; 
lean_dec(x_456);
lean_dec(x_445);
lean_dec(x_438);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_518 = !lean_is_exclusive(x_514);
if (x_518 == 0)
{
return x_514;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_514, 0);
x_520 = lean_ctor_get(x_514, 1);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_514);
x_521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_521, 0, x_519);
lean_ctor_set(x_521, 1, x_520);
return x_521;
}
}
}
else
{
uint8_t x_522; 
lean_dec(x_456);
lean_dec(x_445);
lean_dec(x_438);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_522 = !lean_is_exclusive(x_492);
if (x_522 == 0)
{
return x_492;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_492, 0);
x_524 = lean_ctor_get(x_492, 1);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_492);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_523);
lean_ctor_set(x_525, 1, x_524);
return x_525;
}
}
}
}
else
{
uint8_t x_526; 
lean_dec(x_445);
lean_dec(x_438);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_526 = !lean_is_exclusive(x_452);
if (x_526 == 0)
{
return x_452;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_452, 0);
x_528 = lean_ctor_get(x_452, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_452);
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_527);
lean_ctor_set(x_529, 1, x_528);
return x_529;
}
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_5);
lean_dec(x_4);
x_530 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_446);
x_531 = lean_ctor_get(x_530, 1);
lean_inc(x_531);
lean_dec(x_530);
x_532 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_532, 0, x_438);
lean_closure_set(x_532, 1, x_13);
lean_closure_set(x_532, 2, x_6);
lean_closure_set(x_532, 3, x_7);
lean_closure_set(x_532, 4, x_8);
lean_closure_set(x_532, 5, x_9);
lean_closure_set(x_532, 6, x_10);
x_533 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_445, x_532, x_14, x_15, x_16, x_17, x_531);
if (lean_obj_tag(x_533) == 0)
{
uint8_t x_534; 
x_534 = !lean_is_exclusive(x_533);
if (x_534 == 0)
{
lean_object* x_535; lean_object* x_536; 
x_535 = lean_ctor_get(x_533, 0);
x_536 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_533, 0, x_536);
return x_533;
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_537 = lean_ctor_get(x_533, 0);
x_538 = lean_ctor_get(x_533, 1);
lean_inc(x_538);
lean_inc(x_537);
lean_dec(x_533);
x_539 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_539, 0, x_537);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_538);
return x_540;
}
}
else
{
uint8_t x_541; 
x_541 = !lean_is_exclusive(x_533);
if (x_541 == 0)
{
return x_533;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_ctor_get(x_533, 0);
x_543 = lean_ctor_get(x_533, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_533);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
return x_544;
}
}
}
}
else
{
uint8_t x_545; 
lean_dec(x_438);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_545 = !lean_is_exclusive(x_444);
if (x_545 == 0)
{
return x_444;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_444, 0);
x_547 = lean_ctor_get(x_444, 1);
lean_inc(x_547);
lean_inc(x_546);
lean_dec(x_444);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
return x_548;
}
}
}
}
else
{
uint8_t x_568; 
lean_dec(x_438);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_568 = !lean_is_exclusive(x_440);
if (x_568 == 0)
{
return x_440;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_440, 0);
x_570 = lean_ctor_get(x_440, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_440);
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set(x_571, 1, x_570);
return x_571;
}
}
}
case 4:
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; lean_object* x_580; 
x_572 = lean_ctor_get(x_12, 3);
x_573 = lean_ctor_get(x_12, 0);
x_574 = lean_ctor_get(x_12, 1);
x_575 = lean_ctor_get(x_12, 2);
x_576 = lean_ctor_get(x_19, 0);
lean_inc(x_576);
lean_dec(x_19);
lean_inc(x_572);
x_577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_577, 0, x_576);
lean_ctor_set(x_577, 1, x_572);
lean_inc(x_575);
lean_inc(x_574);
lean_inc(x_573);
x_578 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_578, 0, x_573);
lean_ctor_set(x_578, 1, x_574);
lean_ctor_set(x_578, 2, x_575);
lean_ctor_set(x_578, 3, x_577);
x_579 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_580 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_579, x_578, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_690; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec(x_580);
x_690 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_690 == 0)
{
lean_object* x_691; 
x_691 = lean_box(0);
x_583 = x_691;
goto block_689;
}
else
{
uint8_t x_692; 
x_692 = lean_nat_dec_eq(x_7, x_6);
if (x_692 == 0)
{
lean_object* x_693; 
x_693 = lean_box(0);
x_583 = x_693;
goto block_689;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_694 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_582);
x_695 = lean_ctor_get(x_694, 1);
lean_inc(x_695);
lean_dec(x_694);
x_696 = l_Lean_Compiler_LCNF_Simp_simp(x_581, x_578, x_13, x_14, x_15, x_16, x_17, x_695);
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
lean_object* x_584; 
lean_dec(x_583);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_578);
x_584 = l_Lean_Compiler_LCNF_Simp_simp(x_581, x_578, x_13, x_14, x_15, x_16, x_17, x_582);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
lean_dec(x_584);
lean_inc(x_585);
x_587 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_585);
if (x_587 == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_588 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_586);
x_589 = lean_ctor_get(x_588, 1);
lean_inc(x_589);
lean_dec(x_588);
x_590 = lean_ctor_get(x_5, 2);
lean_inc(x_590);
lean_dec(x_5);
x_591 = l_Lean_mkAppN(x_590, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_592 = l_Lean_Compiler_LCNF_inferType(x_591, x_14, x_15, x_16, x_17, x_589);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
lean_dec(x_592);
x_595 = l_Lean_Compiler_LCNF_mkAuxParam(x_593, x_579, x_14, x_15, x_16, x_17, x_594);
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
x_598 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_598 == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_10);
lean_dec(x_6);
x_599 = lean_ctor_get(x_596, 0);
lean_inc(x_599);
x_600 = lean_st_ref_get(x_17, x_597);
x_601 = lean_ctor_get(x_600, 1);
lean_inc(x_601);
lean_dec(x_600);
x_602 = lean_st_ref_take(x_13, x_601);
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
x_605 = lean_ctor_get(x_603, 0);
lean_inc(x_605);
x_606 = l_Lean_Expr_fvar___override(x_599);
x_607 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_605, x_8, x_606);
x_608 = lean_ctor_get(x_603, 1);
lean_inc(x_608);
x_609 = lean_ctor_get(x_603, 2);
lean_inc(x_609);
x_610 = lean_ctor_get_uint8(x_603, sizeof(void*)*6);
x_611 = lean_ctor_get(x_603, 3);
lean_inc(x_611);
x_612 = lean_ctor_get(x_603, 4);
lean_inc(x_612);
x_613 = lean_ctor_get(x_603, 5);
lean_inc(x_613);
lean_dec(x_603);
x_614 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_614, 0, x_607);
lean_ctor_set(x_614, 1, x_608);
lean_ctor_set(x_614, 2, x_609);
lean_ctor_set(x_614, 3, x_611);
lean_ctor_set(x_614, 4, x_612);
lean_ctor_set(x_614, 5, x_613);
lean_ctor_set_uint8(x_614, sizeof(void*)*6, x_610);
x_615 = lean_st_ref_set(x_13, x_614, x_604);
x_616 = lean_ctor_get(x_615, 1);
lean_inc(x_616);
lean_dec(x_615);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_578);
x_617 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_578, x_13, x_14, x_15, x_16, x_17, x_616);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_596, x_585, x_618, x_578, x_13, x_14, x_15, x_16, x_17, x_619);
lean_dec(x_13);
lean_dec(x_578);
return x_620;
}
else
{
uint8_t x_621; 
lean_dec(x_596);
lean_dec(x_585);
lean_dec(x_578);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_621 = !lean_is_exclusive(x_617);
if (x_621 == 0)
{
return x_617;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_622 = lean_ctor_get(x_617, 0);
x_623 = lean_ctor_get(x_617, 1);
lean_inc(x_623);
lean_inc(x_622);
lean_dec(x_617);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_622);
lean_ctor_set(x_624, 1, x_623);
return x_624;
}
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_625 = lean_ctor_get(x_596, 0);
lean_inc(x_625);
x_626 = l_Lean_Expr_fvar___override(x_625);
x_627 = lean_array_get_size(x_10);
x_628 = l_Array_toSubarray___rarg(x_10, x_6, x_627);
x_629 = l_Array_ofSubarray___rarg(x_628);
x_630 = l_Lean_mkAppN(x_626, x_629);
x_631 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_632 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_630, x_631, x_14, x_15, x_16, x_17, x_597);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_635 = lean_ctor_get(x_633, 0);
lean_inc(x_635);
x_636 = lean_st_ref_get(x_17, x_634);
x_637 = lean_ctor_get(x_636, 1);
lean_inc(x_637);
lean_dec(x_636);
x_638 = lean_st_ref_take(x_13, x_637);
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec(x_638);
x_641 = lean_ctor_get(x_639, 0);
lean_inc(x_641);
x_642 = l_Lean_Expr_fvar___override(x_635);
x_643 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_641, x_8, x_642);
x_644 = lean_ctor_get(x_639, 1);
lean_inc(x_644);
x_645 = lean_ctor_get(x_639, 2);
lean_inc(x_645);
x_646 = lean_ctor_get_uint8(x_639, sizeof(void*)*6);
x_647 = lean_ctor_get(x_639, 3);
lean_inc(x_647);
x_648 = lean_ctor_get(x_639, 4);
lean_inc(x_648);
x_649 = lean_ctor_get(x_639, 5);
lean_inc(x_649);
lean_dec(x_639);
x_650 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_650, 0, x_643);
lean_ctor_set(x_650, 1, x_644);
lean_ctor_set(x_650, 2, x_645);
lean_ctor_set(x_650, 3, x_647);
lean_ctor_set(x_650, 4, x_648);
lean_ctor_set(x_650, 5, x_649);
lean_ctor_set_uint8(x_650, sizeof(void*)*6, x_646);
x_651 = lean_st_ref_set(x_13, x_650, x_640);
x_652 = lean_ctor_get(x_651, 1);
lean_inc(x_652);
lean_dec(x_651);
x_653 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_653, 0, x_633);
lean_ctor_set(x_653, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_578);
x_654 = l_Lean_Compiler_LCNF_Simp_simp(x_653, x_578, x_13, x_14, x_15, x_16, x_17, x_652);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
lean_dec(x_654);
x_657 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_596, x_585, x_655, x_578, x_13, x_14, x_15, x_16, x_17, x_656);
lean_dec(x_13);
lean_dec(x_578);
return x_657;
}
else
{
uint8_t x_658; 
lean_dec(x_596);
lean_dec(x_585);
lean_dec(x_578);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
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
lean_dec(x_596);
lean_dec(x_585);
lean_dec(x_578);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_662 = !lean_is_exclusive(x_632);
if (x_662 == 0)
{
return x_632;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_632, 0);
x_664 = lean_ctor_get(x_632, 1);
lean_inc(x_664);
lean_inc(x_663);
lean_dec(x_632);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
return x_665;
}
}
}
}
else
{
uint8_t x_666; 
lean_dec(x_585);
lean_dec(x_578);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_666 = !lean_is_exclusive(x_592);
if (x_666 == 0)
{
return x_592;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_667 = lean_ctor_get(x_592, 0);
x_668 = lean_ctor_get(x_592, 1);
lean_inc(x_668);
lean_inc(x_667);
lean_dec(x_592);
x_669 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_669, 0, x_667);
lean_ctor_set(x_669, 1, x_668);
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_5);
lean_dec(x_4);
x_670 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_586);
x_671 = lean_ctor_get(x_670, 1);
lean_inc(x_671);
lean_dec(x_670);
x_672 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_672, 0, x_578);
lean_closure_set(x_672, 1, x_13);
lean_closure_set(x_672, 2, x_6);
lean_closure_set(x_672, 3, x_7);
lean_closure_set(x_672, 4, x_8);
lean_closure_set(x_672, 5, x_9);
lean_closure_set(x_672, 6, x_10);
x_673 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_585, x_672, x_14, x_15, x_16, x_17, x_671);
if (lean_obj_tag(x_673) == 0)
{
uint8_t x_674; 
x_674 = !lean_is_exclusive(x_673);
if (x_674 == 0)
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_673, 0);
x_676 = lean_alloc_ctor(1, 1, 0);
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
x_679 = lean_alloc_ctor(1, 1, 0);
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
lean_dec(x_578);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_685 = !lean_is_exclusive(x_584);
if (x_685 == 0)
{
return x_584;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_584, 0);
x_687 = lean_ctor_get(x_584, 1);
lean_inc(x_687);
lean_inc(x_686);
lean_dec(x_584);
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
lean_dec(x_578);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_708 = !lean_is_exclusive(x_580);
if (x_708 == 0)
{
return x_580;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_580, 0);
x_710 = lean_ctor_get(x_580, 1);
lean_inc(x_710);
lean_inc(x_709);
lean_dec(x_580);
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
return x_711;
}
}
}
case 5:
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; uint8_t x_717; lean_object* x_718; 
lean_dec(x_19);
x_712 = lean_ctor_get(x_12, 3);
x_713 = lean_ctor_get(x_12, 0);
x_714 = lean_ctor_get(x_12, 1);
x_715 = lean_ctor_get(x_12, 2);
lean_inc(x_712);
lean_inc(x_715);
lean_inc(x_714);
lean_inc(x_713);
x_716 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_716, 0, x_713);
lean_ctor_set(x_716, 1, x_714);
lean_ctor_set(x_716, 2, x_715);
lean_ctor_set(x_716, 3, x_712);
x_717 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_718 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_717, x_716, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; uint8_t x_828; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec(x_718);
x_828 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_828 == 0)
{
lean_object* x_829; 
x_829 = lean_box(0);
x_721 = x_829;
goto block_827;
}
else
{
uint8_t x_830; 
x_830 = lean_nat_dec_eq(x_7, x_6);
if (x_830 == 0)
{
lean_object* x_831; 
x_831 = lean_box(0);
x_721 = x_831;
goto block_827;
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_832 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_720);
x_833 = lean_ctor_get(x_832, 1);
lean_inc(x_833);
lean_dec(x_832);
x_834 = l_Lean_Compiler_LCNF_Simp_simp(x_719, x_716, x_13, x_14, x_15, x_16, x_17, x_833);
if (lean_obj_tag(x_834) == 0)
{
uint8_t x_835; 
x_835 = !lean_is_exclusive(x_834);
if (x_835 == 0)
{
lean_object* x_836; lean_object* x_837; 
x_836 = lean_ctor_get(x_834, 0);
x_837 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_837, 0, x_836);
lean_ctor_set(x_834, 0, x_837);
return x_834;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_838 = lean_ctor_get(x_834, 0);
x_839 = lean_ctor_get(x_834, 1);
lean_inc(x_839);
lean_inc(x_838);
lean_dec(x_834);
x_840 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_840, 0, x_838);
x_841 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_841, 0, x_840);
lean_ctor_set(x_841, 1, x_839);
return x_841;
}
}
else
{
uint8_t x_842; 
x_842 = !lean_is_exclusive(x_834);
if (x_842 == 0)
{
return x_834;
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_843 = lean_ctor_get(x_834, 0);
x_844 = lean_ctor_get(x_834, 1);
lean_inc(x_844);
lean_inc(x_843);
lean_dec(x_834);
x_845 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_845, 0, x_843);
lean_ctor_set(x_845, 1, x_844);
return x_845;
}
}
}
}
block_827:
{
lean_object* x_722; 
lean_dec(x_721);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_716);
x_722 = l_Lean_Compiler_LCNF_Simp_simp(x_719, x_716, x_13, x_14, x_15, x_16, x_17, x_720);
if (lean_obj_tag(x_722) == 0)
{
lean_object* x_723; lean_object* x_724; uint8_t x_725; 
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_722, 1);
lean_inc(x_724);
lean_dec(x_722);
lean_inc(x_723);
x_725 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_723);
if (x_725 == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_726 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_724);
x_727 = lean_ctor_get(x_726, 1);
lean_inc(x_727);
lean_dec(x_726);
x_728 = lean_ctor_get(x_5, 2);
lean_inc(x_728);
lean_dec(x_5);
x_729 = l_Lean_mkAppN(x_728, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_730 = l_Lean_Compiler_LCNF_inferType(x_729, x_14, x_15, x_16, x_17, x_727);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; uint8_t x_736; 
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec(x_730);
x_733 = l_Lean_Compiler_LCNF_mkAuxParam(x_731, x_717, x_14, x_15, x_16, x_17, x_732);
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
lean_dec(x_733);
x_736 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_736 == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; uint8_t x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
lean_dec(x_10);
lean_dec(x_6);
x_737 = lean_ctor_get(x_734, 0);
lean_inc(x_737);
x_738 = lean_st_ref_get(x_17, x_735);
x_739 = lean_ctor_get(x_738, 1);
lean_inc(x_739);
lean_dec(x_738);
x_740 = lean_st_ref_take(x_13, x_739);
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_740, 1);
lean_inc(x_742);
lean_dec(x_740);
x_743 = lean_ctor_get(x_741, 0);
lean_inc(x_743);
x_744 = l_Lean_Expr_fvar___override(x_737);
x_745 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_743, x_8, x_744);
x_746 = lean_ctor_get(x_741, 1);
lean_inc(x_746);
x_747 = lean_ctor_get(x_741, 2);
lean_inc(x_747);
x_748 = lean_ctor_get_uint8(x_741, sizeof(void*)*6);
x_749 = lean_ctor_get(x_741, 3);
lean_inc(x_749);
x_750 = lean_ctor_get(x_741, 4);
lean_inc(x_750);
x_751 = lean_ctor_get(x_741, 5);
lean_inc(x_751);
lean_dec(x_741);
x_752 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_752, 0, x_745);
lean_ctor_set(x_752, 1, x_746);
lean_ctor_set(x_752, 2, x_747);
lean_ctor_set(x_752, 3, x_749);
lean_ctor_set(x_752, 4, x_750);
lean_ctor_set(x_752, 5, x_751);
lean_ctor_set_uint8(x_752, sizeof(void*)*6, x_748);
x_753 = lean_st_ref_set(x_13, x_752, x_742);
x_754 = lean_ctor_get(x_753, 1);
lean_inc(x_754);
lean_dec(x_753);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_716);
x_755 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_716, x_13, x_14, x_15, x_16, x_17, x_754);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
lean_dec(x_755);
x_758 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_734, x_723, x_756, x_716, x_13, x_14, x_15, x_16, x_17, x_757);
lean_dec(x_13);
lean_dec(x_716);
return x_758;
}
else
{
uint8_t x_759; 
lean_dec(x_734);
lean_dec(x_723);
lean_dec(x_716);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_759 = !lean_is_exclusive(x_755);
if (x_759 == 0)
{
return x_755;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_760 = lean_ctor_get(x_755, 0);
x_761 = lean_ctor_get(x_755, 1);
lean_inc(x_761);
lean_inc(x_760);
lean_dec(x_755);
x_762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_762, 0, x_760);
lean_ctor_set(x_762, 1, x_761);
return x_762;
}
}
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_763 = lean_ctor_get(x_734, 0);
lean_inc(x_763);
x_764 = l_Lean_Expr_fvar___override(x_763);
x_765 = lean_array_get_size(x_10);
x_766 = l_Array_toSubarray___rarg(x_10, x_6, x_765);
x_767 = l_Array_ofSubarray___rarg(x_766);
x_768 = l_Lean_mkAppN(x_764, x_767);
x_769 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_770 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_768, x_769, x_14, x_15, x_16, x_17, x_735);
if (lean_obj_tag(x_770) == 0)
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; uint8_t x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_770, 1);
lean_inc(x_772);
lean_dec(x_770);
x_773 = lean_ctor_get(x_771, 0);
lean_inc(x_773);
x_774 = lean_st_ref_get(x_17, x_772);
x_775 = lean_ctor_get(x_774, 1);
lean_inc(x_775);
lean_dec(x_774);
x_776 = lean_st_ref_take(x_13, x_775);
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_776, 1);
lean_inc(x_778);
lean_dec(x_776);
x_779 = lean_ctor_get(x_777, 0);
lean_inc(x_779);
x_780 = l_Lean_Expr_fvar___override(x_773);
x_781 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_779, x_8, x_780);
x_782 = lean_ctor_get(x_777, 1);
lean_inc(x_782);
x_783 = lean_ctor_get(x_777, 2);
lean_inc(x_783);
x_784 = lean_ctor_get_uint8(x_777, sizeof(void*)*6);
x_785 = lean_ctor_get(x_777, 3);
lean_inc(x_785);
x_786 = lean_ctor_get(x_777, 4);
lean_inc(x_786);
x_787 = lean_ctor_get(x_777, 5);
lean_inc(x_787);
lean_dec(x_777);
x_788 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_788, 0, x_781);
lean_ctor_set(x_788, 1, x_782);
lean_ctor_set(x_788, 2, x_783);
lean_ctor_set(x_788, 3, x_785);
lean_ctor_set(x_788, 4, x_786);
lean_ctor_set(x_788, 5, x_787);
lean_ctor_set_uint8(x_788, sizeof(void*)*6, x_784);
x_789 = lean_st_ref_set(x_13, x_788, x_778);
x_790 = lean_ctor_get(x_789, 1);
lean_inc(x_790);
lean_dec(x_789);
x_791 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_791, 0, x_771);
lean_ctor_set(x_791, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_716);
x_792 = l_Lean_Compiler_LCNF_Simp_simp(x_791, x_716, x_13, x_14, x_15, x_16, x_17, x_790);
if (lean_obj_tag(x_792) == 0)
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
lean_dec(x_792);
x_795 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_734, x_723, x_793, x_716, x_13, x_14, x_15, x_16, x_17, x_794);
lean_dec(x_13);
lean_dec(x_716);
return x_795;
}
else
{
uint8_t x_796; 
lean_dec(x_734);
lean_dec(x_723);
lean_dec(x_716);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_796 = !lean_is_exclusive(x_792);
if (x_796 == 0)
{
return x_792;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_792, 0);
x_798 = lean_ctor_get(x_792, 1);
lean_inc(x_798);
lean_inc(x_797);
lean_dec(x_792);
x_799 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_799, 0, x_797);
lean_ctor_set(x_799, 1, x_798);
return x_799;
}
}
}
else
{
uint8_t x_800; 
lean_dec(x_734);
lean_dec(x_723);
lean_dec(x_716);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_800 = !lean_is_exclusive(x_770);
if (x_800 == 0)
{
return x_770;
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_801 = lean_ctor_get(x_770, 0);
x_802 = lean_ctor_get(x_770, 1);
lean_inc(x_802);
lean_inc(x_801);
lean_dec(x_770);
x_803 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_803, 0, x_801);
lean_ctor_set(x_803, 1, x_802);
return x_803;
}
}
}
}
else
{
uint8_t x_804; 
lean_dec(x_723);
lean_dec(x_716);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_804 = !lean_is_exclusive(x_730);
if (x_804 == 0)
{
return x_730;
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_805 = lean_ctor_get(x_730, 0);
x_806 = lean_ctor_get(x_730, 1);
lean_inc(x_806);
lean_inc(x_805);
lean_dec(x_730);
x_807 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_807, 0, x_805);
lean_ctor_set(x_807, 1, x_806);
return x_807;
}
}
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec(x_5);
lean_dec(x_4);
x_808 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_724);
x_809 = lean_ctor_get(x_808, 1);
lean_inc(x_809);
lean_dec(x_808);
x_810 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_810, 0, x_716);
lean_closure_set(x_810, 1, x_13);
lean_closure_set(x_810, 2, x_6);
lean_closure_set(x_810, 3, x_7);
lean_closure_set(x_810, 4, x_8);
lean_closure_set(x_810, 5, x_9);
lean_closure_set(x_810, 6, x_10);
x_811 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_723, x_810, x_14, x_15, x_16, x_17, x_809);
if (lean_obj_tag(x_811) == 0)
{
uint8_t x_812; 
x_812 = !lean_is_exclusive(x_811);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; 
x_813 = lean_ctor_get(x_811, 0);
x_814 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_814, 0, x_813);
lean_ctor_set(x_811, 0, x_814);
return x_811;
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_815 = lean_ctor_get(x_811, 0);
x_816 = lean_ctor_get(x_811, 1);
lean_inc(x_816);
lean_inc(x_815);
lean_dec(x_811);
x_817 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_817, 0, x_815);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_817);
lean_ctor_set(x_818, 1, x_816);
return x_818;
}
}
else
{
uint8_t x_819; 
x_819 = !lean_is_exclusive(x_811);
if (x_819 == 0)
{
return x_811;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_820 = lean_ctor_get(x_811, 0);
x_821 = lean_ctor_get(x_811, 1);
lean_inc(x_821);
lean_inc(x_820);
lean_dec(x_811);
x_822 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_822, 0, x_820);
lean_ctor_set(x_822, 1, x_821);
return x_822;
}
}
}
}
else
{
uint8_t x_823; 
lean_dec(x_716);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_823 = !lean_is_exclusive(x_722);
if (x_823 == 0)
{
return x_722;
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_824 = lean_ctor_get(x_722, 0);
x_825 = lean_ctor_get(x_722, 1);
lean_inc(x_825);
lean_inc(x_824);
lean_dec(x_722);
x_826 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_826, 0, x_824);
lean_ctor_set(x_826, 1, x_825);
return x_826;
}
}
}
}
else
{
uint8_t x_846; 
lean_dec(x_716);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_846 = !lean_is_exclusive(x_718);
if (x_846 == 0)
{
return x_718;
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_847 = lean_ctor_get(x_718, 0);
x_848 = lean_ctor_get(x_718, 1);
lean_inc(x_848);
lean_inc(x_847);
lean_dec(x_718);
x_849 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_849, 0, x_847);
lean_ctor_set(x_849, 1, x_848);
return x_849;
}
}
}
case 6:
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; uint8_t x_855; lean_object* x_856; 
lean_dec(x_19);
x_850 = lean_ctor_get(x_12, 3);
x_851 = lean_ctor_get(x_12, 0);
x_852 = lean_ctor_get(x_12, 1);
x_853 = lean_ctor_get(x_12, 2);
lean_inc(x_850);
lean_inc(x_853);
lean_inc(x_852);
lean_inc(x_851);
x_854 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_854, 0, x_851);
lean_ctor_set(x_854, 1, x_852);
lean_ctor_set(x_854, 2, x_853);
lean_ctor_set(x_854, 3, x_850);
x_855 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_856 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_855, x_854, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_856) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; uint8_t x_966; 
x_857 = lean_ctor_get(x_856, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_856, 1);
lean_inc(x_858);
lean_dec(x_856);
x_966 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_966 == 0)
{
lean_object* x_967; 
x_967 = lean_box(0);
x_859 = x_967;
goto block_965;
}
else
{
uint8_t x_968; 
x_968 = lean_nat_dec_eq(x_7, x_6);
if (x_968 == 0)
{
lean_object* x_969; 
x_969 = lean_box(0);
x_859 = x_969;
goto block_965;
}
else
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_970 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_858);
x_971 = lean_ctor_get(x_970, 1);
lean_inc(x_971);
lean_dec(x_970);
x_972 = l_Lean_Compiler_LCNF_Simp_simp(x_857, x_854, x_13, x_14, x_15, x_16, x_17, x_971);
if (lean_obj_tag(x_972) == 0)
{
uint8_t x_973; 
x_973 = !lean_is_exclusive(x_972);
if (x_973 == 0)
{
lean_object* x_974; lean_object* x_975; 
x_974 = lean_ctor_get(x_972, 0);
x_975 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_975, 0, x_974);
lean_ctor_set(x_972, 0, x_975);
return x_972;
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; 
x_976 = lean_ctor_get(x_972, 0);
x_977 = lean_ctor_get(x_972, 1);
lean_inc(x_977);
lean_inc(x_976);
lean_dec(x_972);
x_978 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_978, 0, x_976);
x_979 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_979, 0, x_978);
lean_ctor_set(x_979, 1, x_977);
return x_979;
}
}
else
{
uint8_t x_980; 
x_980 = !lean_is_exclusive(x_972);
if (x_980 == 0)
{
return x_972;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_981 = lean_ctor_get(x_972, 0);
x_982 = lean_ctor_get(x_972, 1);
lean_inc(x_982);
lean_inc(x_981);
lean_dec(x_972);
x_983 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_983, 0, x_981);
lean_ctor_set(x_983, 1, x_982);
return x_983;
}
}
}
}
block_965:
{
lean_object* x_860; 
lean_dec(x_859);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_854);
x_860 = l_Lean_Compiler_LCNF_Simp_simp(x_857, x_854, x_13, x_14, x_15, x_16, x_17, x_858);
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; uint8_t x_863; 
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
lean_dec(x_860);
lean_inc(x_861);
x_863 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_861);
if (x_863 == 0)
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_864 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_862);
x_865 = lean_ctor_get(x_864, 1);
lean_inc(x_865);
lean_dec(x_864);
x_866 = lean_ctor_get(x_5, 2);
lean_inc(x_866);
lean_dec(x_5);
x_867 = l_Lean_mkAppN(x_866, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_868 = l_Lean_Compiler_LCNF_inferType(x_867, x_14, x_15, x_16, x_17, x_865);
if (lean_obj_tag(x_868) == 0)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; uint8_t x_874; 
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
x_871 = l_Lean_Compiler_LCNF_mkAuxParam(x_869, x_855, x_14, x_15, x_16, x_17, x_870);
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_871, 1);
lean_inc(x_873);
lean_dec(x_871);
x_874 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_874 == 0)
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; uint8_t x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; 
lean_dec(x_10);
lean_dec(x_6);
x_875 = lean_ctor_get(x_872, 0);
lean_inc(x_875);
x_876 = lean_st_ref_get(x_17, x_873);
x_877 = lean_ctor_get(x_876, 1);
lean_inc(x_877);
lean_dec(x_876);
x_878 = lean_st_ref_take(x_13, x_877);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_ctor_get(x_879, 0);
lean_inc(x_881);
x_882 = l_Lean_Expr_fvar___override(x_875);
x_883 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_881, x_8, x_882);
x_884 = lean_ctor_get(x_879, 1);
lean_inc(x_884);
x_885 = lean_ctor_get(x_879, 2);
lean_inc(x_885);
x_886 = lean_ctor_get_uint8(x_879, sizeof(void*)*6);
x_887 = lean_ctor_get(x_879, 3);
lean_inc(x_887);
x_888 = lean_ctor_get(x_879, 4);
lean_inc(x_888);
x_889 = lean_ctor_get(x_879, 5);
lean_inc(x_889);
lean_dec(x_879);
x_890 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_890, 0, x_883);
lean_ctor_set(x_890, 1, x_884);
lean_ctor_set(x_890, 2, x_885);
lean_ctor_set(x_890, 3, x_887);
lean_ctor_set(x_890, 4, x_888);
lean_ctor_set(x_890, 5, x_889);
lean_ctor_set_uint8(x_890, sizeof(void*)*6, x_886);
x_891 = lean_st_ref_set(x_13, x_890, x_880);
x_892 = lean_ctor_get(x_891, 1);
lean_inc(x_892);
lean_dec(x_891);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_854);
x_893 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_854, x_13, x_14, x_15, x_16, x_17, x_892);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
lean_dec(x_893);
x_896 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_872, x_861, x_894, x_854, x_13, x_14, x_15, x_16, x_17, x_895);
lean_dec(x_13);
lean_dec(x_854);
return x_896;
}
else
{
uint8_t x_897; 
lean_dec(x_872);
lean_dec(x_861);
lean_dec(x_854);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_897 = !lean_is_exclusive(x_893);
if (x_897 == 0)
{
return x_893;
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_898 = lean_ctor_get(x_893, 0);
x_899 = lean_ctor_get(x_893, 1);
lean_inc(x_899);
lean_inc(x_898);
lean_dec(x_893);
x_900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_900, 0, x_898);
lean_ctor_set(x_900, 1, x_899);
return x_900;
}
}
}
else
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
x_901 = lean_ctor_get(x_872, 0);
lean_inc(x_901);
x_902 = l_Lean_Expr_fvar___override(x_901);
x_903 = lean_array_get_size(x_10);
x_904 = l_Array_toSubarray___rarg(x_10, x_6, x_903);
x_905 = l_Array_ofSubarray___rarg(x_904);
x_906 = l_Lean_mkAppN(x_902, x_905);
x_907 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_908 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_906, x_907, x_14, x_15, x_16, x_17, x_873);
if (lean_obj_tag(x_908) == 0)
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; uint8_t x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
x_909 = lean_ctor_get(x_908, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_908, 1);
lean_inc(x_910);
lean_dec(x_908);
x_911 = lean_ctor_get(x_909, 0);
lean_inc(x_911);
x_912 = lean_st_ref_get(x_17, x_910);
x_913 = lean_ctor_get(x_912, 1);
lean_inc(x_913);
lean_dec(x_912);
x_914 = lean_st_ref_take(x_13, x_913);
x_915 = lean_ctor_get(x_914, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_914, 1);
lean_inc(x_916);
lean_dec(x_914);
x_917 = lean_ctor_get(x_915, 0);
lean_inc(x_917);
x_918 = l_Lean_Expr_fvar___override(x_911);
x_919 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_917, x_8, x_918);
x_920 = lean_ctor_get(x_915, 1);
lean_inc(x_920);
x_921 = lean_ctor_get(x_915, 2);
lean_inc(x_921);
x_922 = lean_ctor_get_uint8(x_915, sizeof(void*)*6);
x_923 = lean_ctor_get(x_915, 3);
lean_inc(x_923);
x_924 = lean_ctor_get(x_915, 4);
lean_inc(x_924);
x_925 = lean_ctor_get(x_915, 5);
lean_inc(x_925);
lean_dec(x_915);
x_926 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_926, 0, x_919);
lean_ctor_set(x_926, 1, x_920);
lean_ctor_set(x_926, 2, x_921);
lean_ctor_set(x_926, 3, x_923);
lean_ctor_set(x_926, 4, x_924);
lean_ctor_set(x_926, 5, x_925);
lean_ctor_set_uint8(x_926, sizeof(void*)*6, x_922);
x_927 = lean_st_ref_set(x_13, x_926, x_916);
x_928 = lean_ctor_get(x_927, 1);
lean_inc(x_928);
lean_dec(x_927);
x_929 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_929, 0, x_909);
lean_ctor_set(x_929, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_854);
x_930 = l_Lean_Compiler_LCNF_Simp_simp(x_929, x_854, x_13, x_14, x_15, x_16, x_17, x_928);
if (lean_obj_tag(x_930) == 0)
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_930, 1);
lean_inc(x_932);
lean_dec(x_930);
x_933 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_872, x_861, x_931, x_854, x_13, x_14, x_15, x_16, x_17, x_932);
lean_dec(x_13);
lean_dec(x_854);
return x_933;
}
else
{
uint8_t x_934; 
lean_dec(x_872);
lean_dec(x_861);
lean_dec(x_854);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_934 = !lean_is_exclusive(x_930);
if (x_934 == 0)
{
return x_930;
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; 
x_935 = lean_ctor_get(x_930, 0);
x_936 = lean_ctor_get(x_930, 1);
lean_inc(x_936);
lean_inc(x_935);
lean_dec(x_930);
x_937 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_937, 0, x_935);
lean_ctor_set(x_937, 1, x_936);
return x_937;
}
}
}
else
{
uint8_t x_938; 
lean_dec(x_872);
lean_dec(x_861);
lean_dec(x_854);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_938 = !lean_is_exclusive(x_908);
if (x_938 == 0)
{
return x_908;
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_939 = lean_ctor_get(x_908, 0);
x_940 = lean_ctor_get(x_908, 1);
lean_inc(x_940);
lean_inc(x_939);
lean_dec(x_908);
x_941 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_941, 0, x_939);
lean_ctor_set(x_941, 1, x_940);
return x_941;
}
}
}
}
else
{
uint8_t x_942; 
lean_dec(x_861);
lean_dec(x_854);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_942 = !lean_is_exclusive(x_868);
if (x_942 == 0)
{
return x_868;
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_943 = lean_ctor_get(x_868, 0);
x_944 = lean_ctor_get(x_868, 1);
lean_inc(x_944);
lean_inc(x_943);
lean_dec(x_868);
x_945 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_945, 0, x_943);
lean_ctor_set(x_945, 1, x_944);
return x_945;
}
}
}
else
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
lean_dec(x_5);
lean_dec(x_4);
x_946 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_862);
x_947 = lean_ctor_get(x_946, 1);
lean_inc(x_947);
lean_dec(x_946);
x_948 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_948, 0, x_854);
lean_closure_set(x_948, 1, x_13);
lean_closure_set(x_948, 2, x_6);
lean_closure_set(x_948, 3, x_7);
lean_closure_set(x_948, 4, x_8);
lean_closure_set(x_948, 5, x_9);
lean_closure_set(x_948, 6, x_10);
x_949 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_861, x_948, x_14, x_15, x_16, x_17, x_947);
if (lean_obj_tag(x_949) == 0)
{
uint8_t x_950; 
x_950 = !lean_is_exclusive(x_949);
if (x_950 == 0)
{
lean_object* x_951; lean_object* x_952; 
x_951 = lean_ctor_get(x_949, 0);
x_952 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_952, 0, x_951);
lean_ctor_set(x_949, 0, x_952);
return x_949;
}
else
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
x_953 = lean_ctor_get(x_949, 0);
x_954 = lean_ctor_get(x_949, 1);
lean_inc(x_954);
lean_inc(x_953);
lean_dec(x_949);
x_955 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_955, 0, x_953);
x_956 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_956, 0, x_955);
lean_ctor_set(x_956, 1, x_954);
return x_956;
}
}
else
{
uint8_t x_957; 
x_957 = !lean_is_exclusive(x_949);
if (x_957 == 0)
{
return x_949;
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_958 = lean_ctor_get(x_949, 0);
x_959 = lean_ctor_get(x_949, 1);
lean_inc(x_959);
lean_inc(x_958);
lean_dec(x_949);
x_960 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_960, 0, x_958);
lean_ctor_set(x_960, 1, x_959);
return x_960;
}
}
}
}
else
{
uint8_t x_961; 
lean_dec(x_854);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_961 = !lean_is_exclusive(x_860);
if (x_961 == 0)
{
return x_860;
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_962 = lean_ctor_get(x_860, 0);
x_963 = lean_ctor_get(x_860, 1);
lean_inc(x_963);
lean_inc(x_962);
lean_dec(x_860);
x_964 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_964, 0, x_962);
lean_ctor_set(x_964, 1, x_963);
return x_964;
}
}
}
}
else
{
uint8_t x_984; 
lean_dec(x_854);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_984 = !lean_is_exclusive(x_856);
if (x_984 == 0)
{
return x_856;
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_985 = lean_ctor_get(x_856, 0);
x_986 = lean_ctor_get(x_856, 1);
lean_inc(x_986);
lean_inc(x_985);
lean_dec(x_856);
x_987 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_987, 0, x_985);
lean_ctor_set(x_987, 1, x_986);
return x_987;
}
}
}
case 7:
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; uint8_t x_993; lean_object* x_994; 
lean_dec(x_19);
x_988 = lean_ctor_get(x_12, 3);
x_989 = lean_ctor_get(x_12, 0);
x_990 = lean_ctor_get(x_12, 1);
x_991 = lean_ctor_get(x_12, 2);
lean_inc(x_988);
lean_inc(x_991);
lean_inc(x_990);
lean_inc(x_989);
x_992 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_992, 0, x_989);
lean_ctor_set(x_992, 1, x_990);
lean_ctor_set(x_992, 2, x_991);
lean_ctor_set(x_992, 3, x_988);
x_993 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_994 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_993, x_992, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_994) == 0)
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; uint8_t x_1104; 
x_995 = lean_ctor_get(x_994, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_994, 1);
lean_inc(x_996);
lean_dec(x_994);
x_1104 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_1104 == 0)
{
lean_object* x_1105; 
x_1105 = lean_box(0);
x_997 = x_1105;
goto block_1103;
}
else
{
uint8_t x_1106; 
x_1106 = lean_nat_dec_eq(x_7, x_6);
if (x_1106 == 0)
{
lean_object* x_1107; 
x_1107 = lean_box(0);
x_997 = x_1107;
goto block_1103;
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1108 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_996);
x_1109 = lean_ctor_get(x_1108, 1);
lean_inc(x_1109);
lean_dec(x_1108);
x_1110 = l_Lean_Compiler_LCNF_Simp_simp(x_995, x_992, x_13, x_14, x_15, x_16, x_17, x_1109);
if (lean_obj_tag(x_1110) == 0)
{
uint8_t x_1111; 
x_1111 = !lean_is_exclusive(x_1110);
if (x_1111 == 0)
{
lean_object* x_1112; lean_object* x_1113; 
x_1112 = lean_ctor_get(x_1110, 0);
x_1113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1113, 0, x_1112);
lean_ctor_set(x_1110, 0, x_1113);
return x_1110;
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
x_1114 = lean_ctor_get(x_1110, 0);
x_1115 = lean_ctor_get(x_1110, 1);
lean_inc(x_1115);
lean_inc(x_1114);
lean_dec(x_1110);
x_1116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1116, 0, x_1114);
x_1117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1117, 0, x_1116);
lean_ctor_set(x_1117, 1, x_1115);
return x_1117;
}
}
else
{
uint8_t x_1118; 
x_1118 = !lean_is_exclusive(x_1110);
if (x_1118 == 0)
{
return x_1110;
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1119 = lean_ctor_get(x_1110, 0);
x_1120 = lean_ctor_get(x_1110, 1);
lean_inc(x_1120);
lean_inc(x_1119);
lean_dec(x_1110);
x_1121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1121, 0, x_1119);
lean_ctor_set(x_1121, 1, x_1120);
return x_1121;
}
}
}
}
block_1103:
{
lean_object* x_998; 
lean_dec(x_997);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_992);
x_998 = l_Lean_Compiler_LCNF_Simp_simp(x_995, x_992, x_13, x_14, x_15, x_16, x_17, x_996);
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_999; lean_object* x_1000; uint8_t x_1001; 
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_998, 1);
lean_inc(x_1000);
lean_dec(x_998);
lean_inc(x_999);
x_1001 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_999);
if (x_1001 == 0)
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_1002 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1000);
x_1003 = lean_ctor_get(x_1002, 1);
lean_inc(x_1003);
lean_dec(x_1002);
x_1004 = lean_ctor_get(x_5, 2);
lean_inc(x_1004);
lean_dec(x_5);
x_1005 = l_Lean_mkAppN(x_1004, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1006 = l_Lean_Compiler_LCNF_inferType(x_1005, x_14, x_15, x_16, x_17, x_1003);
if (lean_obj_tag(x_1006) == 0)
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; uint8_t x_1012; 
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1006, 1);
lean_inc(x_1008);
lean_dec(x_1006);
x_1009 = l_Lean_Compiler_LCNF_mkAuxParam(x_1007, x_993, x_14, x_15, x_16, x_17, x_1008);
x_1010 = lean_ctor_get(x_1009, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_1009, 1);
lean_inc(x_1011);
lean_dec(x_1009);
x_1012 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_1012 == 0)
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; uint8_t x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
lean_dec(x_10);
lean_dec(x_6);
x_1013 = lean_ctor_get(x_1010, 0);
lean_inc(x_1013);
x_1014 = lean_st_ref_get(x_17, x_1011);
x_1015 = lean_ctor_get(x_1014, 1);
lean_inc(x_1015);
lean_dec(x_1014);
x_1016 = lean_st_ref_take(x_13, x_1015);
x_1017 = lean_ctor_get(x_1016, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1016, 1);
lean_inc(x_1018);
lean_dec(x_1016);
x_1019 = lean_ctor_get(x_1017, 0);
lean_inc(x_1019);
x_1020 = l_Lean_Expr_fvar___override(x_1013);
x_1021 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1019, x_8, x_1020);
x_1022 = lean_ctor_get(x_1017, 1);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1017, 2);
lean_inc(x_1023);
x_1024 = lean_ctor_get_uint8(x_1017, sizeof(void*)*6);
x_1025 = lean_ctor_get(x_1017, 3);
lean_inc(x_1025);
x_1026 = lean_ctor_get(x_1017, 4);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1017, 5);
lean_inc(x_1027);
lean_dec(x_1017);
x_1028 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_1028, 0, x_1021);
lean_ctor_set(x_1028, 1, x_1022);
lean_ctor_set(x_1028, 2, x_1023);
lean_ctor_set(x_1028, 3, x_1025);
lean_ctor_set(x_1028, 4, x_1026);
lean_ctor_set(x_1028, 5, x_1027);
lean_ctor_set_uint8(x_1028, sizeof(void*)*6, x_1024);
x_1029 = lean_st_ref_set(x_13, x_1028, x_1018);
x_1030 = lean_ctor_get(x_1029, 1);
lean_inc(x_1030);
lean_dec(x_1029);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_992);
x_1031 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_992, x_13, x_14, x_15, x_16, x_17, x_1030);
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1031, 1);
lean_inc(x_1033);
lean_dec(x_1031);
x_1034 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1010, x_999, x_1032, x_992, x_13, x_14, x_15, x_16, x_17, x_1033);
lean_dec(x_13);
lean_dec(x_992);
return x_1034;
}
else
{
uint8_t x_1035; 
lean_dec(x_1010);
lean_dec(x_999);
lean_dec(x_992);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_1035 = !lean_is_exclusive(x_1031);
if (x_1035 == 0)
{
return x_1031;
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1036 = lean_ctor_get(x_1031, 0);
x_1037 = lean_ctor_get(x_1031, 1);
lean_inc(x_1037);
lean_inc(x_1036);
lean_dec(x_1031);
x_1038 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1038, 0, x_1036);
lean_ctor_set(x_1038, 1, x_1037);
return x_1038;
}
}
}
else
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
x_1039 = lean_ctor_get(x_1010, 0);
lean_inc(x_1039);
x_1040 = l_Lean_Expr_fvar___override(x_1039);
x_1041 = lean_array_get_size(x_10);
x_1042 = l_Array_toSubarray___rarg(x_10, x_6, x_1041);
x_1043 = l_Array_ofSubarray___rarg(x_1042);
x_1044 = l_Lean_mkAppN(x_1040, x_1043);
x_1045 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1046 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1044, x_1045, x_14, x_15, x_16, x_17, x_1011);
if (lean_obj_tag(x_1046) == 0)
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; uint8_t x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
x_1047 = lean_ctor_get(x_1046, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1046, 1);
lean_inc(x_1048);
lean_dec(x_1046);
x_1049 = lean_ctor_get(x_1047, 0);
lean_inc(x_1049);
x_1050 = lean_st_ref_get(x_17, x_1048);
x_1051 = lean_ctor_get(x_1050, 1);
lean_inc(x_1051);
lean_dec(x_1050);
x_1052 = lean_st_ref_take(x_13, x_1051);
x_1053 = lean_ctor_get(x_1052, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1052, 1);
lean_inc(x_1054);
lean_dec(x_1052);
x_1055 = lean_ctor_get(x_1053, 0);
lean_inc(x_1055);
x_1056 = l_Lean_Expr_fvar___override(x_1049);
x_1057 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1055, x_8, x_1056);
x_1058 = lean_ctor_get(x_1053, 1);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1053, 2);
lean_inc(x_1059);
x_1060 = lean_ctor_get_uint8(x_1053, sizeof(void*)*6);
x_1061 = lean_ctor_get(x_1053, 3);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1053, 4);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1053, 5);
lean_inc(x_1063);
lean_dec(x_1053);
x_1064 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_1064, 0, x_1057);
lean_ctor_set(x_1064, 1, x_1058);
lean_ctor_set(x_1064, 2, x_1059);
lean_ctor_set(x_1064, 3, x_1061);
lean_ctor_set(x_1064, 4, x_1062);
lean_ctor_set(x_1064, 5, x_1063);
lean_ctor_set_uint8(x_1064, sizeof(void*)*6, x_1060);
x_1065 = lean_st_ref_set(x_13, x_1064, x_1054);
x_1066 = lean_ctor_get(x_1065, 1);
lean_inc(x_1066);
lean_dec(x_1065);
x_1067 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1067, 0, x_1047);
lean_ctor_set(x_1067, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_992);
x_1068 = l_Lean_Compiler_LCNF_Simp_simp(x_1067, x_992, x_13, x_14, x_15, x_16, x_17, x_1066);
if (lean_obj_tag(x_1068) == 0)
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1068, 1);
lean_inc(x_1070);
lean_dec(x_1068);
x_1071 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1010, x_999, x_1069, x_992, x_13, x_14, x_15, x_16, x_17, x_1070);
lean_dec(x_13);
lean_dec(x_992);
return x_1071;
}
else
{
uint8_t x_1072; 
lean_dec(x_1010);
lean_dec(x_999);
lean_dec(x_992);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_1072 = !lean_is_exclusive(x_1068);
if (x_1072 == 0)
{
return x_1068;
}
else
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
x_1073 = lean_ctor_get(x_1068, 0);
x_1074 = lean_ctor_get(x_1068, 1);
lean_inc(x_1074);
lean_inc(x_1073);
lean_dec(x_1068);
x_1075 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1075, 0, x_1073);
lean_ctor_set(x_1075, 1, x_1074);
return x_1075;
}
}
}
else
{
uint8_t x_1076; 
lean_dec(x_1010);
lean_dec(x_999);
lean_dec(x_992);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_1076 = !lean_is_exclusive(x_1046);
if (x_1076 == 0)
{
return x_1046;
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1077 = lean_ctor_get(x_1046, 0);
x_1078 = lean_ctor_get(x_1046, 1);
lean_inc(x_1078);
lean_inc(x_1077);
lean_dec(x_1046);
x_1079 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1079, 0, x_1077);
lean_ctor_set(x_1079, 1, x_1078);
return x_1079;
}
}
}
}
else
{
uint8_t x_1080; 
lean_dec(x_999);
lean_dec(x_992);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1080 = !lean_is_exclusive(x_1006);
if (x_1080 == 0)
{
return x_1006;
}
else
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1081 = lean_ctor_get(x_1006, 0);
x_1082 = lean_ctor_get(x_1006, 1);
lean_inc(x_1082);
lean_inc(x_1081);
lean_dec(x_1006);
x_1083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1083, 0, x_1081);
lean_ctor_set(x_1083, 1, x_1082);
return x_1083;
}
}
}
else
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
lean_dec(x_5);
lean_dec(x_4);
x_1084 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1000);
x_1085 = lean_ctor_get(x_1084, 1);
lean_inc(x_1085);
lean_dec(x_1084);
x_1086 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_1086, 0, x_992);
lean_closure_set(x_1086, 1, x_13);
lean_closure_set(x_1086, 2, x_6);
lean_closure_set(x_1086, 3, x_7);
lean_closure_set(x_1086, 4, x_8);
lean_closure_set(x_1086, 5, x_9);
lean_closure_set(x_1086, 6, x_10);
x_1087 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_999, x_1086, x_14, x_15, x_16, x_17, x_1085);
if (lean_obj_tag(x_1087) == 0)
{
uint8_t x_1088; 
x_1088 = !lean_is_exclusive(x_1087);
if (x_1088 == 0)
{
lean_object* x_1089; lean_object* x_1090; 
x_1089 = lean_ctor_get(x_1087, 0);
x_1090 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1090, 0, x_1089);
lean_ctor_set(x_1087, 0, x_1090);
return x_1087;
}
else
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
x_1091 = lean_ctor_get(x_1087, 0);
x_1092 = lean_ctor_get(x_1087, 1);
lean_inc(x_1092);
lean_inc(x_1091);
lean_dec(x_1087);
x_1093 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1093, 0, x_1091);
x_1094 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1094, 0, x_1093);
lean_ctor_set(x_1094, 1, x_1092);
return x_1094;
}
}
else
{
uint8_t x_1095; 
x_1095 = !lean_is_exclusive(x_1087);
if (x_1095 == 0)
{
return x_1087;
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1096 = lean_ctor_get(x_1087, 0);
x_1097 = lean_ctor_get(x_1087, 1);
lean_inc(x_1097);
lean_inc(x_1096);
lean_dec(x_1087);
x_1098 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1098, 0, x_1096);
lean_ctor_set(x_1098, 1, x_1097);
return x_1098;
}
}
}
}
else
{
uint8_t x_1099; 
lean_dec(x_992);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1099 = !lean_is_exclusive(x_998);
if (x_1099 == 0)
{
return x_998;
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
x_1100 = lean_ctor_get(x_998, 0);
x_1101 = lean_ctor_get(x_998, 1);
lean_inc(x_1101);
lean_inc(x_1100);
lean_dec(x_998);
x_1102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1102, 0, x_1100);
lean_ctor_set(x_1102, 1, x_1101);
return x_1102;
}
}
}
}
else
{
uint8_t x_1122; 
lean_dec(x_992);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1122 = !lean_is_exclusive(x_994);
if (x_1122 == 0)
{
return x_994;
}
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
x_1123 = lean_ctor_get(x_994, 0);
x_1124 = lean_ctor_get(x_994, 1);
lean_inc(x_1124);
lean_inc(x_1123);
lean_dec(x_994);
x_1125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1125, 0, x_1123);
lean_ctor_set(x_1125, 1, x_1124);
return x_1125;
}
}
}
case 8:
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; uint8_t x_1131; lean_object* x_1132; 
lean_dec(x_19);
x_1126 = lean_ctor_get(x_12, 3);
x_1127 = lean_ctor_get(x_12, 0);
x_1128 = lean_ctor_get(x_12, 1);
x_1129 = lean_ctor_get(x_12, 2);
lean_inc(x_1126);
lean_inc(x_1129);
lean_inc(x_1128);
lean_inc(x_1127);
x_1130 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1130, 0, x_1127);
lean_ctor_set(x_1130, 1, x_1128);
lean_ctor_set(x_1130, 2, x_1129);
lean_ctor_set(x_1130, 3, x_1126);
x_1131 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_1132 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_1131, x_1130, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_1132) == 0)
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; uint8_t x_1242; 
x_1133 = lean_ctor_get(x_1132, 0);
lean_inc(x_1133);
x_1134 = lean_ctor_get(x_1132, 1);
lean_inc(x_1134);
lean_dec(x_1132);
x_1242 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_1242 == 0)
{
lean_object* x_1243; 
x_1243 = lean_box(0);
x_1135 = x_1243;
goto block_1241;
}
else
{
uint8_t x_1244; 
x_1244 = lean_nat_dec_eq(x_7, x_6);
if (x_1244 == 0)
{
lean_object* x_1245; 
x_1245 = lean_box(0);
x_1135 = x_1245;
goto block_1241;
}
else
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1246 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1134);
x_1247 = lean_ctor_get(x_1246, 1);
lean_inc(x_1247);
lean_dec(x_1246);
x_1248 = l_Lean_Compiler_LCNF_Simp_simp(x_1133, x_1130, x_13, x_14, x_15, x_16, x_17, x_1247);
if (lean_obj_tag(x_1248) == 0)
{
uint8_t x_1249; 
x_1249 = !lean_is_exclusive(x_1248);
if (x_1249 == 0)
{
lean_object* x_1250; lean_object* x_1251; 
x_1250 = lean_ctor_get(x_1248, 0);
x_1251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1251, 0, x_1250);
lean_ctor_set(x_1248, 0, x_1251);
return x_1248;
}
else
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; 
x_1252 = lean_ctor_get(x_1248, 0);
x_1253 = lean_ctor_get(x_1248, 1);
lean_inc(x_1253);
lean_inc(x_1252);
lean_dec(x_1248);
x_1254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1254, 0, x_1252);
x_1255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1255, 0, x_1254);
lean_ctor_set(x_1255, 1, x_1253);
return x_1255;
}
}
else
{
uint8_t x_1256; 
x_1256 = !lean_is_exclusive(x_1248);
if (x_1256 == 0)
{
return x_1248;
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; 
x_1257 = lean_ctor_get(x_1248, 0);
x_1258 = lean_ctor_get(x_1248, 1);
lean_inc(x_1258);
lean_inc(x_1257);
lean_dec(x_1248);
x_1259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1259, 0, x_1257);
lean_ctor_set(x_1259, 1, x_1258);
return x_1259;
}
}
}
}
block_1241:
{
lean_object* x_1136; 
lean_dec(x_1135);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1130);
x_1136 = l_Lean_Compiler_LCNF_Simp_simp(x_1133, x_1130, x_13, x_14, x_15, x_16, x_17, x_1134);
if (lean_obj_tag(x_1136) == 0)
{
lean_object* x_1137; lean_object* x_1138; uint8_t x_1139; 
x_1137 = lean_ctor_get(x_1136, 0);
lean_inc(x_1137);
x_1138 = lean_ctor_get(x_1136, 1);
lean_inc(x_1138);
lean_dec(x_1136);
lean_inc(x_1137);
x_1139 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1137);
if (x_1139 == 0)
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1140 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1138);
x_1141 = lean_ctor_get(x_1140, 1);
lean_inc(x_1141);
lean_dec(x_1140);
x_1142 = lean_ctor_get(x_5, 2);
lean_inc(x_1142);
lean_dec(x_5);
x_1143 = l_Lean_mkAppN(x_1142, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1144 = l_Lean_Compiler_LCNF_inferType(x_1143, x_14, x_15, x_16, x_17, x_1141);
if (lean_obj_tag(x_1144) == 0)
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; uint8_t x_1150; 
x_1145 = lean_ctor_get(x_1144, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1144, 1);
lean_inc(x_1146);
lean_dec(x_1144);
x_1147 = l_Lean_Compiler_LCNF_mkAuxParam(x_1145, x_1131, x_14, x_15, x_16, x_17, x_1146);
x_1148 = lean_ctor_get(x_1147, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1147, 1);
lean_inc(x_1149);
lean_dec(x_1147);
x_1150 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_1150 == 0)
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; uint8_t x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; 
lean_dec(x_10);
lean_dec(x_6);
x_1151 = lean_ctor_get(x_1148, 0);
lean_inc(x_1151);
x_1152 = lean_st_ref_get(x_17, x_1149);
x_1153 = lean_ctor_get(x_1152, 1);
lean_inc(x_1153);
lean_dec(x_1152);
x_1154 = lean_st_ref_take(x_13, x_1153);
x_1155 = lean_ctor_get(x_1154, 0);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1154, 1);
lean_inc(x_1156);
lean_dec(x_1154);
x_1157 = lean_ctor_get(x_1155, 0);
lean_inc(x_1157);
x_1158 = l_Lean_Expr_fvar___override(x_1151);
x_1159 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1157, x_8, x_1158);
x_1160 = lean_ctor_get(x_1155, 1);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1155, 2);
lean_inc(x_1161);
x_1162 = lean_ctor_get_uint8(x_1155, sizeof(void*)*6);
x_1163 = lean_ctor_get(x_1155, 3);
lean_inc(x_1163);
x_1164 = lean_ctor_get(x_1155, 4);
lean_inc(x_1164);
x_1165 = lean_ctor_get(x_1155, 5);
lean_inc(x_1165);
lean_dec(x_1155);
x_1166 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_1166, 0, x_1159);
lean_ctor_set(x_1166, 1, x_1160);
lean_ctor_set(x_1166, 2, x_1161);
lean_ctor_set(x_1166, 3, x_1163);
lean_ctor_set(x_1166, 4, x_1164);
lean_ctor_set(x_1166, 5, x_1165);
lean_ctor_set_uint8(x_1166, sizeof(void*)*6, x_1162);
x_1167 = lean_st_ref_set(x_13, x_1166, x_1156);
x_1168 = lean_ctor_get(x_1167, 1);
lean_inc(x_1168);
lean_dec(x_1167);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1130);
x_1169 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_1130, x_13, x_14, x_15, x_16, x_17, x_1168);
if (lean_obj_tag(x_1169) == 0)
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1170 = lean_ctor_get(x_1169, 0);
lean_inc(x_1170);
x_1171 = lean_ctor_get(x_1169, 1);
lean_inc(x_1171);
lean_dec(x_1169);
x_1172 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1148, x_1137, x_1170, x_1130, x_13, x_14, x_15, x_16, x_17, x_1171);
lean_dec(x_13);
lean_dec(x_1130);
return x_1172;
}
else
{
uint8_t x_1173; 
lean_dec(x_1148);
lean_dec(x_1137);
lean_dec(x_1130);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_1173 = !lean_is_exclusive(x_1169);
if (x_1173 == 0)
{
return x_1169;
}
else
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1174 = lean_ctor_get(x_1169, 0);
x_1175 = lean_ctor_get(x_1169, 1);
lean_inc(x_1175);
lean_inc(x_1174);
lean_dec(x_1169);
x_1176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1176, 0, x_1174);
lean_ctor_set(x_1176, 1, x_1175);
return x_1176;
}
}
}
else
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; 
x_1177 = lean_ctor_get(x_1148, 0);
lean_inc(x_1177);
x_1178 = l_Lean_Expr_fvar___override(x_1177);
x_1179 = lean_array_get_size(x_10);
x_1180 = l_Array_toSubarray___rarg(x_10, x_6, x_1179);
x_1181 = l_Array_ofSubarray___rarg(x_1180);
x_1182 = l_Lean_mkAppN(x_1178, x_1181);
x_1183 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1184 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1182, x_1183, x_14, x_15, x_16, x_17, x_1149);
if (lean_obj_tag(x_1184) == 0)
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; uint8_t x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; 
x_1185 = lean_ctor_get(x_1184, 0);
lean_inc(x_1185);
x_1186 = lean_ctor_get(x_1184, 1);
lean_inc(x_1186);
lean_dec(x_1184);
x_1187 = lean_ctor_get(x_1185, 0);
lean_inc(x_1187);
x_1188 = lean_st_ref_get(x_17, x_1186);
x_1189 = lean_ctor_get(x_1188, 1);
lean_inc(x_1189);
lean_dec(x_1188);
x_1190 = lean_st_ref_take(x_13, x_1189);
x_1191 = lean_ctor_get(x_1190, 0);
lean_inc(x_1191);
x_1192 = lean_ctor_get(x_1190, 1);
lean_inc(x_1192);
lean_dec(x_1190);
x_1193 = lean_ctor_get(x_1191, 0);
lean_inc(x_1193);
x_1194 = l_Lean_Expr_fvar___override(x_1187);
x_1195 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1193, x_8, x_1194);
x_1196 = lean_ctor_get(x_1191, 1);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1191, 2);
lean_inc(x_1197);
x_1198 = lean_ctor_get_uint8(x_1191, sizeof(void*)*6);
x_1199 = lean_ctor_get(x_1191, 3);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1191, 4);
lean_inc(x_1200);
x_1201 = lean_ctor_get(x_1191, 5);
lean_inc(x_1201);
lean_dec(x_1191);
x_1202 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_1202, 0, x_1195);
lean_ctor_set(x_1202, 1, x_1196);
lean_ctor_set(x_1202, 2, x_1197);
lean_ctor_set(x_1202, 3, x_1199);
lean_ctor_set(x_1202, 4, x_1200);
lean_ctor_set(x_1202, 5, x_1201);
lean_ctor_set_uint8(x_1202, sizeof(void*)*6, x_1198);
x_1203 = lean_st_ref_set(x_13, x_1202, x_1192);
x_1204 = lean_ctor_get(x_1203, 1);
lean_inc(x_1204);
lean_dec(x_1203);
x_1205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1205, 0, x_1185);
lean_ctor_set(x_1205, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1130);
x_1206 = l_Lean_Compiler_LCNF_Simp_simp(x_1205, x_1130, x_13, x_14, x_15, x_16, x_17, x_1204);
if (lean_obj_tag(x_1206) == 0)
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; 
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
lean_dec(x_1206);
x_1209 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1148, x_1137, x_1207, x_1130, x_13, x_14, x_15, x_16, x_17, x_1208);
lean_dec(x_13);
lean_dec(x_1130);
return x_1209;
}
else
{
uint8_t x_1210; 
lean_dec(x_1148);
lean_dec(x_1137);
lean_dec(x_1130);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_1210 = !lean_is_exclusive(x_1206);
if (x_1210 == 0)
{
return x_1206;
}
else
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
x_1211 = lean_ctor_get(x_1206, 0);
x_1212 = lean_ctor_get(x_1206, 1);
lean_inc(x_1212);
lean_inc(x_1211);
lean_dec(x_1206);
x_1213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1213, 0, x_1211);
lean_ctor_set(x_1213, 1, x_1212);
return x_1213;
}
}
}
else
{
uint8_t x_1214; 
lean_dec(x_1148);
lean_dec(x_1137);
lean_dec(x_1130);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_1214 = !lean_is_exclusive(x_1184);
if (x_1214 == 0)
{
return x_1184;
}
else
{
lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; 
x_1215 = lean_ctor_get(x_1184, 0);
x_1216 = lean_ctor_get(x_1184, 1);
lean_inc(x_1216);
lean_inc(x_1215);
lean_dec(x_1184);
x_1217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1217, 0, x_1215);
lean_ctor_set(x_1217, 1, x_1216);
return x_1217;
}
}
}
}
else
{
uint8_t x_1218; 
lean_dec(x_1137);
lean_dec(x_1130);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1218 = !lean_is_exclusive(x_1144);
if (x_1218 == 0)
{
return x_1144;
}
else
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; 
x_1219 = lean_ctor_get(x_1144, 0);
x_1220 = lean_ctor_get(x_1144, 1);
lean_inc(x_1220);
lean_inc(x_1219);
lean_dec(x_1144);
x_1221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1221, 0, x_1219);
lean_ctor_set(x_1221, 1, x_1220);
return x_1221;
}
}
}
else
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; 
lean_dec(x_5);
lean_dec(x_4);
x_1222 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1138);
x_1223 = lean_ctor_get(x_1222, 1);
lean_inc(x_1223);
lean_dec(x_1222);
x_1224 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_1224, 0, x_1130);
lean_closure_set(x_1224, 1, x_13);
lean_closure_set(x_1224, 2, x_6);
lean_closure_set(x_1224, 3, x_7);
lean_closure_set(x_1224, 4, x_8);
lean_closure_set(x_1224, 5, x_9);
lean_closure_set(x_1224, 6, x_10);
x_1225 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1137, x_1224, x_14, x_15, x_16, x_17, x_1223);
if (lean_obj_tag(x_1225) == 0)
{
uint8_t x_1226; 
x_1226 = !lean_is_exclusive(x_1225);
if (x_1226 == 0)
{
lean_object* x_1227; lean_object* x_1228; 
x_1227 = lean_ctor_get(x_1225, 0);
x_1228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1228, 0, x_1227);
lean_ctor_set(x_1225, 0, x_1228);
return x_1225;
}
else
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; 
x_1229 = lean_ctor_get(x_1225, 0);
x_1230 = lean_ctor_get(x_1225, 1);
lean_inc(x_1230);
lean_inc(x_1229);
lean_dec(x_1225);
x_1231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1231, 0, x_1229);
x_1232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1232, 0, x_1231);
lean_ctor_set(x_1232, 1, x_1230);
return x_1232;
}
}
else
{
uint8_t x_1233; 
x_1233 = !lean_is_exclusive(x_1225);
if (x_1233 == 0)
{
return x_1225;
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
x_1234 = lean_ctor_get(x_1225, 0);
x_1235 = lean_ctor_get(x_1225, 1);
lean_inc(x_1235);
lean_inc(x_1234);
lean_dec(x_1225);
x_1236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1236, 0, x_1234);
lean_ctor_set(x_1236, 1, x_1235);
return x_1236;
}
}
}
}
else
{
uint8_t x_1237; 
lean_dec(x_1130);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1237 = !lean_is_exclusive(x_1136);
if (x_1237 == 0)
{
return x_1136;
}
else
{
lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
x_1238 = lean_ctor_get(x_1136, 0);
x_1239 = lean_ctor_get(x_1136, 1);
lean_inc(x_1239);
lean_inc(x_1238);
lean_dec(x_1136);
x_1240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1240, 0, x_1238);
lean_ctor_set(x_1240, 1, x_1239);
return x_1240;
}
}
}
}
else
{
uint8_t x_1260; 
lean_dec(x_1130);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1260 = !lean_is_exclusive(x_1132);
if (x_1260 == 0)
{
return x_1132;
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
x_1261 = lean_ctor_get(x_1132, 0);
x_1262 = lean_ctor_get(x_1132, 1);
lean_inc(x_1262);
lean_inc(x_1261);
lean_dec(x_1132);
x_1263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1263, 0, x_1261);
lean_ctor_set(x_1263, 1, x_1262);
return x_1263;
}
}
}
case 9:
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; uint8_t x_1269; lean_object* x_1270; 
lean_dec(x_19);
x_1264 = lean_ctor_get(x_12, 3);
x_1265 = lean_ctor_get(x_12, 0);
x_1266 = lean_ctor_get(x_12, 1);
x_1267 = lean_ctor_get(x_12, 2);
lean_inc(x_1264);
lean_inc(x_1267);
lean_inc(x_1266);
lean_inc(x_1265);
x_1268 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1268, 0, x_1265);
lean_ctor_set(x_1268, 1, x_1266);
lean_ctor_set(x_1268, 2, x_1267);
lean_ctor_set(x_1268, 3, x_1264);
x_1269 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_1270 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_1269, x_1268, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_1270) == 0)
{
lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; uint8_t x_1380; 
x_1271 = lean_ctor_get(x_1270, 0);
lean_inc(x_1271);
x_1272 = lean_ctor_get(x_1270, 1);
lean_inc(x_1272);
lean_dec(x_1270);
x_1380 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_1380 == 0)
{
lean_object* x_1381; 
x_1381 = lean_box(0);
x_1273 = x_1381;
goto block_1379;
}
else
{
uint8_t x_1382; 
x_1382 = lean_nat_dec_eq(x_7, x_6);
if (x_1382 == 0)
{
lean_object* x_1383; 
x_1383 = lean_box(0);
x_1273 = x_1383;
goto block_1379;
}
else
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1384 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1272);
x_1385 = lean_ctor_get(x_1384, 1);
lean_inc(x_1385);
lean_dec(x_1384);
x_1386 = l_Lean_Compiler_LCNF_Simp_simp(x_1271, x_1268, x_13, x_14, x_15, x_16, x_17, x_1385);
if (lean_obj_tag(x_1386) == 0)
{
uint8_t x_1387; 
x_1387 = !lean_is_exclusive(x_1386);
if (x_1387 == 0)
{
lean_object* x_1388; lean_object* x_1389; 
x_1388 = lean_ctor_get(x_1386, 0);
x_1389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1389, 0, x_1388);
lean_ctor_set(x_1386, 0, x_1389);
return x_1386;
}
else
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
x_1390 = lean_ctor_get(x_1386, 0);
x_1391 = lean_ctor_get(x_1386, 1);
lean_inc(x_1391);
lean_inc(x_1390);
lean_dec(x_1386);
x_1392 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1392, 0, x_1390);
x_1393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1393, 0, x_1392);
lean_ctor_set(x_1393, 1, x_1391);
return x_1393;
}
}
else
{
uint8_t x_1394; 
x_1394 = !lean_is_exclusive(x_1386);
if (x_1394 == 0)
{
return x_1386;
}
else
{
lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; 
x_1395 = lean_ctor_get(x_1386, 0);
x_1396 = lean_ctor_get(x_1386, 1);
lean_inc(x_1396);
lean_inc(x_1395);
lean_dec(x_1386);
x_1397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1397, 0, x_1395);
lean_ctor_set(x_1397, 1, x_1396);
return x_1397;
}
}
}
}
block_1379:
{
lean_object* x_1274; 
lean_dec(x_1273);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1268);
x_1274 = l_Lean_Compiler_LCNF_Simp_simp(x_1271, x_1268, x_13, x_14, x_15, x_16, x_17, x_1272);
if (lean_obj_tag(x_1274) == 0)
{
lean_object* x_1275; lean_object* x_1276; uint8_t x_1277; 
x_1275 = lean_ctor_get(x_1274, 0);
lean_inc(x_1275);
x_1276 = lean_ctor_get(x_1274, 1);
lean_inc(x_1276);
lean_dec(x_1274);
lean_inc(x_1275);
x_1277 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1275);
if (x_1277 == 0)
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
x_1278 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1276);
x_1279 = lean_ctor_get(x_1278, 1);
lean_inc(x_1279);
lean_dec(x_1278);
x_1280 = lean_ctor_get(x_5, 2);
lean_inc(x_1280);
lean_dec(x_5);
x_1281 = l_Lean_mkAppN(x_1280, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1282 = l_Lean_Compiler_LCNF_inferType(x_1281, x_14, x_15, x_16, x_17, x_1279);
if (lean_obj_tag(x_1282) == 0)
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; uint8_t x_1288; 
x_1283 = lean_ctor_get(x_1282, 0);
lean_inc(x_1283);
x_1284 = lean_ctor_get(x_1282, 1);
lean_inc(x_1284);
lean_dec(x_1282);
x_1285 = l_Lean_Compiler_LCNF_mkAuxParam(x_1283, x_1269, x_14, x_15, x_16, x_17, x_1284);
x_1286 = lean_ctor_get(x_1285, 0);
lean_inc(x_1286);
x_1287 = lean_ctor_get(x_1285, 1);
lean_inc(x_1287);
lean_dec(x_1285);
x_1288 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_1288 == 0)
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; uint8_t x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; 
lean_dec(x_10);
lean_dec(x_6);
x_1289 = lean_ctor_get(x_1286, 0);
lean_inc(x_1289);
x_1290 = lean_st_ref_get(x_17, x_1287);
x_1291 = lean_ctor_get(x_1290, 1);
lean_inc(x_1291);
lean_dec(x_1290);
x_1292 = lean_st_ref_take(x_13, x_1291);
x_1293 = lean_ctor_get(x_1292, 0);
lean_inc(x_1293);
x_1294 = lean_ctor_get(x_1292, 1);
lean_inc(x_1294);
lean_dec(x_1292);
x_1295 = lean_ctor_get(x_1293, 0);
lean_inc(x_1295);
x_1296 = l_Lean_Expr_fvar___override(x_1289);
x_1297 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1295, x_8, x_1296);
x_1298 = lean_ctor_get(x_1293, 1);
lean_inc(x_1298);
x_1299 = lean_ctor_get(x_1293, 2);
lean_inc(x_1299);
x_1300 = lean_ctor_get_uint8(x_1293, sizeof(void*)*6);
x_1301 = lean_ctor_get(x_1293, 3);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_1293, 4);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_1293, 5);
lean_inc(x_1303);
lean_dec(x_1293);
x_1304 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_1304, 0, x_1297);
lean_ctor_set(x_1304, 1, x_1298);
lean_ctor_set(x_1304, 2, x_1299);
lean_ctor_set(x_1304, 3, x_1301);
lean_ctor_set(x_1304, 4, x_1302);
lean_ctor_set(x_1304, 5, x_1303);
lean_ctor_set_uint8(x_1304, sizeof(void*)*6, x_1300);
x_1305 = lean_st_ref_set(x_13, x_1304, x_1294);
x_1306 = lean_ctor_get(x_1305, 1);
lean_inc(x_1306);
lean_dec(x_1305);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1268);
x_1307 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_1268, x_13, x_14, x_15, x_16, x_17, x_1306);
if (lean_obj_tag(x_1307) == 0)
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; 
x_1308 = lean_ctor_get(x_1307, 0);
lean_inc(x_1308);
x_1309 = lean_ctor_get(x_1307, 1);
lean_inc(x_1309);
lean_dec(x_1307);
x_1310 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1286, x_1275, x_1308, x_1268, x_13, x_14, x_15, x_16, x_17, x_1309);
lean_dec(x_13);
lean_dec(x_1268);
return x_1310;
}
else
{
uint8_t x_1311; 
lean_dec(x_1286);
lean_dec(x_1275);
lean_dec(x_1268);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_1311 = !lean_is_exclusive(x_1307);
if (x_1311 == 0)
{
return x_1307;
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
x_1312 = lean_ctor_get(x_1307, 0);
x_1313 = lean_ctor_get(x_1307, 1);
lean_inc(x_1313);
lean_inc(x_1312);
lean_dec(x_1307);
x_1314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1314, 0, x_1312);
lean_ctor_set(x_1314, 1, x_1313);
return x_1314;
}
}
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
x_1315 = lean_ctor_get(x_1286, 0);
lean_inc(x_1315);
x_1316 = l_Lean_Expr_fvar___override(x_1315);
x_1317 = lean_array_get_size(x_10);
x_1318 = l_Array_toSubarray___rarg(x_10, x_6, x_1317);
x_1319 = l_Array_ofSubarray___rarg(x_1318);
x_1320 = l_Lean_mkAppN(x_1316, x_1319);
x_1321 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1322 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1320, x_1321, x_14, x_15, x_16, x_17, x_1287);
if (lean_obj_tag(x_1322) == 0)
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; uint8_t x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
x_1323 = lean_ctor_get(x_1322, 0);
lean_inc(x_1323);
x_1324 = lean_ctor_get(x_1322, 1);
lean_inc(x_1324);
lean_dec(x_1322);
x_1325 = lean_ctor_get(x_1323, 0);
lean_inc(x_1325);
x_1326 = lean_st_ref_get(x_17, x_1324);
x_1327 = lean_ctor_get(x_1326, 1);
lean_inc(x_1327);
lean_dec(x_1326);
x_1328 = lean_st_ref_take(x_13, x_1327);
x_1329 = lean_ctor_get(x_1328, 0);
lean_inc(x_1329);
x_1330 = lean_ctor_get(x_1328, 1);
lean_inc(x_1330);
lean_dec(x_1328);
x_1331 = lean_ctor_get(x_1329, 0);
lean_inc(x_1331);
x_1332 = l_Lean_Expr_fvar___override(x_1325);
x_1333 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1331, x_8, x_1332);
x_1334 = lean_ctor_get(x_1329, 1);
lean_inc(x_1334);
x_1335 = lean_ctor_get(x_1329, 2);
lean_inc(x_1335);
x_1336 = lean_ctor_get_uint8(x_1329, sizeof(void*)*6);
x_1337 = lean_ctor_get(x_1329, 3);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1329, 4);
lean_inc(x_1338);
x_1339 = lean_ctor_get(x_1329, 5);
lean_inc(x_1339);
lean_dec(x_1329);
x_1340 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_1340, 0, x_1333);
lean_ctor_set(x_1340, 1, x_1334);
lean_ctor_set(x_1340, 2, x_1335);
lean_ctor_set(x_1340, 3, x_1337);
lean_ctor_set(x_1340, 4, x_1338);
lean_ctor_set(x_1340, 5, x_1339);
lean_ctor_set_uint8(x_1340, sizeof(void*)*6, x_1336);
x_1341 = lean_st_ref_set(x_13, x_1340, x_1330);
x_1342 = lean_ctor_get(x_1341, 1);
lean_inc(x_1342);
lean_dec(x_1341);
x_1343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1343, 0, x_1323);
lean_ctor_set(x_1343, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1268);
x_1344 = l_Lean_Compiler_LCNF_Simp_simp(x_1343, x_1268, x_13, x_14, x_15, x_16, x_17, x_1342);
if (lean_obj_tag(x_1344) == 0)
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; 
x_1345 = lean_ctor_get(x_1344, 0);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_1344, 1);
lean_inc(x_1346);
lean_dec(x_1344);
x_1347 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1286, x_1275, x_1345, x_1268, x_13, x_14, x_15, x_16, x_17, x_1346);
lean_dec(x_13);
lean_dec(x_1268);
return x_1347;
}
else
{
uint8_t x_1348; 
lean_dec(x_1286);
lean_dec(x_1275);
lean_dec(x_1268);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_1348 = !lean_is_exclusive(x_1344);
if (x_1348 == 0)
{
return x_1344;
}
else
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; 
x_1349 = lean_ctor_get(x_1344, 0);
x_1350 = lean_ctor_get(x_1344, 1);
lean_inc(x_1350);
lean_inc(x_1349);
lean_dec(x_1344);
x_1351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1351, 0, x_1349);
lean_ctor_set(x_1351, 1, x_1350);
return x_1351;
}
}
}
else
{
uint8_t x_1352; 
lean_dec(x_1286);
lean_dec(x_1275);
lean_dec(x_1268);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_1352 = !lean_is_exclusive(x_1322);
if (x_1352 == 0)
{
return x_1322;
}
else
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
x_1353 = lean_ctor_get(x_1322, 0);
x_1354 = lean_ctor_get(x_1322, 1);
lean_inc(x_1354);
lean_inc(x_1353);
lean_dec(x_1322);
x_1355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1355, 0, x_1353);
lean_ctor_set(x_1355, 1, x_1354);
return x_1355;
}
}
}
}
else
{
uint8_t x_1356; 
lean_dec(x_1275);
lean_dec(x_1268);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1356 = !lean_is_exclusive(x_1282);
if (x_1356 == 0)
{
return x_1282;
}
else
{
lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; 
x_1357 = lean_ctor_get(x_1282, 0);
x_1358 = lean_ctor_get(x_1282, 1);
lean_inc(x_1358);
lean_inc(x_1357);
lean_dec(x_1282);
x_1359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1359, 0, x_1357);
lean_ctor_set(x_1359, 1, x_1358);
return x_1359;
}
}
}
else
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
lean_dec(x_5);
lean_dec(x_4);
x_1360 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1276);
x_1361 = lean_ctor_get(x_1360, 1);
lean_inc(x_1361);
lean_dec(x_1360);
x_1362 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_1362, 0, x_1268);
lean_closure_set(x_1362, 1, x_13);
lean_closure_set(x_1362, 2, x_6);
lean_closure_set(x_1362, 3, x_7);
lean_closure_set(x_1362, 4, x_8);
lean_closure_set(x_1362, 5, x_9);
lean_closure_set(x_1362, 6, x_10);
x_1363 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1275, x_1362, x_14, x_15, x_16, x_17, x_1361);
if (lean_obj_tag(x_1363) == 0)
{
uint8_t x_1364; 
x_1364 = !lean_is_exclusive(x_1363);
if (x_1364 == 0)
{
lean_object* x_1365; lean_object* x_1366; 
x_1365 = lean_ctor_get(x_1363, 0);
x_1366 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1366, 0, x_1365);
lean_ctor_set(x_1363, 0, x_1366);
return x_1363;
}
else
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; 
x_1367 = lean_ctor_get(x_1363, 0);
x_1368 = lean_ctor_get(x_1363, 1);
lean_inc(x_1368);
lean_inc(x_1367);
lean_dec(x_1363);
x_1369 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1369, 0, x_1367);
x_1370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1370, 0, x_1369);
lean_ctor_set(x_1370, 1, x_1368);
return x_1370;
}
}
else
{
uint8_t x_1371; 
x_1371 = !lean_is_exclusive(x_1363);
if (x_1371 == 0)
{
return x_1363;
}
else
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
x_1372 = lean_ctor_get(x_1363, 0);
x_1373 = lean_ctor_get(x_1363, 1);
lean_inc(x_1373);
lean_inc(x_1372);
lean_dec(x_1363);
x_1374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1374, 0, x_1372);
lean_ctor_set(x_1374, 1, x_1373);
return x_1374;
}
}
}
}
else
{
uint8_t x_1375; 
lean_dec(x_1268);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1375 = !lean_is_exclusive(x_1274);
if (x_1375 == 0)
{
return x_1274;
}
else
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
x_1376 = lean_ctor_get(x_1274, 0);
x_1377 = lean_ctor_get(x_1274, 1);
lean_inc(x_1377);
lean_inc(x_1376);
lean_dec(x_1274);
x_1378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1378, 0, x_1376);
lean_ctor_set(x_1378, 1, x_1377);
return x_1378;
}
}
}
}
else
{
uint8_t x_1398; 
lean_dec(x_1268);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1398 = !lean_is_exclusive(x_1270);
if (x_1398 == 0)
{
return x_1270;
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
x_1399 = lean_ctor_get(x_1270, 0);
x_1400 = lean_ctor_get(x_1270, 1);
lean_inc(x_1400);
lean_inc(x_1399);
lean_dec(x_1270);
x_1401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1401, 0, x_1399);
lean_ctor_set(x_1401, 1, x_1400);
return x_1401;
}
}
}
case 10:
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; uint8_t x_1407; lean_object* x_1408; 
lean_dec(x_19);
x_1402 = lean_ctor_get(x_12, 3);
x_1403 = lean_ctor_get(x_12, 0);
x_1404 = lean_ctor_get(x_12, 1);
x_1405 = lean_ctor_get(x_12, 2);
lean_inc(x_1402);
lean_inc(x_1405);
lean_inc(x_1404);
lean_inc(x_1403);
x_1406 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1406, 0, x_1403);
lean_ctor_set(x_1406, 1, x_1404);
lean_ctor_set(x_1406, 2, x_1405);
lean_ctor_set(x_1406, 3, x_1402);
x_1407 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_1408 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_1407, x_1406, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_1408) == 0)
{
lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; uint8_t x_1518; 
x_1409 = lean_ctor_get(x_1408, 0);
lean_inc(x_1409);
x_1410 = lean_ctor_get(x_1408, 1);
lean_inc(x_1410);
lean_dec(x_1408);
x_1518 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_1518 == 0)
{
lean_object* x_1519; 
x_1519 = lean_box(0);
x_1411 = x_1519;
goto block_1517;
}
else
{
uint8_t x_1520; 
x_1520 = lean_nat_dec_eq(x_7, x_6);
if (x_1520 == 0)
{
lean_object* x_1521; 
x_1521 = lean_box(0);
x_1411 = x_1521;
goto block_1517;
}
else
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1522 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1410);
x_1523 = lean_ctor_get(x_1522, 1);
lean_inc(x_1523);
lean_dec(x_1522);
x_1524 = l_Lean_Compiler_LCNF_Simp_simp(x_1409, x_1406, x_13, x_14, x_15, x_16, x_17, x_1523);
if (lean_obj_tag(x_1524) == 0)
{
uint8_t x_1525; 
x_1525 = !lean_is_exclusive(x_1524);
if (x_1525 == 0)
{
lean_object* x_1526; lean_object* x_1527; 
x_1526 = lean_ctor_get(x_1524, 0);
x_1527 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1527, 0, x_1526);
lean_ctor_set(x_1524, 0, x_1527);
return x_1524;
}
else
{
lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; 
x_1528 = lean_ctor_get(x_1524, 0);
x_1529 = lean_ctor_get(x_1524, 1);
lean_inc(x_1529);
lean_inc(x_1528);
lean_dec(x_1524);
x_1530 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1530, 0, x_1528);
x_1531 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1531, 0, x_1530);
lean_ctor_set(x_1531, 1, x_1529);
return x_1531;
}
}
else
{
uint8_t x_1532; 
x_1532 = !lean_is_exclusive(x_1524);
if (x_1532 == 0)
{
return x_1524;
}
else
{
lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; 
x_1533 = lean_ctor_get(x_1524, 0);
x_1534 = lean_ctor_get(x_1524, 1);
lean_inc(x_1534);
lean_inc(x_1533);
lean_dec(x_1524);
x_1535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1535, 0, x_1533);
lean_ctor_set(x_1535, 1, x_1534);
return x_1535;
}
}
}
}
block_1517:
{
lean_object* x_1412; 
lean_dec(x_1411);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1406);
x_1412 = l_Lean_Compiler_LCNF_Simp_simp(x_1409, x_1406, x_13, x_14, x_15, x_16, x_17, x_1410);
if (lean_obj_tag(x_1412) == 0)
{
lean_object* x_1413; lean_object* x_1414; uint8_t x_1415; 
x_1413 = lean_ctor_get(x_1412, 0);
lean_inc(x_1413);
x_1414 = lean_ctor_get(x_1412, 1);
lean_inc(x_1414);
lean_dec(x_1412);
lean_inc(x_1413);
x_1415 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1413);
if (x_1415 == 0)
{
lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; 
x_1416 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1414);
x_1417 = lean_ctor_get(x_1416, 1);
lean_inc(x_1417);
lean_dec(x_1416);
x_1418 = lean_ctor_get(x_5, 2);
lean_inc(x_1418);
lean_dec(x_5);
x_1419 = l_Lean_mkAppN(x_1418, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1420 = l_Lean_Compiler_LCNF_inferType(x_1419, x_14, x_15, x_16, x_17, x_1417);
if (lean_obj_tag(x_1420) == 0)
{
lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; uint8_t x_1426; 
x_1421 = lean_ctor_get(x_1420, 0);
lean_inc(x_1421);
x_1422 = lean_ctor_get(x_1420, 1);
lean_inc(x_1422);
lean_dec(x_1420);
x_1423 = l_Lean_Compiler_LCNF_mkAuxParam(x_1421, x_1407, x_14, x_15, x_16, x_17, x_1422);
x_1424 = lean_ctor_get(x_1423, 0);
lean_inc(x_1424);
x_1425 = lean_ctor_get(x_1423, 1);
lean_inc(x_1425);
lean_dec(x_1423);
x_1426 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_1426 == 0)
{
lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; uint8_t x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; 
lean_dec(x_10);
lean_dec(x_6);
x_1427 = lean_ctor_get(x_1424, 0);
lean_inc(x_1427);
x_1428 = lean_st_ref_get(x_17, x_1425);
x_1429 = lean_ctor_get(x_1428, 1);
lean_inc(x_1429);
lean_dec(x_1428);
x_1430 = lean_st_ref_take(x_13, x_1429);
x_1431 = lean_ctor_get(x_1430, 0);
lean_inc(x_1431);
x_1432 = lean_ctor_get(x_1430, 1);
lean_inc(x_1432);
lean_dec(x_1430);
x_1433 = lean_ctor_get(x_1431, 0);
lean_inc(x_1433);
x_1434 = l_Lean_Expr_fvar___override(x_1427);
x_1435 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1433, x_8, x_1434);
x_1436 = lean_ctor_get(x_1431, 1);
lean_inc(x_1436);
x_1437 = lean_ctor_get(x_1431, 2);
lean_inc(x_1437);
x_1438 = lean_ctor_get_uint8(x_1431, sizeof(void*)*6);
x_1439 = lean_ctor_get(x_1431, 3);
lean_inc(x_1439);
x_1440 = lean_ctor_get(x_1431, 4);
lean_inc(x_1440);
x_1441 = lean_ctor_get(x_1431, 5);
lean_inc(x_1441);
lean_dec(x_1431);
x_1442 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_1442, 0, x_1435);
lean_ctor_set(x_1442, 1, x_1436);
lean_ctor_set(x_1442, 2, x_1437);
lean_ctor_set(x_1442, 3, x_1439);
lean_ctor_set(x_1442, 4, x_1440);
lean_ctor_set(x_1442, 5, x_1441);
lean_ctor_set_uint8(x_1442, sizeof(void*)*6, x_1438);
x_1443 = lean_st_ref_set(x_13, x_1442, x_1432);
x_1444 = lean_ctor_get(x_1443, 1);
lean_inc(x_1444);
lean_dec(x_1443);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1406);
x_1445 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_1406, x_13, x_14, x_15, x_16, x_17, x_1444);
if (lean_obj_tag(x_1445) == 0)
{
lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; 
x_1446 = lean_ctor_get(x_1445, 0);
lean_inc(x_1446);
x_1447 = lean_ctor_get(x_1445, 1);
lean_inc(x_1447);
lean_dec(x_1445);
x_1448 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1424, x_1413, x_1446, x_1406, x_13, x_14, x_15, x_16, x_17, x_1447);
lean_dec(x_13);
lean_dec(x_1406);
return x_1448;
}
else
{
uint8_t x_1449; 
lean_dec(x_1424);
lean_dec(x_1413);
lean_dec(x_1406);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_1449 = !lean_is_exclusive(x_1445);
if (x_1449 == 0)
{
return x_1445;
}
else
{
lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; 
x_1450 = lean_ctor_get(x_1445, 0);
x_1451 = lean_ctor_get(x_1445, 1);
lean_inc(x_1451);
lean_inc(x_1450);
lean_dec(x_1445);
x_1452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1452, 0, x_1450);
lean_ctor_set(x_1452, 1, x_1451);
return x_1452;
}
}
}
else
{
lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; 
x_1453 = lean_ctor_get(x_1424, 0);
lean_inc(x_1453);
x_1454 = l_Lean_Expr_fvar___override(x_1453);
x_1455 = lean_array_get_size(x_10);
x_1456 = l_Array_toSubarray___rarg(x_10, x_6, x_1455);
x_1457 = l_Array_ofSubarray___rarg(x_1456);
x_1458 = l_Lean_mkAppN(x_1454, x_1457);
x_1459 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1460 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1458, x_1459, x_14, x_15, x_16, x_17, x_1425);
if (lean_obj_tag(x_1460) == 0)
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; uint8_t x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; 
x_1461 = lean_ctor_get(x_1460, 0);
lean_inc(x_1461);
x_1462 = lean_ctor_get(x_1460, 1);
lean_inc(x_1462);
lean_dec(x_1460);
x_1463 = lean_ctor_get(x_1461, 0);
lean_inc(x_1463);
x_1464 = lean_st_ref_get(x_17, x_1462);
x_1465 = lean_ctor_get(x_1464, 1);
lean_inc(x_1465);
lean_dec(x_1464);
x_1466 = lean_st_ref_take(x_13, x_1465);
x_1467 = lean_ctor_get(x_1466, 0);
lean_inc(x_1467);
x_1468 = lean_ctor_get(x_1466, 1);
lean_inc(x_1468);
lean_dec(x_1466);
x_1469 = lean_ctor_get(x_1467, 0);
lean_inc(x_1469);
x_1470 = l_Lean_Expr_fvar___override(x_1463);
x_1471 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1469, x_8, x_1470);
x_1472 = lean_ctor_get(x_1467, 1);
lean_inc(x_1472);
x_1473 = lean_ctor_get(x_1467, 2);
lean_inc(x_1473);
x_1474 = lean_ctor_get_uint8(x_1467, sizeof(void*)*6);
x_1475 = lean_ctor_get(x_1467, 3);
lean_inc(x_1475);
x_1476 = lean_ctor_get(x_1467, 4);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1467, 5);
lean_inc(x_1477);
lean_dec(x_1467);
x_1478 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_1478, 0, x_1471);
lean_ctor_set(x_1478, 1, x_1472);
lean_ctor_set(x_1478, 2, x_1473);
lean_ctor_set(x_1478, 3, x_1475);
lean_ctor_set(x_1478, 4, x_1476);
lean_ctor_set(x_1478, 5, x_1477);
lean_ctor_set_uint8(x_1478, sizeof(void*)*6, x_1474);
x_1479 = lean_st_ref_set(x_13, x_1478, x_1468);
x_1480 = lean_ctor_get(x_1479, 1);
lean_inc(x_1480);
lean_dec(x_1479);
x_1481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1481, 0, x_1461);
lean_ctor_set(x_1481, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1406);
x_1482 = l_Lean_Compiler_LCNF_Simp_simp(x_1481, x_1406, x_13, x_14, x_15, x_16, x_17, x_1480);
if (lean_obj_tag(x_1482) == 0)
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; 
x_1483 = lean_ctor_get(x_1482, 0);
lean_inc(x_1483);
x_1484 = lean_ctor_get(x_1482, 1);
lean_inc(x_1484);
lean_dec(x_1482);
x_1485 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1424, x_1413, x_1483, x_1406, x_13, x_14, x_15, x_16, x_17, x_1484);
lean_dec(x_13);
lean_dec(x_1406);
return x_1485;
}
else
{
uint8_t x_1486; 
lean_dec(x_1424);
lean_dec(x_1413);
lean_dec(x_1406);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_1486 = !lean_is_exclusive(x_1482);
if (x_1486 == 0)
{
return x_1482;
}
else
{
lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; 
x_1487 = lean_ctor_get(x_1482, 0);
x_1488 = lean_ctor_get(x_1482, 1);
lean_inc(x_1488);
lean_inc(x_1487);
lean_dec(x_1482);
x_1489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1489, 0, x_1487);
lean_ctor_set(x_1489, 1, x_1488);
return x_1489;
}
}
}
else
{
uint8_t x_1490; 
lean_dec(x_1424);
lean_dec(x_1413);
lean_dec(x_1406);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_1490 = !lean_is_exclusive(x_1460);
if (x_1490 == 0)
{
return x_1460;
}
else
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; 
x_1491 = lean_ctor_get(x_1460, 0);
x_1492 = lean_ctor_get(x_1460, 1);
lean_inc(x_1492);
lean_inc(x_1491);
lean_dec(x_1460);
x_1493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1493, 0, x_1491);
lean_ctor_set(x_1493, 1, x_1492);
return x_1493;
}
}
}
}
else
{
uint8_t x_1494; 
lean_dec(x_1413);
lean_dec(x_1406);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1494 = !lean_is_exclusive(x_1420);
if (x_1494 == 0)
{
return x_1420;
}
else
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; 
x_1495 = lean_ctor_get(x_1420, 0);
x_1496 = lean_ctor_get(x_1420, 1);
lean_inc(x_1496);
lean_inc(x_1495);
lean_dec(x_1420);
x_1497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1497, 0, x_1495);
lean_ctor_set(x_1497, 1, x_1496);
return x_1497;
}
}
}
else
{
lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; 
lean_dec(x_5);
lean_dec(x_4);
x_1498 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1414);
x_1499 = lean_ctor_get(x_1498, 1);
lean_inc(x_1499);
lean_dec(x_1498);
x_1500 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_1500, 0, x_1406);
lean_closure_set(x_1500, 1, x_13);
lean_closure_set(x_1500, 2, x_6);
lean_closure_set(x_1500, 3, x_7);
lean_closure_set(x_1500, 4, x_8);
lean_closure_set(x_1500, 5, x_9);
lean_closure_set(x_1500, 6, x_10);
x_1501 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1413, x_1500, x_14, x_15, x_16, x_17, x_1499);
if (lean_obj_tag(x_1501) == 0)
{
uint8_t x_1502; 
x_1502 = !lean_is_exclusive(x_1501);
if (x_1502 == 0)
{
lean_object* x_1503; lean_object* x_1504; 
x_1503 = lean_ctor_get(x_1501, 0);
x_1504 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1504, 0, x_1503);
lean_ctor_set(x_1501, 0, x_1504);
return x_1501;
}
else
{
lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; 
x_1505 = lean_ctor_get(x_1501, 0);
x_1506 = lean_ctor_get(x_1501, 1);
lean_inc(x_1506);
lean_inc(x_1505);
lean_dec(x_1501);
x_1507 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1507, 0, x_1505);
x_1508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1508, 0, x_1507);
lean_ctor_set(x_1508, 1, x_1506);
return x_1508;
}
}
else
{
uint8_t x_1509; 
x_1509 = !lean_is_exclusive(x_1501);
if (x_1509 == 0)
{
return x_1501;
}
else
{
lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; 
x_1510 = lean_ctor_get(x_1501, 0);
x_1511 = lean_ctor_get(x_1501, 1);
lean_inc(x_1511);
lean_inc(x_1510);
lean_dec(x_1501);
x_1512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1512, 0, x_1510);
lean_ctor_set(x_1512, 1, x_1511);
return x_1512;
}
}
}
}
else
{
uint8_t x_1513; 
lean_dec(x_1406);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1513 = !lean_is_exclusive(x_1412);
if (x_1513 == 0)
{
return x_1412;
}
else
{
lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; 
x_1514 = lean_ctor_get(x_1412, 0);
x_1515 = lean_ctor_get(x_1412, 1);
lean_inc(x_1515);
lean_inc(x_1514);
lean_dec(x_1412);
x_1516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1516, 0, x_1514);
lean_ctor_set(x_1516, 1, x_1515);
return x_1516;
}
}
}
}
else
{
uint8_t x_1536; 
lean_dec(x_1406);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1536 = !lean_is_exclusive(x_1408);
if (x_1536 == 0)
{
return x_1408;
}
else
{
lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; 
x_1537 = lean_ctor_get(x_1408, 0);
x_1538 = lean_ctor_get(x_1408, 1);
lean_inc(x_1538);
lean_inc(x_1537);
lean_dec(x_1408);
x_1539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1539, 0, x_1537);
lean_ctor_set(x_1539, 1, x_1538);
return x_1539;
}
}
}
default: 
{
lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; uint8_t x_1545; lean_object* x_1546; 
lean_dec(x_19);
x_1540 = lean_ctor_get(x_12, 3);
x_1541 = lean_ctor_get(x_12, 0);
x_1542 = lean_ctor_get(x_12, 1);
x_1543 = lean_ctor_get(x_12, 2);
lean_inc(x_1540);
lean_inc(x_1543);
lean_inc(x_1542);
lean_inc(x_1541);
x_1544 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1544, 0, x_1541);
lean_ctor_set(x_1544, 1, x_1542);
lean_ctor_set(x_1544, 2, x_1543);
lean_ctor_set(x_1544, 3, x_1540);
x_1545 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_4);
x_1546 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_2, x_3, x_4, x_1545, x_1544, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_1546) == 0)
{
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; uint8_t x_1656; 
x_1547 = lean_ctor_get(x_1546, 0);
lean_inc(x_1547);
x_1548 = lean_ctor_get(x_1546, 1);
lean_inc(x_1548);
lean_dec(x_1546);
x_1656 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_9, x_8);
if (x_1656 == 0)
{
lean_object* x_1657; 
x_1657 = lean_box(0);
x_1549 = x_1657;
goto block_1655;
}
else
{
uint8_t x_1658; 
x_1658 = lean_nat_dec_eq(x_7, x_6);
if (x_1658 == 0)
{
lean_object* x_1659; 
x_1659 = lean_box(0);
x_1549 = x_1659;
goto block_1655;
}
else
{
lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1660 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1548);
x_1661 = lean_ctor_get(x_1660, 1);
lean_inc(x_1661);
lean_dec(x_1660);
x_1662 = l_Lean_Compiler_LCNF_Simp_simp(x_1547, x_1544, x_13, x_14, x_15, x_16, x_17, x_1661);
if (lean_obj_tag(x_1662) == 0)
{
uint8_t x_1663; 
x_1663 = !lean_is_exclusive(x_1662);
if (x_1663 == 0)
{
lean_object* x_1664; lean_object* x_1665; 
x_1664 = lean_ctor_get(x_1662, 0);
x_1665 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1665, 0, x_1664);
lean_ctor_set(x_1662, 0, x_1665);
return x_1662;
}
else
{
lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; 
x_1666 = lean_ctor_get(x_1662, 0);
x_1667 = lean_ctor_get(x_1662, 1);
lean_inc(x_1667);
lean_inc(x_1666);
lean_dec(x_1662);
x_1668 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1668, 0, x_1666);
x_1669 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1669, 0, x_1668);
lean_ctor_set(x_1669, 1, x_1667);
return x_1669;
}
}
else
{
uint8_t x_1670; 
x_1670 = !lean_is_exclusive(x_1662);
if (x_1670 == 0)
{
return x_1662;
}
else
{
lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; 
x_1671 = lean_ctor_get(x_1662, 0);
x_1672 = lean_ctor_get(x_1662, 1);
lean_inc(x_1672);
lean_inc(x_1671);
lean_dec(x_1662);
x_1673 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1673, 0, x_1671);
lean_ctor_set(x_1673, 1, x_1672);
return x_1673;
}
}
}
}
block_1655:
{
lean_object* x_1550; 
lean_dec(x_1549);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1544);
x_1550 = l_Lean_Compiler_LCNF_Simp_simp(x_1547, x_1544, x_13, x_14, x_15, x_16, x_17, x_1548);
if (lean_obj_tag(x_1550) == 0)
{
lean_object* x_1551; lean_object* x_1552; uint8_t x_1553; 
x_1551 = lean_ctor_get(x_1550, 0);
lean_inc(x_1551);
x_1552 = lean_ctor_get(x_1550, 1);
lean_inc(x_1552);
lean_dec(x_1550);
lean_inc(x_1551);
x_1553 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1551);
if (x_1553 == 0)
{
lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; 
x_1554 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1552);
x_1555 = lean_ctor_get(x_1554, 1);
lean_inc(x_1555);
lean_dec(x_1554);
x_1556 = lean_ctor_get(x_5, 2);
lean_inc(x_1556);
lean_dec(x_5);
x_1557 = l_Lean_mkAppN(x_1556, x_4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1558 = l_Lean_Compiler_LCNF_inferType(x_1557, x_14, x_15, x_16, x_17, x_1555);
if (lean_obj_tag(x_1558) == 0)
{
lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; uint8_t x_1564; 
x_1559 = lean_ctor_get(x_1558, 0);
lean_inc(x_1559);
x_1560 = lean_ctor_get(x_1558, 1);
lean_inc(x_1560);
lean_dec(x_1558);
x_1561 = l_Lean_Compiler_LCNF_mkAuxParam(x_1559, x_1545, x_14, x_15, x_16, x_17, x_1560);
x_1562 = lean_ctor_get(x_1561, 0);
lean_inc(x_1562);
x_1563 = lean_ctor_get(x_1561, 1);
lean_inc(x_1563);
lean_dec(x_1561);
x_1564 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_1564 == 0)
{
lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; uint8_t x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; 
lean_dec(x_10);
lean_dec(x_6);
x_1565 = lean_ctor_get(x_1562, 0);
lean_inc(x_1565);
x_1566 = lean_st_ref_get(x_17, x_1563);
x_1567 = lean_ctor_get(x_1566, 1);
lean_inc(x_1567);
lean_dec(x_1566);
x_1568 = lean_st_ref_take(x_13, x_1567);
x_1569 = lean_ctor_get(x_1568, 0);
lean_inc(x_1569);
x_1570 = lean_ctor_get(x_1568, 1);
lean_inc(x_1570);
lean_dec(x_1568);
x_1571 = lean_ctor_get(x_1569, 0);
lean_inc(x_1571);
x_1572 = l_Lean_Expr_fvar___override(x_1565);
x_1573 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1571, x_8, x_1572);
x_1574 = lean_ctor_get(x_1569, 1);
lean_inc(x_1574);
x_1575 = lean_ctor_get(x_1569, 2);
lean_inc(x_1575);
x_1576 = lean_ctor_get_uint8(x_1569, sizeof(void*)*6);
x_1577 = lean_ctor_get(x_1569, 3);
lean_inc(x_1577);
x_1578 = lean_ctor_get(x_1569, 4);
lean_inc(x_1578);
x_1579 = lean_ctor_get(x_1569, 5);
lean_inc(x_1579);
lean_dec(x_1569);
x_1580 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_1580, 0, x_1573);
lean_ctor_set(x_1580, 1, x_1574);
lean_ctor_set(x_1580, 2, x_1575);
lean_ctor_set(x_1580, 3, x_1577);
lean_ctor_set(x_1580, 4, x_1578);
lean_ctor_set(x_1580, 5, x_1579);
lean_ctor_set_uint8(x_1580, sizeof(void*)*6, x_1576);
x_1581 = lean_st_ref_set(x_13, x_1580, x_1570);
x_1582 = lean_ctor_get(x_1581, 1);
lean_inc(x_1582);
lean_dec(x_1581);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1544);
x_1583 = l_Lean_Compiler_LCNF_Simp_simp(x_9, x_1544, x_13, x_14, x_15, x_16, x_17, x_1582);
if (lean_obj_tag(x_1583) == 0)
{
lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; 
x_1584 = lean_ctor_get(x_1583, 0);
lean_inc(x_1584);
x_1585 = lean_ctor_get(x_1583, 1);
lean_inc(x_1585);
lean_dec(x_1583);
x_1586 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1562, x_1551, x_1584, x_1544, x_13, x_14, x_15, x_16, x_17, x_1585);
lean_dec(x_13);
lean_dec(x_1544);
return x_1586;
}
else
{
uint8_t x_1587; 
lean_dec(x_1562);
lean_dec(x_1551);
lean_dec(x_1544);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_1587 = !lean_is_exclusive(x_1583);
if (x_1587 == 0)
{
return x_1583;
}
else
{
lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; 
x_1588 = lean_ctor_get(x_1583, 0);
x_1589 = lean_ctor_get(x_1583, 1);
lean_inc(x_1589);
lean_inc(x_1588);
lean_dec(x_1583);
x_1590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1590, 0, x_1588);
lean_ctor_set(x_1590, 1, x_1589);
return x_1590;
}
}
}
else
{
lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; 
x_1591 = lean_ctor_get(x_1562, 0);
lean_inc(x_1591);
x_1592 = l_Lean_Expr_fvar___override(x_1591);
x_1593 = lean_array_get_size(x_10);
x_1594 = l_Array_toSubarray___rarg(x_10, x_6, x_1593);
x_1595 = l_Array_ofSubarray___rarg(x_1594);
x_1596 = l_Lean_mkAppN(x_1592, x_1595);
x_1597 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1598 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1596, x_1597, x_14, x_15, x_16, x_17, x_1563);
if (lean_obj_tag(x_1598) == 0)
{
lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; uint8_t x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; 
x_1599 = lean_ctor_get(x_1598, 0);
lean_inc(x_1599);
x_1600 = lean_ctor_get(x_1598, 1);
lean_inc(x_1600);
lean_dec(x_1598);
x_1601 = lean_ctor_get(x_1599, 0);
lean_inc(x_1601);
x_1602 = lean_st_ref_get(x_17, x_1600);
x_1603 = lean_ctor_get(x_1602, 1);
lean_inc(x_1603);
lean_dec(x_1602);
x_1604 = lean_st_ref_take(x_13, x_1603);
x_1605 = lean_ctor_get(x_1604, 0);
lean_inc(x_1605);
x_1606 = lean_ctor_get(x_1604, 1);
lean_inc(x_1606);
lean_dec(x_1604);
x_1607 = lean_ctor_get(x_1605, 0);
lean_inc(x_1607);
x_1608 = l_Lean_Expr_fvar___override(x_1601);
x_1609 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1607, x_8, x_1608);
x_1610 = lean_ctor_get(x_1605, 1);
lean_inc(x_1610);
x_1611 = lean_ctor_get(x_1605, 2);
lean_inc(x_1611);
x_1612 = lean_ctor_get_uint8(x_1605, sizeof(void*)*6);
x_1613 = lean_ctor_get(x_1605, 3);
lean_inc(x_1613);
x_1614 = lean_ctor_get(x_1605, 4);
lean_inc(x_1614);
x_1615 = lean_ctor_get(x_1605, 5);
lean_inc(x_1615);
lean_dec(x_1605);
x_1616 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_1616, 0, x_1609);
lean_ctor_set(x_1616, 1, x_1610);
lean_ctor_set(x_1616, 2, x_1611);
lean_ctor_set(x_1616, 3, x_1613);
lean_ctor_set(x_1616, 4, x_1614);
lean_ctor_set(x_1616, 5, x_1615);
lean_ctor_set_uint8(x_1616, sizeof(void*)*6, x_1612);
x_1617 = lean_st_ref_set(x_13, x_1616, x_1606);
x_1618 = lean_ctor_get(x_1617, 1);
lean_inc(x_1618);
lean_dec(x_1617);
x_1619 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1619, 0, x_1599);
lean_ctor_set(x_1619, 1, x_9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_1544);
x_1620 = l_Lean_Compiler_LCNF_Simp_simp(x_1619, x_1544, x_13, x_14, x_15, x_16, x_17, x_1618);
if (lean_obj_tag(x_1620) == 0)
{
lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; 
x_1621 = lean_ctor_get(x_1620, 0);
lean_inc(x_1621);
x_1622 = lean_ctor_get(x_1620, 1);
lean_inc(x_1622);
lean_dec(x_1620);
x_1623 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1562, x_1551, x_1621, x_1544, x_13, x_14, x_15, x_16, x_17, x_1622);
lean_dec(x_13);
lean_dec(x_1544);
return x_1623;
}
else
{
uint8_t x_1624; 
lean_dec(x_1562);
lean_dec(x_1551);
lean_dec(x_1544);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_1624 = !lean_is_exclusive(x_1620);
if (x_1624 == 0)
{
return x_1620;
}
else
{
lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; 
x_1625 = lean_ctor_get(x_1620, 0);
x_1626 = lean_ctor_get(x_1620, 1);
lean_inc(x_1626);
lean_inc(x_1625);
lean_dec(x_1620);
x_1627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1627, 0, x_1625);
lean_ctor_set(x_1627, 1, x_1626);
return x_1627;
}
}
}
else
{
uint8_t x_1628; 
lean_dec(x_1562);
lean_dec(x_1551);
lean_dec(x_1544);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_1628 = !lean_is_exclusive(x_1598);
if (x_1628 == 0)
{
return x_1598;
}
else
{
lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; 
x_1629 = lean_ctor_get(x_1598, 0);
x_1630 = lean_ctor_get(x_1598, 1);
lean_inc(x_1630);
lean_inc(x_1629);
lean_dec(x_1598);
x_1631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1631, 0, x_1629);
lean_ctor_set(x_1631, 1, x_1630);
return x_1631;
}
}
}
}
else
{
uint8_t x_1632; 
lean_dec(x_1551);
lean_dec(x_1544);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1632 = !lean_is_exclusive(x_1558);
if (x_1632 == 0)
{
return x_1558;
}
else
{
lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; 
x_1633 = lean_ctor_get(x_1558, 0);
x_1634 = lean_ctor_get(x_1558, 1);
lean_inc(x_1634);
lean_inc(x_1633);
lean_dec(x_1558);
x_1635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1635, 0, x_1633);
lean_ctor_set(x_1635, 1, x_1634);
return x_1635;
}
}
}
else
{
lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; 
lean_dec(x_5);
lean_dec(x_4);
x_1636 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_13, x_14, x_15, x_16, x_17, x_1552);
x_1637 = lean_ctor_get(x_1636, 1);
lean_inc(x_1637);
lean_dec(x_1636);
x_1638 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 13, 7);
lean_closure_set(x_1638, 0, x_1544);
lean_closure_set(x_1638, 1, x_13);
lean_closure_set(x_1638, 2, x_6);
lean_closure_set(x_1638, 3, x_7);
lean_closure_set(x_1638, 4, x_8);
lean_closure_set(x_1638, 5, x_9);
lean_closure_set(x_1638, 6, x_10);
x_1639 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1551, x_1638, x_14, x_15, x_16, x_17, x_1637);
if (lean_obj_tag(x_1639) == 0)
{
uint8_t x_1640; 
x_1640 = !lean_is_exclusive(x_1639);
if (x_1640 == 0)
{
lean_object* x_1641; lean_object* x_1642; 
x_1641 = lean_ctor_get(x_1639, 0);
x_1642 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1642, 0, x_1641);
lean_ctor_set(x_1639, 0, x_1642);
return x_1639;
}
else
{
lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; 
x_1643 = lean_ctor_get(x_1639, 0);
x_1644 = lean_ctor_get(x_1639, 1);
lean_inc(x_1644);
lean_inc(x_1643);
lean_dec(x_1639);
x_1645 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1645, 0, x_1643);
x_1646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1646, 0, x_1645);
lean_ctor_set(x_1646, 1, x_1644);
return x_1646;
}
}
else
{
uint8_t x_1647; 
x_1647 = !lean_is_exclusive(x_1639);
if (x_1647 == 0)
{
return x_1639;
}
else
{
lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; 
x_1648 = lean_ctor_get(x_1639, 0);
x_1649 = lean_ctor_get(x_1639, 1);
lean_inc(x_1649);
lean_inc(x_1648);
lean_dec(x_1639);
x_1650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1650, 0, x_1648);
lean_ctor_set(x_1650, 1, x_1649);
return x_1650;
}
}
}
}
else
{
uint8_t x_1651; 
lean_dec(x_1544);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1651 = !lean_is_exclusive(x_1550);
if (x_1651 == 0)
{
return x_1550;
}
else
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; 
x_1652 = lean_ctor_get(x_1550, 0);
x_1653 = lean_ctor_get(x_1550, 1);
lean_inc(x_1653);
lean_inc(x_1652);
lean_dec(x_1550);
x_1654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1654, 0, x_1652);
lean_ctor_set(x_1654, 1, x_1653);
return x_1654;
}
}
}
}
else
{
uint8_t x_1674; 
lean_dec(x_1544);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1674 = !lean_is_exclusive(x_1546);
if (x_1674 == 0)
{
return x_1546;
}
else
{
lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; 
x_1675 = lean_ctor_get(x_1546, 0);
x_1676 = lean_ctor_get(x_1546, 1);
lean_inc(x_1676);
lean_inc(x_1675);
lean_dec(x_1546);
x_1677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1677, 0, x_1675);
lean_ctor_set(x_1677, 1, x_1676);
return x_1677;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 3);
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get(x_6, 2);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
lean_inc(x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_2, x_20, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_st_ref_get(x_11, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_take(x_7, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = l_Lean_Expr_fvar___override(x_24);
x_32 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_30, x_3, x_31);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 2);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_28, sizeof(void*)*6);
x_36 = lean_ctor_get(x_28, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_28, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_28, 5);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_37);
lean_ctor_set(x_39, 5, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*6, x_35);
x_40 = lean_st_ref_set(x_7, x_39, x_29);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_7, x_8, x_9, x_10, x_11, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_22);
lean_ctor_set(x_44, 1, x_4);
x_45 = l_Lean_Compiler_LCNF_Simp_simp(x_44, x_20, x_7, x_8, x_9, x_10, x_11, x_43);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_45);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
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
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_45, 0);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
return x_21;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_21, 0);
x_59 = lean_ctor_get(x_21, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_21);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_13);
x_61 = lean_ctor_get(x_6, 3);
x_62 = lean_ctor_get(x_6, 0);
x_63 = lean_ctor_get(x_6, 1);
x_64 = lean_ctor_get(x_6, 2);
lean_inc(x_61);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_65, 3, x_61);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_66 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_2, x_65, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_st_ref_get(x_11, x_68);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_st_ref_take(x_7, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = l_Lean_Expr_fvar___override(x_69);
x_77 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_75, x_3, x_76);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 2);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_73, sizeof(void*)*6);
x_81 = lean_ctor_get(x_73, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_73, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_73, 5);
lean_inc(x_83);
lean_dec(x_73);
x_84 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set(x_84, 2, x_79);
lean_ctor_set(x_84, 3, x_81);
lean_ctor_set(x_84, 4, x_82);
lean_ctor_set(x_84, 5, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*6, x_80);
x_85 = lean_st_ref_set(x_7, x_84, x_74);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_7, x_8, x_9, x_10, x_11, x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_67);
lean_ctor_set(x_89, 1, x_4);
x_90 = l_Lean_Compiler_LCNF_Simp_simp(x_89, x_65, x_7, x_8, x_9, x_10, x_11, x_88);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_90, 0);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_90);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_90);
if (x_98 == 0)
{
return x_90;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_90, 0);
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_90);
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
lean_dec(x_65);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_66);
if (x_102 == 0)
{
return x_66;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_66, 0);
x_104 = lean_ctor_get(x_66, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_66);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inline", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__4;
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inlining ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_20);
x_25 = lean_nat_dec_lt(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
x_28 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
lean_inc(x_21);
x_29 = l_Array_toSubarray___rarg(x_21, x_28, x_24);
x_30 = l_Array_ofSubarray___rarg(x_29);
x_31 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__6;
x_32 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(x_10, x_26, x_27, x_30, x_20, x_24, x_22, x_23, x_2, x_21, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_3);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
lean_inc(x_10);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_10);
x_40 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__8;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__10;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining___spec__2(x_31, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(x_10, x_26, x_27, x_30, x_20, x_24, x_22, x_23, x_2, x_21, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_3);
lean_dec(x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
x_48 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__6;
x_49 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_box(0);
x_54 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5(x_10, x_20, x_23, x_2, x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_3);
lean_dec(x_10);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
lean_inc(x_10);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_10);
x_57 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__8;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__10;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining___spec__2(x_48, x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_55);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5(x_10, x_20, x_23, x_2, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
lean_dec(x_3);
lean_dec(x_62);
lean_dec(x_10);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_11);
if (x_65 == 0)
{
return x_11;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_11, 0);
x_67 = lean_ctor_get(x_11, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_11);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_fget(x_3, x_2);
x_15 = lean_box(x_6);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_16 = lean_apply_8(x_1, x_14, x_4, x_5, x_15, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ptr_addr(x_14);
lean_dec(x_14);
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
x_10 = x_18;
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
x_10 = x_18;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(x_2, x_10, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_fget(x_3, x_2);
x_15 = lean_box(x_6);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_16 = lean_apply_8(x_1, x_14, x_4, x_5, x_15, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ptr_addr(x_14);
lean_dec(x_14);
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
x_10 = x_18;
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
x_10 = x_18;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7(x_2, x_10, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_13 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_4, 3);
lean_inc(x_16);
x_17 = l_Lean_Expr_isFVar(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_4);
x_18 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_4, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_24 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
x_28 = l_Lean_Compiler_LCNF_Simp_isUsed(x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_25);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
lean_inc(x_4);
x_38 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; size_t x_41; size_t x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_42 = lean_ptr_addr(x_25);
x_43 = lean_usize_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_25);
lean_ctor_set(x_38, 0, x_44);
return x_38;
}
else
{
size_t x_45; size_t x_46; uint8_t x_47; 
x_45 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_46 = lean_ptr_addr(x_4);
x_47 = lean_usize_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_25);
lean_ctor_set(x_38, 0, x_48);
return x_38;
}
else
{
lean_dec(x_25);
lean_dec(x_4);
lean_ctor_set(x_38, 0, x_3);
return x_38;
}
}
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_dec(x_38);
x_50 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_51 = lean_ptr_addr(x_25);
x_52 = lean_usize_dec_eq(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_25);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
else
{
size_t x_55; size_t x_56; uint8_t x_57; 
x_55 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_56 = lean_ptr_addr(x_4);
x_57 = lean_usize_dec_eq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_3);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_25);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_49);
return x_59;
}
else
{
lean_object* x_60; 
lean_dec(x_25);
lean_dec(x_4);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_3);
lean_ctor_set(x_60, 1, x_49);
return x_60;
}
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
return x_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_ctor_get(x_22, 0);
lean_inc(x_65);
lean_dec(x_22);
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
lean_dec(x_21);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_ctor_get(x_4, 0);
lean_inc(x_69);
x_70 = lean_st_ref_get(x_11, x_66);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_st_ref_take(x_7, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_73, 0);
x_77 = l_Lean_Expr_fvar___override(x_68);
x_78 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_76, x_69, x_77);
lean_ctor_set(x_73, 0, x_78);
x_79 = lean_st_ref_set(x_7, x_73, x_74);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_80);
lean_dec(x_4);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_83 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_67, x_84, x_6, x_7, x_8, x_9, x_10, x_11, x_85);
lean_dec(x_67);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_67);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_83);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_91 = lean_ctor_get(x_73, 0);
x_92 = lean_ctor_get(x_73, 1);
x_93 = lean_ctor_get(x_73, 2);
x_94 = lean_ctor_get_uint8(x_73, sizeof(void*)*6);
x_95 = lean_ctor_get(x_73, 3);
x_96 = lean_ctor_get(x_73, 4);
x_97 = lean_ctor_get(x_73, 5);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_73);
x_98 = l_Lean_Expr_fvar___override(x_68);
x_99 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_91, x_69, x_98);
x_100 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_92);
lean_ctor_set(x_100, 2, x_93);
lean_ctor_set(x_100, 3, x_95);
lean_ctor_set(x_100, 4, x_96);
lean_ctor_set(x_100, 5, x_97);
lean_ctor_set_uint8(x_100, sizeof(void*)*6, x_94);
x_101 = lean_st_ref_set(x_7, x_100, x_74);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_102);
lean_dec(x_4);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_105 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_67, x_106, x_6, x_7, x_8, x_9, x_10, x_11, x_107);
lean_dec(x_67);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_67);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_111 = x_105;
} else {
 lean_dec_ref(x_105);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_21);
if (x_113 == 0)
{
return x_21;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_21, 0);
x_115 = lean_ctor_get(x_21, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_21);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_ctor_get(x_18, 1);
lean_inc(x_117);
lean_dec(x_18);
x_118 = lean_ctor_get(x_19, 0);
lean_inc(x_118);
lean_dec(x_19);
x_119 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_117);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_119, 0);
lean_dec(x_121);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_18);
if (x_124 == 0)
{
return x_18;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_18, 0);
x_126 = lean_ctor_get(x_18, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_18);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_3);
lean_dec(x_2);
x_128 = lean_ctor_get(x_4, 0);
lean_inc(x_128);
x_129 = l_Lean_Expr_fvarId_x21(x_16);
x_130 = lean_st_ref_get(x_11, x_15);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_st_ref_take(x_7, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = !lean_is_exclusive(x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = lean_ctor_get(x_133, 0);
x_137 = l_Lean_Expr_fvar___override(x_129);
x_138 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_136, x_128, x_137);
lean_ctor_set(x_133, 0, x_138);
x_139 = lean_st_ref_set(x_7, x_133, x_134);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_140);
lean_dec(x_4);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
x_143 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_142);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_144 = lean_ctor_get(x_133, 0);
x_145 = lean_ctor_get(x_133, 1);
x_146 = lean_ctor_get(x_133, 2);
x_147 = lean_ctor_get_uint8(x_133, sizeof(void*)*6);
x_148 = lean_ctor_get(x_133, 3);
x_149 = lean_ctor_get(x_133, 4);
x_150 = lean_ctor_get(x_133, 5);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_133);
x_151 = l_Lean_Expr_fvar___override(x_129);
x_152 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_144, x_128, x_151);
x_153 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_145);
lean_ctor_set(x_153, 2, x_146);
lean_ctor_set(x_153, 3, x_148);
lean_ctor_set(x_153, 4, x_149);
lean_ctor_set(x_153, 5, x_150);
lean_ctor_set_uint8(x_153, sizeof(void*)*6, x_147);
x_154 = lean_st_ref_set(x_7, x_153, x_134);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_155);
lean_dec(x_4);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_158 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_157);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_159 = lean_ctor_get(x_13, 1);
lean_inc(x_159);
lean_dec(x_13);
x_160 = lean_ctor_get(x_14, 0);
lean_inc(x_160);
lean_dec(x_14);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_1);
x_162 = l_Lean_Compiler_LCNF_Simp_simp(x_161, x_6, x_7, x_8, x_9, x_10, x_11, x_159);
return x_162;
}
}
else
{
uint8_t x_163; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_13);
if (x_163 == 0)
{
return x_13;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_13, 0);
x_165 = lean_ctor_get(x_13, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_13);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_box(x_6);
x_16 = lean_apply_9(x_1, x_12, x_14, x_4, x_5, x_15, x_7, x_8, x_9, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___boxed), 8, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed), 9, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___spec__1___rarg___boxed), 9, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg(x_1, x_10, x_11, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
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
x_44 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_42);
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
case 1:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_35, 1);
lean_inc(x_56);
lean_dec(x_35);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
lean_inc(x_1);
lean_inc(x_57);
x_64 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed), 13, 4);
lean_closure_set(x_64, 0, x_58);
lean_closure_set(x_64, 1, x_57);
lean_closure_set(x_64, 2, x_1);
lean_closure_set(x_64, 3, x_61);
x_65 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(0);
x_67 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_64, x_57, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_63);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_57, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_57, 2);
lean_inc(x_69);
x_70 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_68, x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_box(0);
x_72 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_64, x_57, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_63);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_73 = lean_st_ref_get(x_7, x_63);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_st_ref_get(x_3, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
x_79 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_80 = l_Lean_Compiler_LCNF_normFunDeclImp(x_79, x_57, x_78, x_4, x_5, x_6, x_7, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_83 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_81, x_4, x_5, x_6, x_7, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_64, x_84, x_87, x_2, x_3, x_4, x_5, x_6, x_7, x_88);
lean_dec(x_87);
return x_89;
}
else
{
uint8_t x_90; 
lean_dec(x_64);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_83);
if (x_90 == 0)
{
return x_83;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_83, 0);
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_83);
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
lean_dec(x_64);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_80);
if (x_94 == 0)
{
return x_80;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_80, 0);
x_96 = lean_ctor_get(x_80, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_80);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_98 = lean_ctor_get(x_60, 1);
lean_inc(x_98);
lean_dec(x_60);
x_99 = lean_st_ref_get(x_7, x_98);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_st_ref_get(x_3, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
lean_dec(x_102);
x_105 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_57);
x_106 = l_Lean_Compiler_LCNF_normFunDeclImp(x_105, x_57, x_104, x_4, x_5, x_6, x_7, x_103);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_box(0);
x_110 = lean_unbox(x_61);
lean_dec(x_61);
x_111 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_58, x_57, x_1, x_110, x_107, x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_108);
return x_111;
}
else
{
uint8_t x_112; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_106);
if (x_112 == 0)
{
return x_106;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_106, 0);
x_114 = lean_ctor_get(x_106, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_106);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
case 2:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_116 = lean_ctor_get(x_35, 1);
lean_inc(x_116);
lean_dec(x_35);
x_117 = lean_ctor_get(x_1, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_1, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
x_120 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_119, x_2, x_3, x_4, x_5, x_6, x_7, x_116);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_1);
lean_inc(x_117);
x_124 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 13, 4);
lean_closure_set(x_124, 0, x_118);
lean_closure_set(x_124, 1, x_117);
lean_closure_set(x_124, 2, x_1);
lean_closure_set(x_124, 3, x_121);
x_125 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_box(0);
x_127 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_124, x_117, x_126, x_2, x_3, x_4, x_5, x_6, x_7, x_123);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_128 = lean_ctor_get(x_117, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_117, 2);
lean_inc(x_129);
x_130 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_128, x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_box(0);
x_132 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_124, x_117, x_131, x_2, x_3, x_4, x_5, x_6, x_7, x_123);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_133 = lean_st_ref_get(x_7, x_123);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_st_ref_get(x_3, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
lean_dec(x_136);
x_139 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_140 = l_Lean_Compiler_LCNF_normFunDeclImp(x_139, x_117, x_138, x_4, x_5, x_6, x_7, x_137);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_143 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_141, x_4, x_5, x_6, x_7, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_124, x_144, x_147, x_2, x_3, x_4, x_5, x_6, x_7, x_148);
lean_dec(x_147);
return x_149;
}
else
{
uint8_t x_150; 
lean_dec(x_124);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_150 = !lean_is_exclusive(x_143);
if (x_150 == 0)
{
return x_143;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_143, 0);
x_152 = lean_ctor_get(x_143, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_143);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_124);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_154 = !lean_is_exclusive(x_140);
if (x_154 == 0)
{
return x_140;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_140, 0);
x_156 = lean_ctor_get(x_140, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_140);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; 
x_158 = lean_ctor_get(x_120, 1);
lean_inc(x_158);
lean_dec(x_120);
x_159 = lean_st_ref_get(x_7, x_158);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_st_ref_get(x_3, x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
lean_dec(x_162);
x_165 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_117);
x_166 = l_Lean_Compiler_LCNF_normFunDeclImp(x_165, x_117, x_164, x_4, x_5, x_6, x_7, x_163);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_box(0);
x_170 = lean_unbox(x_121);
lean_dec(x_121);
x_171 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_118, x_117, x_1, x_170, x_167, x_169, x_2, x_3, x_4, x_5, x_6, x_7, x_168);
return x_171;
}
else
{
uint8_t x_172; 
lean_dec(x_121);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_166);
if (x_172 == 0)
{
return x_166;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_166, 0);
x_174 = lean_ctor_get(x_166, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_166);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
case 3:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; 
x_176 = lean_ctor_get(x_35, 1);
lean_inc(x_176);
lean_dec(x_35);
x_177 = lean_ctor_get(x_1, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_1, 1);
lean_inc(x_178);
x_179 = lean_st_ref_get(x_7, x_176);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_st_ref_get(x_3, x_180);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
lean_dec(x_182);
x_185 = 0;
lean_inc(x_177);
x_186 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_184, x_177, x_185);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_178);
x_187 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_185, x_178, x_2, x_3, x_4, x_5, x_6, x_7, x_183);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_210; 
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_188);
lean_inc(x_186);
x_210 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_186, x_188, x_2, x_3, x_4, x_5, x_6, x_7, x_189);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
lean_inc(x_186);
x_213 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_186, x_2, x_3, x_4, x_5, x_6, x_7, x_212);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_array_get_size(x_188);
x_216 = lean_unsigned_to_nat(0u);
x_217 = lean_nat_dec_lt(x_216, x_215);
if (x_217 == 0)
{
lean_dec(x_215);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_191 = x_214;
goto block_209;
}
else
{
uint8_t x_218; 
x_218 = lean_nat_dec_le(x_215, x_215);
if (x_218 == 0)
{
lean_dec(x_215);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_191 = x_214;
goto block_209;
}
else
{
size_t x_219; size_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = 0;
x_220 = lean_usize_of_nat(x_215);
lean_dec(x_215);
x_221 = lean_box(0);
x_222 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_188, x_219, x_220, x_221, x_2, x_3, x_4, x_5, x_6, x_7, x_214);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_191 = x_223;
goto block_209;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_190);
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_1);
x_224 = lean_ctor_get(x_210, 1);
lean_inc(x_224);
lean_dec(x_210);
x_225 = lean_ctor_get(x_211, 0);
lean_inc(x_225);
lean_dec(x_211);
x_1 = x_225;
x_8 = x_224;
goto _start;
}
}
else
{
uint8_t x_227; 
lean_dec(x_190);
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_227 = !lean_is_exclusive(x_210);
if (x_227 == 0)
{
return x_210;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_210, 0);
x_229 = lean_ctor_get(x_210, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_210);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
block_209:
{
uint8_t x_192; 
x_192 = lean_name_eq(x_177, x_186);
lean_dec(x_177);
if (x_192 == 0)
{
uint8_t x_193; 
lean_dec(x_178);
x_193 = !lean_is_exclusive(x_1);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_1, 1);
lean_dec(x_194);
x_195 = lean_ctor_get(x_1, 0);
lean_dec(x_195);
lean_ctor_set(x_1, 1, x_188);
lean_ctor_set(x_1, 0, x_186);
if (lean_is_scalar(x_190)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_190;
}
lean_ctor_set(x_196, 0, x_1);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_1);
x_197 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_197, 0, x_186);
lean_ctor_set(x_197, 1, x_188);
if (lean_is_scalar(x_190)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_190;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_191);
return x_198;
}
}
else
{
size_t x_199; size_t x_200; uint8_t x_201; 
x_199 = lean_ptr_addr(x_178);
lean_dec(x_178);
x_200 = lean_ptr_addr(x_188);
x_201 = lean_usize_dec_eq(x_199, x_200);
if (x_201 == 0)
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_1);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_1, 1);
lean_dec(x_203);
x_204 = lean_ctor_get(x_1, 0);
lean_dec(x_204);
lean_ctor_set(x_1, 1, x_188);
lean_ctor_set(x_1, 0, x_186);
if (lean_is_scalar(x_190)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_190;
}
lean_ctor_set(x_205, 0, x_1);
lean_ctor_set(x_205, 1, x_191);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_1);
x_206 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_206, 0, x_186);
lean_ctor_set(x_206, 1, x_188);
if (lean_is_scalar(x_190)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_190;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_191);
return x_207;
}
}
else
{
lean_object* x_208; 
lean_dec(x_188);
lean_dec(x_186);
if (lean_is_scalar(x_190)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_190;
}
lean_ctor_set(x_208, 0, x_1);
lean_ctor_set(x_208, 1, x_191);
return x_208;
}
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_186);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_187);
if (x_231 == 0)
{
return x_187;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_187, 0);
x_233 = lean_ctor_get(x_187, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_187);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
case 4:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_35, 1);
lean_inc(x_235);
lean_dec(x_35);
x_236 = lean_ctor_get(x_1, 0);
lean_inc(x_236);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_236);
x_237 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_236, x_2, x_3, x_4, x_5, x_6, x_7, x_235);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_ctor_get(x_236, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_236, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_236, 2);
lean_inc(x_242);
x_243 = lean_ctor_get(x_236, 3);
lean_inc(x_243);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 lean_ctor_release(x_236, 3);
 x_244 = x_236;
} else {
 lean_dec_ref(x_236);
 x_244 = lean_box(0);
}
x_245 = lean_st_ref_get(x_7, x_239);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
x_247 = lean_st_ref_get(x_3, x_246);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
lean_dec(x_248);
x_251 = 0;
lean_inc(x_242);
x_252 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_250, x_242, x_251);
x_253 = lean_st_ref_get(x_7, x_249);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_255 = lean_st_ref_get(x_3, x_254);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
lean_dec(x_256);
lean_inc(x_241);
x_259 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_258, x_251, x_241);
lean_inc(x_252);
x_260 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_252, x_2, x_3, x_4, x_5, x_6, x_7, x_257);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
lean_inc(x_252);
x_262 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__8___boxed), 9, 1);
lean_closure_set(x_262, 0, x_252);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_243);
x_263 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_243, x_262, x_2, x_3, x_4, x_5, x_6, x_7, x_261);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_266 = x_263;
} else {
 lean_dec_ref(x_263);
 x_266 = lean_box(0);
}
x_267 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_264, x_2, x_3, x_4, x_5, x_6, x_7, x_265);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_302; lean_object* x_303; uint8_t x_314; 
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
x_302 = lean_array_get_size(x_268);
x_314 = lean_nat_dec_eq(x_302, x_33);
if (x_314 == 0)
{
lean_object* x_315; 
lean_dec(x_302);
lean_dec(x_266);
x_315 = lean_box(0);
x_271 = x_315;
goto block_301;
}
else
{
lean_object* x_316; uint8_t x_317; 
x_316 = lean_unsigned_to_nat(0u);
x_317 = lean_nat_dec_lt(x_316, x_302);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; 
x_318 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__9;
x_319 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_318);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; 
lean_dec(x_319);
lean_dec(x_302);
lean_dec(x_266);
x_320 = lean_box(0);
x_271 = x_320;
goto block_301;
}
else
{
lean_object* x_321; 
lean_dec(x_319);
lean_dec(x_270);
lean_dec(x_259);
lean_dec(x_252);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_1);
x_321 = lean_box(0);
x_303 = x_321;
goto block_313;
}
}
else
{
lean_object* x_322; 
x_322 = lean_array_fget(x_268, x_316);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; 
lean_dec(x_322);
lean_dec(x_302);
lean_dec(x_266);
x_323 = lean_box(0);
x_271 = x_323;
goto block_301;
}
else
{
lean_object* x_324; 
lean_dec(x_322);
lean_dec(x_270);
lean_dec(x_259);
lean_dec(x_252);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_1);
x_324 = lean_box(0);
x_303 = x_324;
goto block_313;
}
}
}
block_301:
{
size_t x_272; size_t x_273; uint8_t x_274; 
lean_dec(x_271);
x_272 = lean_ptr_addr(x_243);
lean_dec(x_243);
x_273 = lean_ptr_addr(x_268);
x_274 = lean_usize_dec_eq(x_272, x_273);
if (x_274 == 0)
{
uint8_t x_275; 
lean_dec(x_242);
lean_dec(x_241);
x_275 = !lean_is_exclusive(x_1);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_1, 0);
lean_dec(x_276);
if (lean_is_scalar(x_244)) {
 x_277 = lean_alloc_ctor(0, 4, 0);
} else {
 x_277 = x_244;
}
lean_ctor_set(x_277, 0, x_240);
lean_ctor_set(x_277, 1, x_259);
lean_ctor_set(x_277, 2, x_252);
lean_ctor_set(x_277, 3, x_268);
lean_ctor_set(x_1, 0, x_277);
if (lean_is_scalar(x_270)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_270;
}
lean_ctor_set(x_278, 0, x_1);
lean_ctor_set(x_278, 1, x_269);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_1);
if (lean_is_scalar(x_244)) {
 x_279 = lean_alloc_ctor(0, 4, 0);
} else {
 x_279 = x_244;
}
lean_ctor_set(x_279, 0, x_240);
lean_ctor_set(x_279, 1, x_259);
lean_ctor_set(x_279, 2, x_252);
lean_ctor_set(x_279, 3, x_268);
x_280 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_280, 0, x_279);
if (lean_is_scalar(x_270)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_270;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_269);
return x_281;
}
}
else
{
size_t x_282; size_t x_283; uint8_t x_284; 
x_282 = lean_ptr_addr(x_241);
lean_dec(x_241);
x_283 = lean_ptr_addr(x_259);
x_284 = lean_usize_dec_eq(x_282, x_283);
if (x_284 == 0)
{
uint8_t x_285; 
lean_dec(x_242);
x_285 = !lean_is_exclusive(x_1);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_1, 0);
lean_dec(x_286);
if (lean_is_scalar(x_244)) {
 x_287 = lean_alloc_ctor(0, 4, 0);
} else {
 x_287 = x_244;
}
lean_ctor_set(x_287, 0, x_240);
lean_ctor_set(x_287, 1, x_259);
lean_ctor_set(x_287, 2, x_252);
lean_ctor_set(x_287, 3, x_268);
lean_ctor_set(x_1, 0, x_287);
if (lean_is_scalar(x_270)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_270;
}
lean_ctor_set(x_288, 0, x_1);
lean_ctor_set(x_288, 1, x_269);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_1);
if (lean_is_scalar(x_244)) {
 x_289 = lean_alloc_ctor(0, 4, 0);
} else {
 x_289 = x_244;
}
lean_ctor_set(x_289, 0, x_240);
lean_ctor_set(x_289, 1, x_259);
lean_ctor_set(x_289, 2, x_252);
lean_ctor_set(x_289, 3, x_268);
x_290 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_290, 0, x_289);
if (lean_is_scalar(x_270)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_270;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_269);
return x_291;
}
}
else
{
uint8_t x_292; 
x_292 = lean_name_eq(x_242, x_252);
lean_dec(x_242);
if (x_292 == 0)
{
uint8_t x_293; 
x_293 = !lean_is_exclusive(x_1);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_1, 0);
lean_dec(x_294);
if (lean_is_scalar(x_244)) {
 x_295 = lean_alloc_ctor(0, 4, 0);
} else {
 x_295 = x_244;
}
lean_ctor_set(x_295, 0, x_240);
lean_ctor_set(x_295, 1, x_259);
lean_ctor_set(x_295, 2, x_252);
lean_ctor_set(x_295, 3, x_268);
lean_ctor_set(x_1, 0, x_295);
if (lean_is_scalar(x_270)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_270;
}
lean_ctor_set(x_296, 0, x_1);
lean_ctor_set(x_296, 1, x_269);
return x_296;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_1);
if (lean_is_scalar(x_244)) {
 x_297 = lean_alloc_ctor(0, 4, 0);
} else {
 x_297 = x_244;
}
lean_ctor_set(x_297, 0, x_240);
lean_ctor_set(x_297, 1, x_259);
lean_ctor_set(x_297, 2, x_252);
lean_ctor_set(x_297, 3, x_268);
x_298 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_298, 0, x_297);
if (lean_is_scalar(x_270)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_270;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_269);
return x_299;
}
}
else
{
lean_object* x_300; 
lean_dec(x_268);
lean_dec(x_259);
lean_dec(x_252);
lean_dec(x_244);
lean_dec(x_240);
if (lean_is_scalar(x_270)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_270;
}
lean_ctor_set(x_300, 0, x_1);
lean_ctor_set(x_300, 1, x_269);
return x_300;
}
}
}
}
block_313:
{
lean_object* x_304; uint8_t x_305; 
lean_dec(x_303);
x_304 = lean_unsigned_to_nat(0u);
x_305 = lean_nat_dec_lt(x_304, x_302);
lean_dec(x_302);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_268);
x_306 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__9;
x_307 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_306);
x_308 = l_Lean_Compiler_LCNF_AltCore_getCode(x_307);
lean_dec(x_307);
if (lean_is_scalar(x_266)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_266;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_269);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_array_fget(x_268, x_304);
lean_dec(x_268);
x_311 = l_Lean_Compiler_LCNF_AltCore_getCode(x_310);
lean_dec(x_310);
if (lean_is_scalar(x_266)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_266;
}
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_269);
return x_312;
}
}
}
else
{
uint8_t x_325; 
lean_dec(x_266);
lean_dec(x_259);
lean_dec(x_252);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_1);
x_325 = !lean_is_exclusive(x_267);
if (x_325 == 0)
{
return x_267;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_267, 0);
x_327 = lean_ctor_get(x_267, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_267);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
else
{
uint8_t x_329; 
lean_dec(x_259);
lean_dec(x_252);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_329 = !lean_is_exclusive(x_263);
if (x_329 == 0)
{
return x_263;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_263, 0);
x_331 = lean_ctor_get(x_263, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_263);
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
lean_dec(x_236);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_333 = !lean_is_exclusive(x_237);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_237, 0);
lean_dec(x_334);
x_335 = lean_ctor_get(x_238, 0);
lean_inc(x_335);
lean_dec(x_238);
lean_ctor_set(x_237, 0, x_335);
return x_237;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_237, 1);
lean_inc(x_336);
lean_dec(x_237);
x_337 = lean_ctor_get(x_238, 0);
lean_inc(x_337);
lean_dec(x_238);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
}
else
{
uint8_t x_339; 
lean_dec(x_236);
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_339 = !lean_is_exclusive(x_237);
if (x_339 == 0)
{
return x_237;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_237, 0);
x_341 = lean_ctor_get(x_237, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_237);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
case 5:
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_343 = lean_ctor_get(x_35, 1);
lean_inc(x_343);
lean_dec(x_35);
x_344 = lean_ctor_get(x_1, 0);
lean_inc(x_344);
x_345 = lean_st_ref_get(x_7, x_343);
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
lean_dec(x_345);
x_347 = lean_st_ref_get(x_3, x_346);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
lean_dec(x_347);
x_350 = lean_ctor_get(x_348, 0);
lean_inc(x_350);
lean_dec(x_348);
x_351 = 0;
lean_inc(x_344);
x_352 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_350, x_344, x_351);
lean_inc(x_352);
x_353 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_352, x_2, x_3, x_4, x_5, x_6, x_7, x_349);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_354 = !lean_is_exclusive(x_353);
if (x_354 == 0)
{
lean_object* x_355; uint8_t x_356; 
x_355 = lean_ctor_get(x_353, 0);
lean_dec(x_355);
x_356 = lean_name_eq(x_344, x_352);
lean_dec(x_344);
if (x_356 == 0)
{
uint8_t x_357; 
x_357 = !lean_is_exclusive(x_1);
if (x_357 == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_1, 0);
lean_dec(x_358);
lean_ctor_set(x_1, 0, x_352);
lean_ctor_set(x_353, 0, x_1);
return x_353;
}
else
{
lean_object* x_359; 
lean_dec(x_1);
x_359 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_359, 0, x_352);
lean_ctor_set(x_353, 0, x_359);
return x_353;
}
}
else
{
lean_dec(x_352);
lean_ctor_set(x_353, 0, x_1);
return x_353;
}
}
else
{
lean_object* x_360; uint8_t x_361; 
x_360 = lean_ctor_get(x_353, 1);
lean_inc(x_360);
lean_dec(x_353);
x_361 = lean_name_eq(x_344, x_352);
lean_dec(x_344);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_362 = x_1;
} else {
 lean_dec_ref(x_1);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(5, 1, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_352);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_360);
return x_364;
}
else
{
lean_object* x_365; 
lean_dec(x_352);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_1);
lean_ctor_set(x_365, 1, x_360);
return x_365;
}
}
}
default: 
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_366 = lean_ctor_get(x_35, 1);
lean_inc(x_366);
lean_dec(x_35);
x_367 = lean_ctor_get(x_1, 0);
lean_inc(x_367);
x_368 = lean_st_ref_get(x_7, x_366);
lean_dec(x_7);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_370 = lean_st_ref_get(x_3, x_369);
lean_dec(x_3);
x_371 = !lean_is_exclusive(x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; lean_object* x_375; size_t x_376; size_t x_377; uint8_t x_378; 
x_372 = lean_ctor_get(x_370, 0);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
lean_dec(x_372);
x_374 = 0;
lean_inc(x_367);
x_375 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_373, x_374, x_367);
x_376 = lean_ptr_addr(x_367);
lean_dec(x_367);
x_377 = lean_ptr_addr(x_375);
x_378 = lean_usize_dec_eq(x_376, x_377);
if (x_378 == 0)
{
uint8_t x_379; 
x_379 = !lean_is_exclusive(x_1);
if (x_379 == 0)
{
lean_object* x_380; 
x_380 = lean_ctor_get(x_1, 0);
lean_dec(x_380);
lean_ctor_set(x_1, 0, x_375);
lean_ctor_set(x_370, 0, x_1);
return x_370;
}
else
{
lean_object* x_381; 
lean_dec(x_1);
x_381 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_381, 0, x_375);
lean_ctor_set(x_370, 0, x_381);
return x_370;
}
}
else
{
lean_dec(x_375);
lean_ctor_set(x_370, 0, x_1);
return x_370;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; size_t x_387; size_t x_388; uint8_t x_389; 
x_382 = lean_ctor_get(x_370, 0);
x_383 = lean_ctor_get(x_370, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_370);
x_384 = lean_ctor_get(x_382, 0);
lean_inc(x_384);
lean_dec(x_382);
x_385 = 0;
lean_inc(x_367);
x_386 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_384, x_385, x_367);
x_387 = lean_ptr_addr(x_367);
lean_dec(x_367);
x_388 = lean_ptr_addr(x_386);
x_389 = lean_usize_dec_eq(x_387, x_388);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_390 = x_1;
} else {
 lean_dec_ref(x_1);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(6, 1, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_386);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_383);
return x_392;
}
else
{
lean_object* x_393; 
lean_dec(x_386);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_1);
lean_ctor_set(x_393, 1, x_383);
return x_393;
}
}
}
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_6);
x_394 = lean_unsigned_to_nat(1u);
x_395 = lean_nat_add(x_12, x_394);
lean_dec(x_12);
x_396 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_396, 0, x_9);
lean_ctor_set(x_396, 1, x_10);
lean_ctor_set(x_396, 2, x_11);
lean_ctor_set(x_396, 3, x_395);
lean_ctor_set(x_396, 4, x_13);
lean_ctor_set(x_396, 5, x_14);
lean_ctor_set(x_396, 6, x_15);
lean_ctor_set(x_396, 7, x_16);
lean_ctor_set(x_396, 8, x_17);
lean_ctor_set(x_396, 9, x_18);
lean_ctor_set(x_396, 10, x_19);
x_397 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_5, x_396, x_7, x_8);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
x_399 = lean_ctor_get(x_1, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_1, 1);
lean_inc(x_400);
x_401 = 0;
lean_inc(x_399);
x_402 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_401, x_399, x_2, x_3, x_4, x_5, x_396, x_7, x_398);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_ctor_get(x_403, 3);
lean_inc(x_405);
x_406 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_405, x_2, x_3, x_4, x_5, x_396, x_7, x_404);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_409 = lean_box(0);
x_410 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_400, x_399, x_1, x_403, x_409, x_2, x_3, x_4, x_5, x_396, x_7, x_408);
return x_410;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_411 = lean_ctor_get(x_406, 1);
lean_inc(x_411);
lean_dec(x_406);
x_412 = lean_ctor_get(x_407, 0);
lean_inc(x_412);
lean_dec(x_407);
x_413 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_403, x_412, x_4, x_5, x_396, x_7, x_411);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_box(0);
x_417 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_400, x_399, x_1, x_414, x_416, x_2, x_3, x_4, x_5, x_396, x_7, x_415);
return x_417;
}
}
case 1:
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_418 = lean_ctor_get(x_397, 1);
lean_inc(x_418);
lean_dec(x_397);
x_419 = lean_ctor_get(x_1, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_1, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 0);
lean_inc(x_421);
x_422 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_421, x_2, x_3, x_4, x_5, x_396, x_7, x_418);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_unbox(x_423);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; uint8_t x_427; 
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
lean_dec(x_422);
lean_inc(x_1);
lean_inc(x_419);
x_426 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed), 13, 4);
lean_closure_set(x_426, 0, x_420);
lean_closure_set(x_426, 1, x_419);
lean_closure_set(x_426, 2, x_1);
lean_closure_set(x_426, 3, x_423);
x_427 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_box(0);
x_429 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_426, x_419, x_428, x_2, x_3, x_4, x_5, x_396, x_7, x_425);
return x_429;
}
else
{
lean_object* x_430; lean_object* x_431; uint8_t x_432; 
x_430 = lean_ctor_get(x_419, 3);
lean_inc(x_430);
x_431 = lean_ctor_get(x_419, 2);
lean_inc(x_431);
x_432 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_430, x_431);
lean_dec(x_431);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_box(0);
x_434 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_426, x_419, x_433, x_2, x_3, x_4, x_5, x_396, x_7, x_425);
return x_434;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; 
x_435 = lean_st_ref_get(x_7, x_425);
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
lean_dec(x_435);
x_437 = lean_st_ref_get(x_3, x_436);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
lean_dec(x_437);
x_440 = lean_ctor_get(x_438, 0);
lean_inc(x_440);
lean_dec(x_438);
x_441 = 0;
lean_inc(x_7);
lean_inc(x_396);
lean_inc(x_5);
x_442 = l_Lean_Compiler_LCNF_normFunDeclImp(x_441, x_419, x_440, x_4, x_5, x_396, x_7, x_439);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
lean_inc(x_7);
lean_inc(x_396);
lean_inc(x_5);
x_445 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_443, x_4, x_5, x_396, x_7, x_444);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
x_448 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_396, x_7, x_447);
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_426, x_446, x_449, x_2, x_3, x_4, x_5, x_396, x_7, x_450);
lean_dec(x_449);
return x_451;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_426);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_452 = lean_ctor_get(x_445, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_445, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_454 = x_445;
} else {
 lean_dec_ref(x_445);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(1, 2, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_452);
lean_ctor_set(x_455, 1, x_453);
return x_455;
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_426);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_456 = lean_ctor_get(x_442, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_442, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_458 = x_442;
} else {
 lean_dec_ref(x_442);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 2, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_456);
lean_ctor_set(x_459, 1, x_457);
return x_459;
}
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; 
x_460 = lean_ctor_get(x_422, 1);
lean_inc(x_460);
lean_dec(x_422);
x_461 = lean_st_ref_get(x_7, x_460);
x_462 = lean_ctor_get(x_461, 1);
lean_inc(x_462);
lean_dec(x_461);
x_463 = lean_st_ref_get(x_3, x_462);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
x_466 = lean_ctor_get(x_464, 0);
lean_inc(x_466);
lean_dec(x_464);
x_467 = 0;
lean_inc(x_7);
lean_inc(x_396);
lean_inc(x_5);
lean_inc(x_419);
x_468 = l_Lean_Compiler_LCNF_normFunDeclImp(x_467, x_419, x_466, x_4, x_5, x_396, x_7, x_465);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
lean_dec(x_468);
x_471 = lean_box(0);
x_472 = lean_unbox(x_423);
lean_dec(x_423);
x_473 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_420, x_419, x_1, x_472, x_469, x_471, x_2, x_3, x_4, x_5, x_396, x_7, x_470);
return x_473;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
lean_dec(x_423);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_474 = lean_ctor_get(x_468, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_468, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_476 = x_468;
} else {
 lean_dec_ref(x_468);
 x_476 = lean_box(0);
}
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(1, 2, 0);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_474);
lean_ctor_set(x_477, 1, x_475);
return x_477;
}
}
}
case 2:
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
x_478 = lean_ctor_get(x_397, 1);
lean_inc(x_478);
lean_dec(x_397);
x_479 = lean_ctor_get(x_1, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_1, 1);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 0);
lean_inc(x_481);
x_482 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_481, x_2, x_3, x_4, x_5, x_396, x_7, x_478);
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_unbox(x_483);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; uint8_t x_487; 
x_485 = lean_ctor_get(x_482, 1);
lean_inc(x_485);
lean_dec(x_482);
lean_inc(x_1);
lean_inc(x_479);
x_486 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 13, 4);
lean_closure_set(x_486, 0, x_480);
lean_closure_set(x_486, 1, x_479);
lean_closure_set(x_486, 2, x_1);
lean_closure_set(x_486, 3, x_483);
x_487 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; 
x_488 = lean_box(0);
x_489 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_486, x_479, x_488, x_2, x_3, x_4, x_5, x_396, x_7, x_485);
return x_489;
}
else
{
lean_object* x_490; lean_object* x_491; uint8_t x_492; 
x_490 = lean_ctor_get(x_479, 3);
lean_inc(x_490);
x_491 = lean_ctor_get(x_479, 2);
lean_inc(x_491);
x_492 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_490, x_491);
lean_dec(x_491);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; 
x_493 = lean_box(0);
x_494 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_486, x_479, x_493, x_2, x_3, x_4, x_5, x_396, x_7, x_485);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; lean_object* x_502; 
x_495 = lean_st_ref_get(x_7, x_485);
x_496 = lean_ctor_get(x_495, 1);
lean_inc(x_496);
lean_dec(x_495);
x_497 = lean_st_ref_get(x_3, x_496);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = lean_ctor_get(x_498, 0);
lean_inc(x_500);
lean_dec(x_498);
x_501 = 0;
lean_inc(x_7);
lean_inc(x_396);
lean_inc(x_5);
x_502 = l_Lean_Compiler_LCNF_normFunDeclImp(x_501, x_479, x_500, x_4, x_5, x_396, x_7, x_499);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec(x_502);
lean_inc(x_7);
lean_inc(x_396);
lean_inc(x_5);
x_505 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_503, x_4, x_5, x_396, x_7, x_504);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_396, x_7, x_507);
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_486, x_506, x_509, x_2, x_3, x_4, x_5, x_396, x_7, x_510);
lean_dec(x_509);
return x_511;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_486);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_512 = lean_ctor_get(x_505, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_505, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_514 = x_505;
} else {
 lean_dec_ref(x_505);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_512);
lean_ctor_set(x_515, 1, x_513);
return x_515;
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_486);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_516 = lean_ctor_get(x_502, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_502, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_518 = x_502;
} else {
 lean_dec_ref(x_502);
 x_518 = lean_box(0);
}
if (lean_is_scalar(x_518)) {
 x_519 = lean_alloc_ctor(1, 2, 0);
} else {
 x_519 = x_518;
}
lean_ctor_set(x_519, 0, x_516);
lean_ctor_set(x_519, 1, x_517);
return x_519;
}
}
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; lean_object* x_528; 
x_520 = lean_ctor_get(x_482, 1);
lean_inc(x_520);
lean_dec(x_482);
x_521 = lean_st_ref_get(x_7, x_520);
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
lean_dec(x_521);
x_523 = lean_st_ref_get(x_3, x_522);
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
x_526 = lean_ctor_get(x_524, 0);
lean_inc(x_526);
lean_dec(x_524);
x_527 = 0;
lean_inc(x_7);
lean_inc(x_396);
lean_inc(x_5);
lean_inc(x_479);
x_528 = l_Lean_Compiler_LCNF_normFunDeclImp(x_527, x_479, x_526, x_4, x_5, x_396, x_7, x_525);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; lean_object* x_533; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
lean_dec(x_528);
x_531 = lean_box(0);
x_532 = lean_unbox(x_483);
lean_dec(x_483);
x_533 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_480, x_479, x_1, x_532, x_529, x_531, x_2, x_3, x_4, x_5, x_396, x_7, x_530);
return x_533;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_483);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_534 = lean_ctor_get(x_528, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_528, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_536 = x_528;
} else {
 lean_dec_ref(x_528);
 x_536 = lean_box(0);
}
if (lean_is_scalar(x_536)) {
 x_537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_537 = x_536;
}
lean_ctor_set(x_537, 0, x_534);
lean_ctor_set(x_537, 1, x_535);
return x_537;
}
}
}
case 3:
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; uint8_t x_547; lean_object* x_548; lean_object* x_549; 
x_538 = lean_ctor_get(x_397, 1);
lean_inc(x_538);
lean_dec(x_397);
x_539 = lean_ctor_get(x_1, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_1, 1);
lean_inc(x_540);
x_541 = lean_st_ref_get(x_7, x_538);
x_542 = lean_ctor_get(x_541, 1);
lean_inc(x_542);
lean_dec(x_541);
x_543 = lean_st_ref_get(x_3, x_542);
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = lean_ctor_get(x_544, 0);
lean_inc(x_546);
lean_dec(x_544);
x_547 = 0;
lean_inc(x_539);
x_548 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_546, x_539, x_547);
lean_inc(x_7);
lean_inc(x_396);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_540);
x_549 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_547, x_540, x_2, x_3, x_4, x_5, x_396, x_7, x_545);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_566; 
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
lean_inc(x_7);
lean_inc(x_396);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_550);
lean_inc(x_548);
x_566 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_548, x_550, x_2, x_3, x_4, x_5, x_396, x_7, x_551);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; 
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
lean_inc(x_548);
x_569 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_548, x_2, x_3, x_4, x_5, x_396, x_7, x_568);
x_570 = lean_ctor_get(x_569, 1);
lean_inc(x_570);
lean_dec(x_569);
x_571 = lean_array_get_size(x_550);
x_572 = lean_unsigned_to_nat(0u);
x_573 = lean_nat_dec_lt(x_572, x_571);
if (x_573 == 0)
{
lean_dec(x_571);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_553 = x_570;
goto block_565;
}
else
{
uint8_t x_574; 
x_574 = lean_nat_dec_le(x_571, x_571);
if (x_574 == 0)
{
lean_dec(x_571);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_553 = x_570;
goto block_565;
}
else
{
size_t x_575; size_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_575 = 0;
x_576 = lean_usize_of_nat(x_571);
lean_dec(x_571);
x_577 = lean_box(0);
x_578 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_550, x_575, x_576, x_577, x_2, x_3, x_4, x_5, x_396, x_7, x_570);
lean_dec(x_7);
lean_dec(x_396);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_579 = lean_ctor_get(x_578, 1);
lean_inc(x_579);
lean_dec(x_578);
x_553 = x_579;
goto block_565;
}
}
}
else
{
lean_object* x_580; lean_object* x_581; 
lean_dec(x_552);
lean_dec(x_550);
lean_dec(x_548);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_1);
x_580 = lean_ctor_get(x_566, 1);
lean_inc(x_580);
lean_dec(x_566);
x_581 = lean_ctor_get(x_567, 0);
lean_inc(x_581);
lean_dec(x_567);
x_1 = x_581;
x_6 = x_396;
x_8 = x_580;
goto _start;
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
lean_dec(x_552);
lean_dec(x_550);
lean_dec(x_548);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_583 = lean_ctor_get(x_566, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_566, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_585 = x_566;
} else {
 lean_dec_ref(x_566);
 x_585 = lean_box(0);
}
if (lean_is_scalar(x_585)) {
 x_586 = lean_alloc_ctor(1, 2, 0);
} else {
 x_586 = x_585;
}
lean_ctor_set(x_586, 0, x_583);
lean_ctor_set(x_586, 1, x_584);
return x_586;
}
block_565:
{
uint8_t x_554; 
x_554 = lean_name_eq(x_539, x_548);
lean_dec(x_539);
if (x_554 == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_540);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_555 = x_1;
} else {
 lean_dec_ref(x_1);
 x_555 = lean_box(0);
}
if (lean_is_scalar(x_555)) {
 x_556 = lean_alloc_ctor(3, 2, 0);
} else {
 x_556 = x_555;
}
lean_ctor_set(x_556, 0, x_548);
lean_ctor_set(x_556, 1, x_550);
if (lean_is_scalar(x_552)) {
 x_557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_557 = x_552;
}
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_553);
return x_557;
}
else
{
size_t x_558; size_t x_559; uint8_t x_560; 
x_558 = lean_ptr_addr(x_540);
lean_dec(x_540);
x_559 = lean_ptr_addr(x_550);
x_560 = lean_usize_dec_eq(x_558, x_559);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_561 = x_1;
} else {
 lean_dec_ref(x_1);
 x_561 = lean_box(0);
}
if (lean_is_scalar(x_561)) {
 x_562 = lean_alloc_ctor(3, 2, 0);
} else {
 x_562 = x_561;
}
lean_ctor_set(x_562, 0, x_548);
lean_ctor_set(x_562, 1, x_550);
if (lean_is_scalar(x_552)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_552;
}
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_553);
return x_563;
}
else
{
lean_object* x_564; 
lean_dec(x_550);
lean_dec(x_548);
if (lean_is_scalar(x_552)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_552;
}
lean_ctor_set(x_564, 0, x_1);
lean_ctor_set(x_564, 1, x_553);
return x_564;
}
}
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_548);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_587 = lean_ctor_get(x_549, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_549, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_589 = x_549;
} else {
 lean_dec_ref(x_549);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(1, 2, 0);
} else {
 x_590 = x_589;
}
lean_ctor_set(x_590, 0, x_587);
lean_ctor_set(x_590, 1, x_588);
return x_590;
}
}
case 4:
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_591 = lean_ctor_get(x_397, 1);
lean_inc(x_591);
lean_dec(x_397);
x_592 = lean_ctor_get(x_1, 0);
lean_inc(x_592);
lean_inc(x_7);
lean_inc(x_396);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_592);
x_593 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_592, x_2, x_3, x_4, x_5, x_396, x_7, x_591);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; 
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_595 = lean_ctor_get(x_593, 1);
lean_inc(x_595);
lean_dec(x_593);
x_596 = lean_ctor_get(x_592, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_592, 1);
lean_inc(x_597);
x_598 = lean_ctor_get(x_592, 2);
lean_inc(x_598);
x_599 = lean_ctor_get(x_592, 3);
lean_inc(x_599);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 lean_ctor_release(x_592, 2);
 lean_ctor_release(x_592, 3);
 x_600 = x_592;
} else {
 lean_dec_ref(x_592);
 x_600 = lean_box(0);
}
x_601 = lean_st_ref_get(x_7, x_595);
x_602 = lean_ctor_get(x_601, 1);
lean_inc(x_602);
lean_dec(x_601);
x_603 = lean_st_ref_get(x_3, x_602);
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
x_606 = lean_ctor_get(x_604, 0);
lean_inc(x_606);
lean_dec(x_604);
x_607 = 0;
lean_inc(x_598);
x_608 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_606, x_598, x_607);
x_609 = lean_st_ref_get(x_7, x_605);
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
lean_inc(x_597);
x_615 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_614, x_607, x_597);
lean_inc(x_608);
x_616 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_608, x_2, x_3, x_4, x_5, x_396, x_7, x_613);
x_617 = lean_ctor_get(x_616, 1);
lean_inc(x_617);
lean_dec(x_616);
lean_inc(x_608);
x_618 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__8___boxed), 9, 1);
lean_closure_set(x_618, 0, x_608);
lean_inc(x_7);
lean_inc(x_396);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_599);
x_619 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_599, x_618, x_2, x_3, x_4, x_5, x_396, x_7, x_617);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_622 = x_619;
} else {
 lean_dec_ref(x_619);
 x_622 = lean_box(0);
}
x_623 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_620, x_2, x_3, x_4, x_5, x_396, x_7, x_621);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_649; lean_object* x_650; uint8_t x_661; 
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_626 = x_623;
} else {
 lean_dec_ref(x_623);
 x_626 = lean_box(0);
}
x_649 = lean_array_get_size(x_624);
x_661 = lean_nat_dec_eq(x_649, x_394);
if (x_661 == 0)
{
lean_object* x_662; 
lean_dec(x_649);
lean_dec(x_622);
x_662 = lean_box(0);
x_627 = x_662;
goto block_648;
}
else
{
lean_object* x_663; uint8_t x_664; 
x_663 = lean_unsigned_to_nat(0u);
x_664 = lean_nat_dec_lt(x_663, x_649);
if (x_664 == 0)
{
lean_object* x_665; lean_object* x_666; 
x_665 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__9;
x_666 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_665);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; 
lean_dec(x_666);
lean_dec(x_649);
lean_dec(x_622);
x_667 = lean_box(0);
x_627 = x_667;
goto block_648;
}
else
{
lean_object* x_668; 
lean_dec(x_666);
lean_dec(x_626);
lean_dec(x_615);
lean_dec(x_608);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_1);
x_668 = lean_box(0);
x_650 = x_668;
goto block_660;
}
}
else
{
lean_object* x_669; 
x_669 = lean_array_fget(x_624, x_663);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; 
lean_dec(x_669);
lean_dec(x_649);
lean_dec(x_622);
x_670 = lean_box(0);
x_627 = x_670;
goto block_648;
}
else
{
lean_object* x_671; 
lean_dec(x_669);
lean_dec(x_626);
lean_dec(x_615);
lean_dec(x_608);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_1);
x_671 = lean_box(0);
x_650 = x_671;
goto block_660;
}
}
}
block_648:
{
size_t x_628; size_t x_629; uint8_t x_630; 
lean_dec(x_627);
x_628 = lean_ptr_addr(x_599);
lean_dec(x_599);
x_629 = lean_ptr_addr(x_624);
x_630 = lean_usize_dec_eq(x_628, x_629);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_598);
lean_dec(x_597);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_631 = x_1;
} else {
 lean_dec_ref(x_1);
 x_631 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_632 = lean_alloc_ctor(0, 4, 0);
} else {
 x_632 = x_600;
}
lean_ctor_set(x_632, 0, x_596);
lean_ctor_set(x_632, 1, x_615);
lean_ctor_set(x_632, 2, x_608);
lean_ctor_set(x_632, 3, x_624);
if (lean_is_scalar(x_631)) {
 x_633 = lean_alloc_ctor(4, 1, 0);
} else {
 x_633 = x_631;
}
lean_ctor_set(x_633, 0, x_632);
if (lean_is_scalar(x_626)) {
 x_634 = lean_alloc_ctor(0, 2, 0);
} else {
 x_634 = x_626;
}
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_625);
return x_634;
}
else
{
size_t x_635; size_t x_636; uint8_t x_637; 
x_635 = lean_ptr_addr(x_597);
lean_dec(x_597);
x_636 = lean_ptr_addr(x_615);
x_637 = lean_usize_dec_eq(x_635, x_636);
if (x_637 == 0)
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
lean_dec(x_598);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_638 = x_1;
} else {
 lean_dec_ref(x_1);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_639 = lean_alloc_ctor(0, 4, 0);
} else {
 x_639 = x_600;
}
lean_ctor_set(x_639, 0, x_596);
lean_ctor_set(x_639, 1, x_615);
lean_ctor_set(x_639, 2, x_608);
lean_ctor_set(x_639, 3, x_624);
if (lean_is_scalar(x_638)) {
 x_640 = lean_alloc_ctor(4, 1, 0);
} else {
 x_640 = x_638;
}
lean_ctor_set(x_640, 0, x_639);
if (lean_is_scalar(x_626)) {
 x_641 = lean_alloc_ctor(0, 2, 0);
} else {
 x_641 = x_626;
}
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_625);
return x_641;
}
else
{
uint8_t x_642; 
x_642 = lean_name_eq(x_598, x_608);
lean_dec(x_598);
if (x_642 == 0)
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_643 = x_1;
} else {
 lean_dec_ref(x_1);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_644 = lean_alloc_ctor(0, 4, 0);
} else {
 x_644 = x_600;
}
lean_ctor_set(x_644, 0, x_596);
lean_ctor_set(x_644, 1, x_615);
lean_ctor_set(x_644, 2, x_608);
lean_ctor_set(x_644, 3, x_624);
if (lean_is_scalar(x_643)) {
 x_645 = lean_alloc_ctor(4, 1, 0);
} else {
 x_645 = x_643;
}
lean_ctor_set(x_645, 0, x_644);
if (lean_is_scalar(x_626)) {
 x_646 = lean_alloc_ctor(0, 2, 0);
} else {
 x_646 = x_626;
}
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_625);
return x_646;
}
else
{
lean_object* x_647; 
lean_dec(x_624);
lean_dec(x_615);
lean_dec(x_608);
lean_dec(x_600);
lean_dec(x_596);
if (lean_is_scalar(x_626)) {
 x_647 = lean_alloc_ctor(0, 2, 0);
} else {
 x_647 = x_626;
}
lean_ctor_set(x_647, 0, x_1);
lean_ctor_set(x_647, 1, x_625);
return x_647;
}
}
}
}
block_660:
{
lean_object* x_651; uint8_t x_652; 
lean_dec(x_650);
x_651 = lean_unsigned_to_nat(0u);
x_652 = lean_nat_dec_lt(x_651, x_649);
lean_dec(x_649);
if (x_652 == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_624);
x_653 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__9;
x_654 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_653);
x_655 = l_Lean_Compiler_LCNF_AltCore_getCode(x_654);
lean_dec(x_654);
if (lean_is_scalar(x_622)) {
 x_656 = lean_alloc_ctor(0, 2, 0);
} else {
 x_656 = x_622;
}
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_625);
return x_656;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_array_fget(x_624, x_651);
lean_dec(x_624);
x_658 = l_Lean_Compiler_LCNF_AltCore_getCode(x_657);
lean_dec(x_657);
if (lean_is_scalar(x_622)) {
 x_659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_659 = x_622;
}
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_625);
return x_659;
}
}
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_622);
lean_dec(x_615);
lean_dec(x_608);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_1);
x_672 = lean_ctor_get(x_623, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_623, 1);
lean_inc(x_673);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_674 = x_623;
} else {
 lean_dec_ref(x_623);
 x_674 = lean_box(0);
}
if (lean_is_scalar(x_674)) {
 x_675 = lean_alloc_ctor(1, 2, 0);
} else {
 x_675 = x_674;
}
lean_ctor_set(x_675, 0, x_672);
lean_ctor_set(x_675, 1, x_673);
return x_675;
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
lean_dec(x_615);
lean_dec(x_608);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_676 = lean_ctor_get(x_619, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_619, 1);
lean_inc(x_677);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_678 = x_619;
} else {
 lean_dec_ref(x_619);
 x_678 = lean_box(0);
}
if (lean_is_scalar(x_678)) {
 x_679 = lean_alloc_ctor(1, 2, 0);
} else {
 x_679 = x_678;
}
lean_ctor_set(x_679, 0, x_676);
lean_ctor_set(x_679, 1, x_677);
return x_679;
}
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec(x_592);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_680 = lean_ctor_get(x_593, 1);
lean_inc(x_680);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_681 = x_593;
} else {
 lean_dec_ref(x_593);
 x_681 = lean_box(0);
}
x_682 = lean_ctor_get(x_594, 0);
lean_inc(x_682);
lean_dec(x_594);
if (lean_is_scalar(x_681)) {
 x_683 = lean_alloc_ctor(0, 2, 0);
} else {
 x_683 = x_681;
}
lean_ctor_set(x_683, 0, x_682);
lean_ctor_set(x_683, 1, x_680);
return x_683;
}
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
lean_dec(x_592);
lean_dec(x_396);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_684 = lean_ctor_get(x_593, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_593, 1);
lean_inc(x_685);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_686 = x_593;
} else {
 lean_dec_ref(x_593);
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
case 5:
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; uint8_t x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; uint8_t x_701; 
x_688 = lean_ctor_get(x_397, 1);
lean_inc(x_688);
lean_dec(x_397);
x_689 = lean_ctor_get(x_1, 0);
lean_inc(x_689);
x_690 = lean_st_ref_get(x_7, x_688);
x_691 = lean_ctor_get(x_690, 1);
lean_inc(x_691);
lean_dec(x_690);
x_692 = lean_st_ref_get(x_3, x_691);
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_692, 1);
lean_inc(x_694);
lean_dec(x_692);
x_695 = lean_ctor_get(x_693, 0);
lean_inc(x_695);
lean_dec(x_693);
x_696 = 0;
lean_inc(x_689);
x_697 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_695, x_689, x_696);
lean_inc(x_697);
x_698 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_697, x_2, x_3, x_4, x_5, x_396, x_7, x_694);
lean_dec(x_7);
lean_dec(x_396);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_699 = lean_ctor_get(x_698, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_698)) {
 lean_ctor_release(x_698, 0);
 lean_ctor_release(x_698, 1);
 x_700 = x_698;
} else {
 lean_dec_ref(x_698);
 x_700 = lean_box(0);
}
x_701 = lean_name_eq(x_689, x_697);
lean_dec(x_689);
if (x_701 == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_702 = x_1;
} else {
 lean_dec_ref(x_1);
 x_702 = lean_box(0);
}
if (lean_is_scalar(x_702)) {
 x_703 = lean_alloc_ctor(5, 1, 0);
} else {
 x_703 = x_702;
}
lean_ctor_set(x_703, 0, x_697);
if (lean_is_scalar(x_700)) {
 x_704 = lean_alloc_ctor(0, 2, 0);
} else {
 x_704 = x_700;
}
lean_ctor_set(x_704, 0, x_703);
lean_ctor_set(x_704, 1, x_699);
return x_704;
}
else
{
lean_object* x_705; 
lean_dec(x_697);
if (lean_is_scalar(x_700)) {
 x_705 = lean_alloc_ctor(0, 2, 0);
} else {
 x_705 = x_700;
}
lean_ctor_set(x_705, 0, x_1);
lean_ctor_set(x_705, 1, x_699);
return x_705;
}
}
default: 
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; lean_object* x_716; size_t x_717; size_t x_718; uint8_t x_719; 
lean_dec(x_396);
lean_dec(x_5);
lean_dec(x_2);
x_706 = lean_ctor_get(x_397, 1);
lean_inc(x_706);
lean_dec(x_397);
x_707 = lean_ctor_get(x_1, 0);
lean_inc(x_707);
x_708 = lean_st_ref_get(x_7, x_706);
lean_dec(x_7);
x_709 = lean_ctor_get(x_708, 1);
lean_inc(x_709);
lean_dec(x_708);
x_710 = lean_st_ref_get(x_3, x_709);
lean_dec(x_3);
x_711 = lean_ctor_get(x_710, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_710, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 lean_ctor_release(x_710, 1);
 x_713 = x_710;
} else {
 lean_dec_ref(x_710);
 x_713 = lean_box(0);
}
x_714 = lean_ctor_get(x_711, 0);
lean_inc(x_714);
lean_dec(x_711);
x_715 = 0;
lean_inc(x_707);
x_716 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_714, x_715, x_707);
x_717 = lean_ptr_addr(x_707);
lean_dec(x_707);
x_718 = lean_ptr_addr(x_716);
x_719 = lean_usize_dec_eq(x_717, x_718);
if (x_719 == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_720 = x_1;
} else {
 lean_dec_ref(x_1);
 x_720 = lean_box(0);
}
if (lean_is_scalar(x_720)) {
 x_721 = lean_alloc_ctor(6, 1, 0);
} else {
 x_721 = x_720;
}
lean_ctor_set(x_721, 0, x_716);
if (lean_is_scalar(x_713)) {
 x_722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_722 = x_713;
}
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_712);
return x_722;
}
else
{
lean_object* x_723; 
lean_dec(x_716);
if (lean_is_scalar(x_713)) {
 x_723 = lean_alloc_ctor(0, 2, 0);
} else {
 x_723 = x_713;
}
lean_ctor_set(x_723, 0, x_1);
lean_ctor_set(x_723, 1, x_712);
return x_723;
}
}
}
}
}
else
{
lean_object* x_724; 
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
x_724 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_724;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_41 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_36, x_40, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
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
x_48 = lean_st_ref_get(x_10, x_43);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_st_ref_take(x_6, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = l_Lean_Expr_fvar___override(x_47);
x_56 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_54, x_46, x_55);
lean_ctor_set(x_51, 0, x_56);
x_57 = lean_st_ref_set(x_6, x_51, x_52);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
lean_ctor_set(x_4, 1, x_45);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_4);
x_15 = x_59;
x_16 = x_58;
goto block_23;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
x_62 = lean_ctor_get(x_51, 2);
x_63 = lean_ctor_get_uint8(x_51, sizeof(void*)*6);
x_64 = lean_ctor_get(x_51, 3);
x_65 = lean_ctor_get(x_51, 4);
x_66 = lean_ctor_get(x_51, 5);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
x_67 = l_Lean_Expr_fvar___override(x_47);
x_68 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_60, x_46, x_67);
x_69 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_62);
lean_ctor_set(x_69, 3, x_64);
lean_ctor_set(x_69, 4, x_65);
lean_ctor_set(x_69, 5, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*6, x_63);
x_70 = lean_st_ref_set(x_6, x_69, x_52);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
lean_ctor_set(x_4, 1, x_45);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_4);
x_15 = x_72;
x_16 = x_71;
goto block_23;
}
}
else
{
uint8_t x_73; 
lean_dec(x_25);
lean_free_object(x_4);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_73 = !lean_is_exclusive(x_41);
if (x_73 == 0)
{
return x_41;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_41, 0);
x_75 = lean_ctor_get(x_41, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_77 = lean_ctor_get(x_14, 0);
lean_inc(x_77);
lean_dec(x_14);
x_78 = l_Lean_Expr_fvarId_x21(x_36);
x_79 = lean_st_ref_get(x_10, x_11);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_st_ref_take(x_6, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = l_Lean_Expr_fvar___override(x_78);
x_87 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_85, x_77, x_86);
lean_ctor_set(x_82, 0, x_87);
x_88 = lean_st_ref_set(x_6, x_82, x_83);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_4);
x_15 = x_90;
x_16 = x_89;
goto block_23;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_91 = lean_ctor_get(x_82, 0);
x_92 = lean_ctor_get(x_82, 1);
x_93 = lean_ctor_get(x_82, 2);
x_94 = lean_ctor_get_uint8(x_82, sizeof(void*)*6);
x_95 = lean_ctor_get(x_82, 3);
x_96 = lean_ctor_get(x_82, 4);
x_97 = lean_ctor_get(x_82, 5);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_82);
x_98 = l_Lean_Expr_fvar___override(x_78);
x_99 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_91, x_77, x_98);
x_100 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_92);
lean_ctor_set(x_100, 2, x_93);
lean_ctor_set(x_100, 3, x_95);
lean_ctor_set(x_100, 4, x_96);
lean_ctor_set(x_100, 5, x_97);
lean_ctor_set_uint8(x_100, sizeof(void*)*6, x_94);
x_101 = lean_st_ref_set(x_6, x_100, x_83);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_4);
x_15 = x_103;
x_16 = x_102;
goto block_23;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
lean_dec(x_25);
x_104 = lean_array_fget(x_27, x_28);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_28, x_105);
lean_dec(x_28);
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_27);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_29);
x_108 = l_Lean_Expr_isFVar(x_104);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_110 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_104, x_109, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_111);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_111);
x_114 = lean_array_push(x_26, x_113);
x_115 = lean_ctor_get(x_14, 0);
lean_inc(x_115);
lean_dec(x_14);
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
lean_dec(x_111);
x_117 = lean_st_ref_get(x_10, x_112);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_st_ref_take(x_6, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 2);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_120, sizeof(void*)*6);
x_126 = lean_ctor_get(x_120, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_120, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_120, 5);
lean_inc(x_128);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 lean_ctor_release(x_120, 5);
 x_129 = x_120;
} else {
 lean_dec_ref(x_120);
 x_129 = lean_box(0);
}
x_130 = l_Lean_Expr_fvar___override(x_116);
x_131 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_122, x_115, x_130);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(0, 6, 1);
} else {
 x_132 = x_129;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_123);
lean_ctor_set(x_132, 2, x_124);
lean_ctor_set(x_132, 3, x_126);
lean_ctor_set(x_132, 4, x_127);
lean_ctor_set(x_132, 5, x_128);
lean_ctor_set_uint8(x_132, sizeof(void*)*6, x_125);
x_133 = lean_st_ref_set(x_6, x_132, x_121);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
lean_ctor_set(x_4, 1, x_114);
lean_ctor_set(x_4, 0, x_107);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_4);
x_15 = x_135;
x_16 = x_134;
goto block_23;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_107);
lean_free_object(x_4);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_136 = lean_ctor_get(x_110, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_110, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_138 = x_110;
} else {
 lean_dec_ref(x_110);
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
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_140 = lean_ctor_get(x_14, 0);
lean_inc(x_140);
lean_dec(x_14);
x_141 = l_Lean_Expr_fvarId_x21(x_104);
x_142 = lean_st_ref_get(x_10, x_11);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_st_ref_take(x_6, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_145, 2);
lean_inc(x_149);
x_150 = lean_ctor_get_uint8(x_145, sizeof(void*)*6);
x_151 = lean_ctor_get(x_145, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_145, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_145, 5);
lean_inc(x_153);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 lean_ctor_release(x_145, 2);
 lean_ctor_release(x_145, 3);
 lean_ctor_release(x_145, 4);
 lean_ctor_release(x_145, 5);
 x_154 = x_145;
} else {
 lean_dec_ref(x_145);
 x_154 = lean_box(0);
}
x_155 = l_Lean_Expr_fvar___override(x_141);
x_156 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_147, x_140, x_155);
if (lean_is_scalar(x_154)) {
 x_157 = lean_alloc_ctor(0, 6, 1);
} else {
 x_157 = x_154;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_148);
lean_ctor_set(x_157, 2, x_149);
lean_ctor_set(x_157, 3, x_151);
lean_ctor_set(x_157, 4, x_152);
lean_ctor_set(x_157, 5, x_153);
lean_ctor_set_uint8(x_157, sizeof(void*)*6, x_150);
x_158 = lean_st_ref_set(x_6, x_157, x_146);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
lean_ctor_set(x_4, 0, x_107);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_4);
x_15 = x_160;
x_16 = x_159;
goto block_23;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_161 = lean_ctor_get(x_4, 0);
x_162 = lean_ctor_get(x_4, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_4);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_161, 2);
lean_inc(x_165);
x_166 = lean_nat_dec_lt(x_164, x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_14);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_162);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_15 = x_168;
x_16 = x_11;
goto block_23;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 x_169 = x_161;
} else {
 lean_dec_ref(x_161);
 x_169 = lean_box(0);
}
x_170 = lean_array_fget(x_163, x_164);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_add(x_164, x_171);
lean_dec(x_164);
if (lean_is_scalar(x_169)) {
 x_173 = lean_alloc_ctor(0, 3, 0);
} else {
 x_173 = x_169;
}
lean_ctor_set(x_173, 0, x_163);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_173, 2, x_165);
x_174 = l_Lean_Expr_isFVar(x_170);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_176 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_170, x_175, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
lean_inc(x_177);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_177);
x_180 = lean_array_push(x_162, x_179);
x_181 = lean_ctor_get(x_14, 0);
lean_inc(x_181);
lean_dec(x_14);
x_182 = lean_ctor_get(x_177, 0);
lean_inc(x_182);
lean_dec(x_177);
x_183 = lean_st_ref_get(x_10, x_178);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_st_ref_take(x_6, x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 2);
lean_inc(x_190);
x_191 = lean_ctor_get_uint8(x_186, sizeof(void*)*6);
x_192 = lean_ctor_get(x_186, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_186, 4);
lean_inc(x_193);
x_194 = lean_ctor_get(x_186, 5);
lean_inc(x_194);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 lean_ctor_release(x_186, 4);
 lean_ctor_release(x_186, 5);
 x_195 = x_186;
} else {
 lean_dec_ref(x_186);
 x_195 = lean_box(0);
}
x_196 = l_Lean_Expr_fvar___override(x_182);
x_197 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_188, x_181, x_196);
if (lean_is_scalar(x_195)) {
 x_198 = lean_alloc_ctor(0, 6, 1);
} else {
 x_198 = x_195;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_190);
lean_ctor_set(x_198, 3, x_192);
lean_ctor_set(x_198, 4, x_193);
lean_ctor_set(x_198, 5, x_194);
lean_ctor_set_uint8(x_198, sizeof(void*)*6, x_191);
x_199 = lean_st_ref_set(x_6, x_198, x_187);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_173);
lean_ctor_set(x_201, 1, x_180);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_15 = x_202;
x_16 = x_200;
goto block_23;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_173);
lean_dec(x_162);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_203 = lean_ctor_get(x_176, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_176, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_205 = x_176;
} else {
 lean_dec_ref(x_176);
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
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_207 = lean_ctor_get(x_14, 0);
lean_inc(x_207);
lean_dec(x_14);
x_208 = l_Lean_Expr_fvarId_x21(x_170);
x_209 = lean_st_ref_get(x_10, x_11);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = lean_st_ref_take(x_6, x_210);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_212, 2);
lean_inc(x_216);
x_217 = lean_ctor_get_uint8(x_212, sizeof(void*)*6);
x_218 = lean_ctor_get(x_212, 3);
lean_inc(x_218);
x_219 = lean_ctor_get(x_212, 4);
lean_inc(x_219);
x_220 = lean_ctor_get(x_212, 5);
lean_inc(x_220);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 lean_ctor_release(x_212, 3);
 lean_ctor_release(x_212, 4);
 lean_ctor_release(x_212, 5);
 x_221 = x_212;
} else {
 lean_dec_ref(x_212);
 x_221 = lean_box(0);
}
x_222 = l_Lean_Expr_fvar___override(x_208);
x_223 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_214, x_207, x_222);
if (lean_is_scalar(x_221)) {
 x_224 = lean_alloc_ctor(0, 6, 1);
} else {
 x_224 = x_221;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_215);
lean_ctor_set(x_224, 2, x_216);
lean_ctor_set(x_224, 3, x_218);
lean_ctor_set(x_224, 4, x_219);
lean_ctor_set(x_224, 5, x_220);
lean_ctor_set_uint8(x_224, sizeof(void*)*6, x_217);
x_225 = lean_st_ref_set(x_6, x_224, x_213);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_173);
lean_ctor_set(x_227, 1, x_162);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_15 = x_228;
x_16 = x_226;
goto block_23;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_fget(x_3, x_2);
x_15 = lean_box(x_6);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_16 = lean_apply_8(x_1, x_14, x_4, x_5, x_15, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ptr_addr(x_14);
lean_dec(x_14);
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
x_10 = x_18;
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
x_10 = x_18;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(x_2, x_10, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_9);
lean_dec(x_9);
x_15 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_14);
lean_dec(x_14);
x_20 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_19, x_15, x_16, x_17, x_18);
lean_dec(x_12);
lean_dec(x_11);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_8);
lean_dec(x_8);
x_14 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_10, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(x_10, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_10, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_8);
lean_dec(x_8);
x_14 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_9);
lean_dec(x_9);
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_9);
lean_dec(x_9);
x_16 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_15, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_9);
lean_dec(x_9);
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_9);
lean_dec(x_9);
x_16 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_15, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_Compiler_LCNF_Simp_simp___lambda__7(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_Compiler_LCNF_Simp_simp___lambda__8(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(x_10, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(x_10, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
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
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1);
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__2);
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__3);
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__4);
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__5 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__5);
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__6 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__6();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__6);
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__7 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__7();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__7);
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__8 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__8();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__8);
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__9 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__9();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__9);
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
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__6 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__6);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__7 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__7);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__8 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__8);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__9 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__9);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__10 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
