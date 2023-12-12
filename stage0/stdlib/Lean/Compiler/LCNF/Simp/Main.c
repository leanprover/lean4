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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCode;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_hasLocalInst(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1940_(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedLetValue___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_1 = lean_unsigned_to_nat(8u);
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
lean_object* x_173; 
x_173 = lean_box(0);
x_12 = x_173;
x_13 = x_9;
goto block_172;
}
else
{
lean_object* x_174; 
x_174 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_12 = x_174;
x_13 = x_9;
goto block_172;
}
block_172:
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
lean_object* x_16; 
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 3)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_20 = x_16;
} else {
 lean_dec_ref(x_16);
 x_20 = lean_box(0);
}
x_21 = lean_st_ref_get(x_8, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
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
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
lean_inc(x_17);
x_26 = lean_environment_find(x_25, x_17);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_24;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_ConstantInfo_type(x_29);
lean_dec(x_29);
x_31 = l_Lean_Compiler_LCNF_hasLocalInst(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_168; 
x_168 = 0;
x_32 = x_168;
goto block_167;
}
else
{
uint8_t x_169; 
x_169 = 1;
x_32 = x_169;
goto block_167;
}
block_167:
{
lean_object* x_33; lean_object* x_34; 
if (x_32 == 0)
{
lean_object* x_165; 
x_165 = lean_box(0);
x_33 = x_165;
x_34 = x_23;
goto block_164;
}
else
{
lean_object* x_166; 
x_166 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_33 = x_166;
x_34 = x_23;
goto block_164;
}
block_164:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_24;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_161; 
lean_dec(x_33);
lean_dec(x_24);
lean_inc(x_17);
x_37 = l_Lean_Meta_isInstance(x_17, x_7, x_8, x_34);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_161 = lean_unbox(x_38);
lean_dec(x_38);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = 1;
x_41 = x_162;
goto block_160;
}
else
{
uint8_t x_163; 
x_163 = 0;
x_41 = x_163;
goto block_160;
}
block_160:
{
uint8_t x_42; 
if (x_41 == 0)
{
uint8_t x_158; 
x_158 = 0;
x_42 = x_158;
goto block_157;
}
else
{
uint8_t x_159; 
x_159 = 1;
x_42 = x_159;
goto block_157;
}
block_157:
{
lean_object* x_43; lean_object* x_44; 
if (x_42 == 0)
{
lean_object* x_155; 
x_155 = lean_box(0);
x_43 = x_155;
x_44 = x_39;
goto block_154;
}
else
{
lean_object* x_156; 
x_156 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_43 = x_156;
x_44 = x_39;
goto block_154;
}
block_154:
{
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_45 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_40;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_43);
lean_dec(x_40);
lean_inc(x_17);
x_47 = l_Lean_Compiler_LCNF_getDecl_x3f(x_17, x_5, x_6, x_7, x_8, x_44);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_56 = x_47;
} else {
 lean_dec_ref(x_47);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_48, 0);
lean_inc(x_57);
lean_dec(x_48);
x_58 = lean_array_get_size(x_19);
x_59 = l_Lean_Compiler_LCNF_Decl_getArity(x_57);
lean_dec(x_57);
x_60 = lean_nat_dec_lt(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_152; 
x_152 = lean_box(0);
x_61 = x_152;
x_62 = x_55;
goto block_151;
}
else
{
lean_object* x_153; 
x_153 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_61 = x_153;
x_62 = x_55;
goto block_151;
}
block_151:
{
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_63 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_56;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_56);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_66 = lean_ctor_get(x_61, 0);
lean_dec(x_66);
x_67 = lean_ctor_get(x_1, 2);
lean_inc(x_67);
x_68 = l_Lean_Compiler_LCNF_mkNewParams(x_67, x_5, x_6, x_7, x_8, x_62);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_array_get_size(x_69);
x_72 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_73 = 0;
lean_inc(x_69);
x_74 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_72, x_73, x_69);
x_75 = l_Array_append___rarg(x_19, x_74);
if (lean_is_scalar(x_20)) {
 x_76 = lean_alloc_ctor(3, 3, 0);
} else {
 x_76 = x_20;
}
lean_ctor_set(x_76, 0, x_17);
lean_ctor_set(x_76, 1, x_18);
lean_ctor_set(x_76, 2, x_75);
x_77 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_78 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_76, x_77, x_5, x_6, x_7, x_8, x_70);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_85 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_69, x_83, x_84, x_5, x_6, x_7, x_8, x_80);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_88, x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_91);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
lean_ctor_set(x_61, 0, x_86);
lean_ctor_set(x_92, 0, x_61);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
lean_ctor_set(x_61, 0, x_86);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_61);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_86);
lean_free_object(x_61);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_free_object(x_61);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_85);
if (x_101 == 0)
{
return x_85;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_85, 0);
x_103 = lean_ctor_get(x_85, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_85);
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
lean_dec(x_69);
lean_free_object(x_61);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_78);
if (x_105 == 0)
{
return x_78;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_78, 0);
x_107 = lean_ctor_get(x_78, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_78);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_61);
x_109 = lean_ctor_get(x_1, 2);
lean_inc(x_109);
x_110 = l_Lean_Compiler_LCNF_mkNewParams(x_109, x_5, x_6, x_7, x_8, x_62);
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
x_116 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_114, x_115, x_111);
x_117 = l_Array_append___rarg(x_19, x_116);
if (lean_is_scalar(x_20)) {
 x_118 = lean_alloc_ctor(3, 3, 0);
} else {
 x_118 = x_20;
}
lean_ctor_set(x_118, 0, x_17);
lean_ctor_set(x_118, 1, x_18);
lean_ctor_set(x_118, 2, x_117);
x_119 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_120 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_118, x_119, x_5, x_6, x_7, x_8, x_112);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
x_124 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_127 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_111, x_125, x_126, x_5, x_6, x_7, x_8, x_122);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_1, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
x_132 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_130, x_131, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_129);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_133);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_128);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_128);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_139 = lean_ctor_get(x_132, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_132, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_141 = x_132;
} else {
 lean_dec_ref(x_132);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_143 = lean_ctor_get(x_127, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_127, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_145 = x_127;
} else {
 lean_dec_ref(x_127);
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
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_111);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_147 = lean_ctor_get(x_120, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_120, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_149 = x_120;
} else {
 lean_dec_ref(x_120);
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
lean_object* x_170; lean_object* x_171; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_13);
return x_171;
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_st_ref_get(x_4, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 0;
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_15, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_name_eq(x_18, x_2);
lean_dec(x_18);
x_20 = lean_box(x_19);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; 
x_21 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 0;
x_26 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_24, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_name_eq(x_27, x_2);
lean_dec(x_27);
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
}
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_10);
return x_35;
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
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_inc(x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
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
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_array_get_size(x_8);
x_26 = l_Array_toSubarray___rarg(x_8, x_4, x_25);
x_27 = l_Array_ofSubarray___rarg(x_26);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_28, x_29, x_10, x_11, x_12, x_13, x_16);
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
x_34 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_6, x_33, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_7);
x_37 = l_Lean_Compiler_LCNF_Simp_simp(x_36, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_35);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_27);
lean_inc(x_23);
x_32 = l_Array_toSubarray___rarg(x_23, x_31, x_27);
x_33 = l_Array_ofSubarray___rarg(x_32);
switch (lean_obj_tag(x_11)) {
case 0:
{
uint8_t x_34; lean_object* x_35; 
lean_dec(x_11);
x_34 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_35 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_216; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_216 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_box(0);
x_38 = x_217;
goto block_215;
}
else
{
uint8_t x_218; 
x_218 = lean_nat_dec_eq(x_24, x_27);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_box(0);
x_38 = x_219;
goto block_215;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_220 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_37);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = l_Lean_Compiler_LCNF_Simp_simp(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_221);
if (lean_obj_tag(x_222) == 0)
{
uint8_t x_223; 
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_222, 0);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_222, 0, x_225);
return x_222;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_222, 0);
x_227 = lean_ctor_get(x_222, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_222);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_226);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_222);
if (x_230 == 0)
{
return x_222;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_222, 0);
x_232 = lean_ctor_get(x_222, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_222);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
}
block_215:
{
lean_object* x_39; 
lean_dec(x_38);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_39 = l_Lean_Compiler_LCNF_Simp_simp(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_40);
x_42 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_43 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_41);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_21, 2);
lean_inc(x_45);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_inferAppType(x_45, x_33, x_6, x_7, x_8, x_9, x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_47);
x_49 = l_Lean_Expr_headBeta(x_47);
x_50 = l_Lean_Expr_isForall(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_51 = l_Lean_Compiler_LCNF_mkAuxParam(x_47, x_34, x_6, x_7, x_8, x_9, x_48);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_55 == 0)
{
lean_object* x_84; 
lean_dec(x_27);
lean_dec(x_23);
x_84 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_86 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_56 = x_87;
x_57 = x_88;
goto block_83;
}
else
{
uint8_t x_89; 
lean_dec(x_52);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_86, 0);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_86);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_52);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_84);
if (x_93 == 0)
{
return x_84;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_84, 0);
x_95 = lean_ctor_get(x_84, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_84);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_array_get_size(x_23);
x_98 = l_Array_toSubarray___rarg(x_23, x_27, x_97);
x_99 = l_Array_ofSubarray___rarg(x_98);
x_100 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_100, 0, x_54);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_102 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_100, x_101, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_105, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_109 = l_Lean_Compiler_LCNF_Simp_simp(x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_56 = x_110;
x_57 = x_111;
goto block_83;
}
else
{
uint8_t x_112; 
lean_dec(x_52);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
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
lean_dec(x_103);
lean_dec(x_52);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = !lean_is_exclusive(x_106);
if (x_116 == 0)
{
return x_106;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_106, 0);
x_118 = lean_ctor_get(x_106, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_106);
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
lean_dec(x_52);
lean_dec(x_40);
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
x_120 = !lean_is_exclusive(x_102);
if (x_120 == 0)
{
return x_102;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_102, 0);
x_122 = lean_ctor_get(x_102, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_102);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
block_83:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_59 = lean_array_push(x_58, x_52);
x_60 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_61 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_59, x_56, x_60, x_6, x_7, x_8, x_9, x_57);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_62);
x_64 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_64, 0, x_62);
lean_closure_set(x_64, 1, x_58);
x_65 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_64, x_6, x_7, x_8, x_9, x_63);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_22)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_22;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_65, 0, x_69);
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_65, 0);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_65);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_70);
if (lean_is_scalar(x_22)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_22;
}
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_62);
lean_dec(x_22);
x_75 = !lean_is_exclusive(x_65);
if (x_75 == 0)
{
return x_65;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_65, 0);
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_65);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_79 = !lean_is_exclusive(x_61);
if (x_79 == 0)
{
return x_61;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_61, 0);
x_81 = lean_ctor_get(x_61, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_61);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_47);
x_124 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_125 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_126 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_124, x_40, x_125, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_129 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_127, x_6, x_7, x_8, x_9, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_133 == 0)
{
lean_object* x_148; 
lean_dec(x_27);
lean_dec(x_23);
x_148 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_132, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_131);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_150 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_134 = x_151;
x_135 = x_152;
goto block_147;
}
else
{
uint8_t x_153; 
lean_dec(x_130);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_153 = !lean_is_exclusive(x_150);
if (x_153 == 0)
{
return x_150;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_150, 0);
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_150);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_130);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_148);
if (x_157 == 0)
{
return x_148;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_148, 0);
x_159 = lean_ctor_get(x_148, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_148);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_array_get_size(x_23);
x_162 = l_Array_toSubarray___rarg(x_23, x_27, x_161);
x_163 = l_Array_ofSubarray___rarg(x_162);
x_164 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_164, 0, x_132);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_166 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_164, x_165, x_6, x_7, x_8, x_9, x_131);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
x_170 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_169, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_168);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_167);
lean_ctor_set(x_172, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_173 = l_Lean_Compiler_LCNF_Simp_simp(x_172, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_134 = x_174;
x_135 = x_175;
goto block_147;
}
else
{
uint8_t x_176; 
lean_dec(x_130);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_176 = !lean_is_exclusive(x_173);
if (x_176 == 0)
{
return x_173;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_173, 0);
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_173);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_167);
lean_dec(x_130);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_170);
if (x_180 == 0)
{
return x_170;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_170, 0);
x_182 = lean_ctor_get(x_170, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_170);
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
lean_dec(x_130);
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
x_184 = !lean_is_exclusive(x_166);
if (x_184 == 0)
{
return x_166;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_166, 0);
x_186 = lean_ctor_get(x_166, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_166);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
block_147:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_130);
x_137 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_138 = lean_array_push(x_137, x_136);
x_139 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_138, x_134, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_135);
lean_dec(x_138);
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
}
else
{
uint8_t x_188; 
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
x_188 = !lean_is_exclusive(x_129);
if (x_188 == 0)
{
return x_129;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_129, 0);
x_190 = lean_ctor_get(x_129, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_129);
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
x_192 = !lean_is_exclusive(x_126);
if (x_192 == 0)
{
return x_126;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_126, 0);
x_194 = lean_ctor_get(x_126, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_126);
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
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_33);
lean_dec(x_21);
x_196 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_41);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_198, 0, x_3);
lean_closure_set(x_198, 1, x_4);
lean_closure_set(x_198, 2, x_5);
lean_closure_set(x_198, 3, x_27);
lean_closure_set(x_198, 4, x_24);
lean_closure_set(x_198, 5, x_26);
lean_closure_set(x_198, 6, x_2);
lean_closure_set(x_198, 7, x_23);
x_199 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_198, x_6, x_7, x_8, x_9, x_197);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_199, 0);
if (lean_is_scalar(x_22)) {
 x_202 = lean_alloc_ctor(1, 1, 0);
} else {
 x_202 = x_22;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_199, 0, x_202);
return x_199;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_199, 0);
x_204 = lean_ctor_get(x_199, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_199);
if (lean_is_scalar(x_22)) {
 x_205 = lean_alloc_ctor(1, 1, 0);
} else {
 x_205 = x_22;
}
lean_ctor_set(x_205, 0, x_203);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
else
{
uint8_t x_207; 
lean_dec(x_22);
x_207 = !lean_is_exclusive(x_199);
if (x_207 == 0)
{
return x_199;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_199, 0);
x_209 = lean_ctor_get(x_199, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_199);
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
uint8_t x_211; 
lean_dec(x_33);
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
x_211 = !lean_is_exclusive(x_39);
if (x_211 == 0)
{
return x_39;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_39, 0);
x_213 = lean_ctor_get(x_39, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_39);
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
uint8_t x_234; 
lean_dec(x_33);
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
x_234 = !lean_is_exclusive(x_35);
if (x_234 == 0)
{
return x_35;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_35, 0);
x_236 = lean_ctor_get(x_35, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_35);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
case 1:
{
uint8_t x_238; lean_object* x_239; 
x_238 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_239 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_238, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_420; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_420 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_420 == 0)
{
lean_object* x_421; 
x_421 = lean_box(0);
x_242 = x_421;
goto block_419;
}
else
{
uint8_t x_422; 
x_422 = lean_nat_dec_eq(x_24, x_27);
if (x_422 == 0)
{
lean_object* x_423; 
x_423 = lean_box(0);
x_242 = x_423;
goto block_419;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_424 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_241);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
lean_dec(x_424);
x_426 = l_Lean_Compiler_LCNF_Simp_simp(x_240, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_425);
if (lean_obj_tag(x_426) == 0)
{
uint8_t x_427; 
x_427 = !lean_is_exclusive(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_426, 0);
x_429 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_426, 0, x_429);
return x_426;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_430 = lean_ctor_get(x_426, 0);
x_431 = lean_ctor_get(x_426, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_426);
x_432 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_432, 0, x_430);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
}
else
{
uint8_t x_434; 
x_434 = !lean_is_exclusive(x_426);
if (x_434 == 0)
{
return x_426;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_426, 0);
x_436 = lean_ctor_get(x_426, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_426);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
}
block_419:
{
lean_object* x_243; 
lean_dec(x_242);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_243 = l_Lean_Compiler_LCNF_Simp_simp(x_240, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_241);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
lean_inc(x_244);
x_246 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_244);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_247 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_245);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec(x_247);
x_249 = lean_ctor_get(x_21, 2);
lean_inc(x_249);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_250 = l_Lean_Compiler_LCNF_inferAppType(x_249, x_33, x_6, x_7, x_8, x_9, x_248);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
lean_inc(x_251);
x_253 = l_Lean_Expr_headBeta(x_251);
x_254 = l_Lean_Expr_isForall(x_253);
lean_dec(x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; 
x_255 = l_Lean_Compiler_LCNF_mkAuxParam(x_251, x_238, x_6, x_7, x_8, x_9, x_252);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
x_259 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_259 == 0)
{
lean_object* x_288; 
lean_dec(x_27);
lean_dec(x_23);
x_288 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_258, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_257);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
lean_dec(x_288);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_290 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_289);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_260 = x_291;
x_261 = x_292;
goto block_287;
}
else
{
uint8_t x_293; 
lean_dec(x_256);
lean_dec(x_244);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_293 = !lean_is_exclusive(x_290);
if (x_293 == 0)
{
return x_290;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_290, 0);
x_295 = lean_ctor_get(x_290, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_290);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
uint8_t x_297; 
lean_dec(x_256);
lean_dec(x_244);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_297 = !lean_is_exclusive(x_288);
if (x_297 == 0)
{
return x_288;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_288, 0);
x_299 = lean_ctor_get(x_288, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_288);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_301 = lean_array_get_size(x_23);
x_302 = l_Array_toSubarray___rarg(x_23, x_27, x_301);
x_303 = l_Array_ofSubarray___rarg(x_302);
x_304 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_304, 0, x_258);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_306 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_304, x_305, x_6, x_7, x_8, x_9, x_257);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = lean_ctor_get(x_307, 0);
lean_inc(x_309);
x_310 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_309, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_308);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_307);
lean_ctor_set(x_312, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_313 = l_Lean_Compiler_LCNF_Simp_simp(x_312, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_311);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_260 = x_314;
x_261 = x_315;
goto block_287;
}
else
{
uint8_t x_316; 
lean_dec(x_256);
lean_dec(x_244);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_316 = !lean_is_exclusive(x_313);
if (x_316 == 0)
{
return x_313;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_313, 0);
x_318 = lean_ctor_get(x_313, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_313);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
else
{
uint8_t x_320; 
lean_dec(x_307);
lean_dec(x_256);
lean_dec(x_244);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_320 = !lean_is_exclusive(x_310);
if (x_320 == 0)
{
return x_310;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_310, 0);
x_322 = lean_ctor_get(x_310, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_310);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_256);
lean_dec(x_244);
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
x_324 = !lean_is_exclusive(x_306);
if (x_324 == 0)
{
return x_306;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_306, 0);
x_326 = lean_ctor_get(x_306, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_306);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
block_287:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_263 = lean_array_push(x_262, x_256);
x_264 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_265 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_263, x_260, x_264, x_6, x_7, x_8, x_9, x_261);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
lean_inc(x_266);
x_268 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_268, 0, x_266);
lean_closure_set(x_268, 1, x_262);
x_269 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_244, x_268, x_6, x_7, x_8, x_9, x_267);
if (lean_obj_tag(x_269) == 0)
{
uint8_t x_270; 
x_270 = !lean_is_exclusive(x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_269, 0);
x_272 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_272, 0, x_266);
lean_ctor_set(x_272, 1, x_271);
if (lean_is_scalar(x_22)) {
 x_273 = lean_alloc_ctor(1, 1, 0);
} else {
 x_273 = x_22;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_269, 0, x_273);
return x_269;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_274 = lean_ctor_get(x_269, 0);
x_275 = lean_ctor_get(x_269, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_269);
x_276 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_276, 0, x_266);
lean_ctor_set(x_276, 1, x_274);
if (lean_is_scalar(x_22)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_22;
}
lean_ctor_set(x_277, 0, x_276);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_275);
return x_278;
}
}
else
{
uint8_t x_279; 
lean_dec(x_266);
lean_dec(x_22);
x_279 = !lean_is_exclusive(x_269);
if (x_279 == 0)
{
return x_269;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_269, 0);
x_281 = lean_ctor_get(x_269, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_269);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_244);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_283 = !lean_is_exclusive(x_265);
if (x_283 == 0)
{
return x_265;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_265, 0);
x_285 = lean_ctor_get(x_265, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_265);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_251);
x_328 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_329 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_330 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_328, x_244, x_329, x_6, x_7, x_8, x_9, x_252);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_333 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_331, x_6, x_7, x_8, x_9, x_332);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec(x_333);
x_336 = lean_ctor_get(x_334, 0);
lean_inc(x_336);
x_337 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_337 == 0)
{
lean_object* x_352; 
lean_dec(x_27);
lean_dec(x_23);
x_352 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_336, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_335);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
lean_dec(x_352);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_354 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_353);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
x_338 = x_355;
x_339 = x_356;
goto block_351;
}
else
{
uint8_t x_357; 
lean_dec(x_334);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_357 = !lean_is_exclusive(x_354);
if (x_357 == 0)
{
return x_354;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_354, 0);
x_359 = lean_ctor_get(x_354, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_354);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
}
}
else
{
uint8_t x_361; 
lean_dec(x_334);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_361 = !lean_is_exclusive(x_352);
if (x_361 == 0)
{
return x_352;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_352, 0);
x_363 = lean_ctor_get(x_352, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_352);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_365 = lean_array_get_size(x_23);
x_366 = l_Array_toSubarray___rarg(x_23, x_27, x_365);
x_367 = l_Array_ofSubarray___rarg(x_366);
x_368 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_368, 0, x_336);
lean_ctor_set(x_368, 1, x_367);
x_369 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_370 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_368, x_369, x_6, x_7, x_8, x_9, x_335);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = lean_ctor_get(x_371, 0);
lean_inc(x_373);
x_374 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_373, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_372);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_374, 1);
lean_inc(x_375);
lean_dec(x_374);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_371);
lean_ctor_set(x_376, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_377 = l_Lean_Compiler_LCNF_Simp_simp(x_376, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_375);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_338 = x_378;
x_339 = x_379;
goto block_351;
}
else
{
uint8_t x_380; 
lean_dec(x_334);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_380 = !lean_is_exclusive(x_377);
if (x_380 == 0)
{
return x_377;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_377, 0);
x_382 = lean_ctor_get(x_377, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_377);
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
lean_dec(x_371);
lean_dec(x_334);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_384 = !lean_is_exclusive(x_374);
if (x_384 == 0)
{
return x_374;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_374, 0);
x_386 = lean_ctor_get(x_374, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_374);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
}
else
{
uint8_t x_388; 
lean_dec(x_334);
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
x_388 = !lean_is_exclusive(x_370);
if (x_388 == 0)
{
return x_370;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_370, 0);
x_390 = lean_ctor_get(x_370, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_370);
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
}
}
block_351:
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_334);
x_341 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_342 = lean_array_push(x_341, x_340);
x_343 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_342, x_338, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_339);
lean_dec(x_342);
x_344 = !lean_is_exclusive(x_343);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_ctor_get(x_343, 0);
if (lean_is_scalar(x_22)) {
 x_346 = lean_alloc_ctor(1, 1, 0);
} else {
 x_346 = x_22;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_343, 0, x_346);
return x_343;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_347 = lean_ctor_get(x_343, 0);
x_348 = lean_ctor_get(x_343, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_343);
if (lean_is_scalar(x_22)) {
 x_349 = lean_alloc_ctor(1, 1, 0);
} else {
 x_349 = x_22;
}
lean_ctor_set(x_349, 0, x_347);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
}
else
{
uint8_t x_392; 
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
x_392 = !lean_is_exclusive(x_333);
if (x_392 == 0)
{
return x_333;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_333, 0);
x_394 = lean_ctor_get(x_333, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_333);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
}
}
else
{
uint8_t x_396; 
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
x_396 = !lean_is_exclusive(x_330);
if (x_396 == 0)
{
return x_330;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_330, 0);
x_398 = lean_ctor_get(x_330, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_330);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
return x_399;
}
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_33);
lean_dec(x_21);
x_400 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_245);
x_401 = lean_ctor_get(x_400, 1);
lean_inc(x_401);
lean_dec(x_400);
x_402 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_402, 0, x_3);
lean_closure_set(x_402, 1, x_4);
lean_closure_set(x_402, 2, x_5);
lean_closure_set(x_402, 3, x_27);
lean_closure_set(x_402, 4, x_24);
lean_closure_set(x_402, 5, x_26);
lean_closure_set(x_402, 6, x_2);
lean_closure_set(x_402, 7, x_23);
x_403 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_244, x_402, x_6, x_7, x_8, x_9, x_401);
if (lean_obj_tag(x_403) == 0)
{
uint8_t x_404; 
x_404 = !lean_is_exclusive(x_403);
if (x_404 == 0)
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_ctor_get(x_403, 0);
if (lean_is_scalar(x_22)) {
 x_406 = lean_alloc_ctor(1, 1, 0);
} else {
 x_406 = x_22;
}
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_403, 0, x_406);
return x_403;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_407 = lean_ctor_get(x_403, 0);
x_408 = lean_ctor_get(x_403, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_403);
if (lean_is_scalar(x_22)) {
 x_409 = lean_alloc_ctor(1, 1, 0);
} else {
 x_409 = x_22;
}
lean_ctor_set(x_409, 0, x_407);
x_410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
else
{
uint8_t x_411; 
lean_dec(x_22);
x_411 = !lean_is_exclusive(x_403);
if (x_411 == 0)
{
return x_403;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_403, 0);
x_413 = lean_ctor_get(x_403, 1);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_403);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
}
else
{
uint8_t x_415; 
lean_dec(x_33);
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
x_415 = !lean_is_exclusive(x_243);
if (x_415 == 0)
{
return x_243;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_243, 0);
x_417 = lean_ctor_get(x_243, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_243);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
return x_418;
}
}
}
}
else
{
uint8_t x_438; 
lean_dec(x_33);
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
x_438 = !lean_is_exclusive(x_239);
if (x_438 == 0)
{
return x_239;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_239, 0);
x_440 = lean_ctor_get(x_239, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_239);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
}
}
case 2:
{
uint8_t x_442; lean_object* x_443; 
lean_dec(x_11);
x_442 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_443 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_442, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_624; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_624 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_624 == 0)
{
lean_object* x_625; 
x_625 = lean_box(0);
x_446 = x_625;
goto block_623;
}
else
{
uint8_t x_626; 
x_626 = lean_nat_dec_eq(x_24, x_27);
if (x_626 == 0)
{
lean_object* x_627; 
x_627 = lean_box(0);
x_446 = x_627;
goto block_623;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_628 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_445);
x_629 = lean_ctor_get(x_628, 1);
lean_inc(x_629);
lean_dec(x_628);
x_630 = l_Lean_Compiler_LCNF_Simp_simp(x_444, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_629);
if (lean_obj_tag(x_630) == 0)
{
uint8_t x_631; 
x_631 = !lean_is_exclusive(x_630);
if (x_631 == 0)
{
lean_object* x_632; lean_object* x_633; 
x_632 = lean_ctor_get(x_630, 0);
x_633 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_630, 0, x_633);
return x_630;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_634 = lean_ctor_get(x_630, 0);
x_635 = lean_ctor_get(x_630, 1);
lean_inc(x_635);
lean_inc(x_634);
lean_dec(x_630);
x_636 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_636, 0, x_634);
x_637 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_637, 1, x_635);
return x_637;
}
}
else
{
uint8_t x_638; 
x_638 = !lean_is_exclusive(x_630);
if (x_638 == 0)
{
return x_630;
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_639 = lean_ctor_get(x_630, 0);
x_640 = lean_ctor_get(x_630, 1);
lean_inc(x_640);
lean_inc(x_639);
lean_dec(x_630);
x_641 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_641, 0, x_639);
lean_ctor_set(x_641, 1, x_640);
return x_641;
}
}
}
}
block_623:
{
lean_object* x_447; 
lean_dec(x_446);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_447 = l_Lean_Compiler_LCNF_Simp_simp(x_444, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_445);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; uint8_t x_450; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec(x_447);
lean_inc(x_448);
x_450 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_448);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; 
x_451 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_449);
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec(x_451);
x_453 = lean_ctor_get(x_21, 2);
lean_inc(x_453);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_454 = l_Lean_Compiler_LCNF_inferAppType(x_453, x_33, x_6, x_7, x_8, x_9, x_452);
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
lean_dec(x_454);
lean_inc(x_455);
x_457 = l_Lean_Expr_headBeta(x_455);
x_458 = l_Lean_Expr_isForall(x_457);
lean_dec(x_457);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; 
x_459 = l_Lean_Compiler_LCNF_mkAuxParam(x_455, x_442, x_6, x_7, x_8, x_9, x_456);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_462 = lean_ctor_get(x_460, 0);
lean_inc(x_462);
x_463 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_463 == 0)
{
lean_object* x_492; 
lean_dec(x_27);
lean_dec(x_23);
x_492 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_462, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_461);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; 
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
lean_dec(x_492);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_494 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_493);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_464 = x_495;
x_465 = x_496;
goto block_491;
}
else
{
uint8_t x_497; 
lean_dec(x_460);
lean_dec(x_448);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_497 = !lean_is_exclusive(x_494);
if (x_497 == 0)
{
return x_494;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_494, 0);
x_499 = lean_ctor_get(x_494, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_494);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
}
}
}
else
{
uint8_t x_501; 
lean_dec(x_460);
lean_dec(x_448);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_501 = !lean_is_exclusive(x_492);
if (x_501 == 0)
{
return x_492;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_492, 0);
x_503 = lean_ctor_get(x_492, 1);
lean_inc(x_503);
lean_inc(x_502);
lean_dec(x_492);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
return x_504;
}
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_505 = lean_array_get_size(x_23);
x_506 = l_Array_toSubarray___rarg(x_23, x_27, x_505);
x_507 = l_Array_ofSubarray___rarg(x_506);
x_508 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_508, 0, x_462);
lean_ctor_set(x_508, 1, x_507);
x_509 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_510 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_508, x_509, x_6, x_7, x_8, x_9, x_461);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_513 = lean_ctor_get(x_511, 0);
lean_inc(x_513);
x_514 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_513, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_512);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
lean_dec(x_514);
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_511);
lean_ctor_set(x_516, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_517 = l_Lean_Compiler_LCNF_Simp_simp(x_516, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_515);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec(x_517);
x_464 = x_518;
x_465 = x_519;
goto block_491;
}
else
{
uint8_t x_520; 
lean_dec(x_460);
lean_dec(x_448);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_520 = !lean_is_exclusive(x_517);
if (x_520 == 0)
{
return x_517;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_517, 0);
x_522 = lean_ctor_get(x_517, 1);
lean_inc(x_522);
lean_inc(x_521);
lean_dec(x_517);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_522);
return x_523;
}
}
}
else
{
uint8_t x_524; 
lean_dec(x_511);
lean_dec(x_460);
lean_dec(x_448);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_524 = !lean_is_exclusive(x_514);
if (x_524 == 0)
{
return x_514;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_514, 0);
x_526 = lean_ctor_get(x_514, 1);
lean_inc(x_526);
lean_inc(x_525);
lean_dec(x_514);
x_527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_527, 0, x_525);
lean_ctor_set(x_527, 1, x_526);
return x_527;
}
}
}
else
{
uint8_t x_528; 
lean_dec(x_460);
lean_dec(x_448);
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
x_528 = !lean_is_exclusive(x_510);
if (x_528 == 0)
{
return x_510;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_510, 0);
x_530 = lean_ctor_get(x_510, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_510);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
return x_531;
}
}
}
block_491:
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_466 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_467 = lean_array_push(x_466, x_460);
x_468 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_469 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_467, x_464, x_468, x_6, x_7, x_8, x_9, x_465);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
lean_inc(x_470);
x_472 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_472, 0, x_470);
lean_closure_set(x_472, 1, x_466);
x_473 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_448, x_472, x_6, x_7, x_8, x_9, x_471);
if (lean_obj_tag(x_473) == 0)
{
uint8_t x_474; 
x_474 = !lean_is_exclusive(x_473);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_473, 0);
x_476 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_476, 0, x_470);
lean_ctor_set(x_476, 1, x_475);
if (lean_is_scalar(x_22)) {
 x_477 = lean_alloc_ctor(1, 1, 0);
} else {
 x_477 = x_22;
}
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_473, 0, x_477);
return x_473;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_478 = lean_ctor_get(x_473, 0);
x_479 = lean_ctor_get(x_473, 1);
lean_inc(x_479);
lean_inc(x_478);
lean_dec(x_473);
x_480 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_480, 0, x_470);
lean_ctor_set(x_480, 1, x_478);
if (lean_is_scalar(x_22)) {
 x_481 = lean_alloc_ctor(1, 1, 0);
} else {
 x_481 = x_22;
}
lean_ctor_set(x_481, 0, x_480);
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_479);
return x_482;
}
}
else
{
uint8_t x_483; 
lean_dec(x_470);
lean_dec(x_22);
x_483 = !lean_is_exclusive(x_473);
if (x_483 == 0)
{
return x_473;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_473, 0);
x_485 = lean_ctor_get(x_473, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_473);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
else
{
uint8_t x_487; 
lean_dec(x_448);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_487 = !lean_is_exclusive(x_469);
if (x_487 == 0)
{
return x_469;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_469, 0);
x_489 = lean_ctor_get(x_469, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_469);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_455);
x_532 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_533 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_534 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_532, x_448, x_533, x_6, x_7, x_8, x_9, x_456);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_537 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_535, x_6, x_7, x_8, x_9, x_536);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; lean_object* x_543; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_540 = lean_ctor_get(x_538, 0);
lean_inc(x_540);
x_541 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_541 == 0)
{
lean_object* x_556; 
lean_dec(x_27);
lean_dec(x_23);
x_556 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_540, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_539);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; 
x_557 = lean_ctor_get(x_556, 1);
lean_inc(x_557);
lean_dec(x_556);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_558 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_557);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
lean_dec(x_558);
x_542 = x_559;
x_543 = x_560;
goto block_555;
}
else
{
uint8_t x_561; 
lean_dec(x_538);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_561 = !lean_is_exclusive(x_558);
if (x_561 == 0)
{
return x_558;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_558, 0);
x_563 = lean_ctor_get(x_558, 1);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_558);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
return x_564;
}
}
}
else
{
uint8_t x_565; 
lean_dec(x_538);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_565 = !lean_is_exclusive(x_556);
if (x_565 == 0)
{
return x_556;
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_566 = lean_ctor_get(x_556, 0);
x_567 = lean_ctor_get(x_556, 1);
lean_inc(x_567);
lean_inc(x_566);
lean_dec(x_556);
x_568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_568, 0, x_566);
lean_ctor_set(x_568, 1, x_567);
return x_568;
}
}
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_569 = lean_array_get_size(x_23);
x_570 = l_Array_toSubarray___rarg(x_23, x_27, x_569);
x_571 = l_Array_ofSubarray___rarg(x_570);
x_572 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_572, 0, x_540);
lean_ctor_set(x_572, 1, x_571);
x_573 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_574 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_572, x_573, x_6, x_7, x_8, x_9, x_539);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec(x_574);
x_577 = lean_ctor_get(x_575, 0);
lean_inc(x_577);
x_578 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_577, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_576);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_578, 1);
lean_inc(x_579);
lean_dec(x_578);
x_580 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_580, 0, x_575);
lean_ctor_set(x_580, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_581 = l_Lean_Compiler_LCNF_Simp_simp(x_580, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_579);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_581, 1);
lean_inc(x_583);
lean_dec(x_581);
x_542 = x_582;
x_543 = x_583;
goto block_555;
}
else
{
uint8_t x_584; 
lean_dec(x_538);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_584 = !lean_is_exclusive(x_581);
if (x_584 == 0)
{
return x_581;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_581, 0);
x_586 = lean_ctor_get(x_581, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_581);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
return x_587;
}
}
}
else
{
uint8_t x_588; 
lean_dec(x_575);
lean_dec(x_538);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_588 = !lean_is_exclusive(x_578);
if (x_588 == 0)
{
return x_578;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_589 = lean_ctor_get(x_578, 0);
x_590 = lean_ctor_get(x_578, 1);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_578);
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_589);
lean_ctor_set(x_591, 1, x_590);
return x_591;
}
}
}
else
{
uint8_t x_592; 
lean_dec(x_538);
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
x_592 = !lean_is_exclusive(x_574);
if (x_592 == 0)
{
return x_574;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_593 = lean_ctor_get(x_574, 0);
x_594 = lean_ctor_get(x_574, 1);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_574);
x_595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_595, 0, x_593);
lean_ctor_set(x_595, 1, x_594);
return x_595;
}
}
}
block_555:
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; 
x_544 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_544, 0, x_538);
x_545 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_546 = lean_array_push(x_545, x_544);
x_547 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_546, x_542, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_543);
lean_dec(x_546);
x_548 = !lean_is_exclusive(x_547);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; 
x_549 = lean_ctor_get(x_547, 0);
if (lean_is_scalar(x_22)) {
 x_550 = lean_alloc_ctor(1, 1, 0);
} else {
 x_550 = x_22;
}
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_547, 0, x_550);
return x_547;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_551 = lean_ctor_get(x_547, 0);
x_552 = lean_ctor_get(x_547, 1);
lean_inc(x_552);
lean_inc(x_551);
lean_dec(x_547);
if (lean_is_scalar(x_22)) {
 x_553 = lean_alloc_ctor(1, 1, 0);
} else {
 x_553 = x_22;
}
lean_ctor_set(x_553, 0, x_551);
x_554 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_552);
return x_554;
}
}
}
else
{
uint8_t x_596; 
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
x_596 = !lean_is_exclusive(x_537);
if (x_596 == 0)
{
return x_537;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_537, 0);
x_598 = lean_ctor_get(x_537, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_537);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
else
{
uint8_t x_600; 
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
x_600 = !lean_is_exclusive(x_534);
if (x_600 == 0)
{
return x_534;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_534, 0);
x_602 = lean_ctor_get(x_534, 1);
lean_inc(x_602);
lean_inc(x_601);
lean_dec(x_534);
x_603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set(x_603, 1, x_602);
return x_603;
}
}
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_33);
lean_dec(x_21);
x_604 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_449);
x_605 = lean_ctor_get(x_604, 1);
lean_inc(x_605);
lean_dec(x_604);
x_606 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_606, 0, x_3);
lean_closure_set(x_606, 1, x_4);
lean_closure_set(x_606, 2, x_5);
lean_closure_set(x_606, 3, x_27);
lean_closure_set(x_606, 4, x_24);
lean_closure_set(x_606, 5, x_26);
lean_closure_set(x_606, 6, x_2);
lean_closure_set(x_606, 7, x_23);
x_607 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_448, x_606, x_6, x_7, x_8, x_9, x_605);
if (lean_obj_tag(x_607) == 0)
{
uint8_t x_608; 
x_608 = !lean_is_exclusive(x_607);
if (x_608 == 0)
{
lean_object* x_609; lean_object* x_610; 
x_609 = lean_ctor_get(x_607, 0);
if (lean_is_scalar(x_22)) {
 x_610 = lean_alloc_ctor(1, 1, 0);
} else {
 x_610 = x_22;
}
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_607, 0, x_610);
return x_607;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_607, 0);
x_612 = lean_ctor_get(x_607, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_607);
if (lean_is_scalar(x_22)) {
 x_613 = lean_alloc_ctor(1, 1, 0);
} else {
 x_613 = x_22;
}
lean_ctor_set(x_613, 0, x_611);
x_614 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_612);
return x_614;
}
}
else
{
uint8_t x_615; 
lean_dec(x_22);
x_615 = !lean_is_exclusive(x_607);
if (x_615 == 0)
{
return x_607;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_607, 0);
x_617 = lean_ctor_get(x_607, 1);
lean_inc(x_617);
lean_inc(x_616);
lean_dec(x_607);
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_616);
lean_ctor_set(x_618, 1, x_617);
return x_618;
}
}
}
}
else
{
uint8_t x_619; 
lean_dec(x_33);
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
x_619 = !lean_is_exclusive(x_447);
if (x_619 == 0)
{
return x_447;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_447, 0);
x_621 = lean_ctor_get(x_447, 1);
lean_inc(x_621);
lean_inc(x_620);
lean_dec(x_447);
x_622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_622, 0, x_620);
lean_ctor_set(x_622, 1, x_621);
return x_622;
}
}
}
}
else
{
uint8_t x_642; 
lean_dec(x_33);
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
x_642 = !lean_is_exclusive(x_443);
if (x_642 == 0)
{
return x_443;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_643 = lean_ctor_get(x_443, 0);
x_644 = lean_ctor_get(x_443, 1);
lean_inc(x_644);
lean_inc(x_643);
lean_dec(x_443);
x_645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_645, 0, x_643);
lean_ctor_set(x_645, 1, x_644);
return x_645;
}
}
}
case 3:
{
lean_object* x_646; lean_object* x_647; 
x_646 = lean_ctor_get(x_11, 0);
lean_inc(x_646);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_646);
x_647 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_646, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; lean_object* x_649; uint8_t x_650; 
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_647, 1);
lean_inc(x_649);
lean_dec(x_647);
x_650 = !lean_is_exclusive(x_3);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; lean_object* x_656; 
x_651 = lean_ctor_get(x_3, 2);
x_652 = lean_ctor_get(x_3, 3);
lean_inc(x_646);
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_646);
lean_ctor_set(x_653, 1, x_651);
x_654 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_652, x_646, x_648);
lean_ctor_set(x_3, 3, x_654);
lean_ctor_set(x_3, 2, x_653);
x_655 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_656 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_655, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_649);
lean_dec(x_29);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_837; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
x_837 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_837 == 0)
{
lean_object* x_838; 
x_838 = lean_box(0);
x_659 = x_838;
goto block_836;
}
else
{
uint8_t x_839; 
x_839 = lean_nat_dec_eq(x_24, x_27);
if (x_839 == 0)
{
lean_object* x_840; 
x_840 = lean_box(0);
x_659 = x_840;
goto block_836;
}
else
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_841 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_658);
x_842 = lean_ctor_get(x_841, 1);
lean_inc(x_842);
lean_dec(x_841);
x_843 = l_Lean_Compiler_LCNF_Simp_simp(x_657, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_842);
if (lean_obj_tag(x_843) == 0)
{
uint8_t x_844; 
x_844 = !lean_is_exclusive(x_843);
if (x_844 == 0)
{
lean_object* x_845; lean_object* x_846; 
x_845 = lean_ctor_get(x_843, 0);
x_846 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_846, 0, x_845);
lean_ctor_set(x_843, 0, x_846);
return x_843;
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
x_847 = lean_ctor_get(x_843, 0);
x_848 = lean_ctor_get(x_843, 1);
lean_inc(x_848);
lean_inc(x_847);
lean_dec(x_843);
x_849 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_849, 0, x_847);
x_850 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_850, 0, x_849);
lean_ctor_set(x_850, 1, x_848);
return x_850;
}
}
else
{
uint8_t x_851; 
x_851 = !lean_is_exclusive(x_843);
if (x_851 == 0)
{
return x_843;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_852 = lean_ctor_get(x_843, 0);
x_853 = lean_ctor_get(x_843, 1);
lean_inc(x_853);
lean_inc(x_852);
lean_dec(x_843);
x_854 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_854, 0, x_852);
lean_ctor_set(x_854, 1, x_853);
return x_854;
}
}
}
}
block_836:
{
lean_object* x_660; 
lean_dec(x_659);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_660 = l_Lean_Compiler_LCNF_Simp_simp(x_657, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_658);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; uint8_t x_663; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
lean_dec(x_660);
lean_inc(x_661);
x_663 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_661);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; uint8_t x_671; 
x_664 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_662);
x_665 = lean_ctor_get(x_664, 1);
lean_inc(x_665);
lean_dec(x_664);
x_666 = lean_ctor_get(x_21, 2);
lean_inc(x_666);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_667 = l_Lean_Compiler_LCNF_inferAppType(x_666, x_33, x_6, x_7, x_8, x_9, x_665);
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
x_669 = lean_ctor_get(x_667, 1);
lean_inc(x_669);
lean_dec(x_667);
lean_inc(x_668);
x_670 = l_Lean_Expr_headBeta(x_668);
x_671 = l_Lean_Expr_isForall(x_670);
lean_dec(x_670);
if (x_671 == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; lean_object* x_677; lean_object* x_678; 
x_672 = l_Lean_Compiler_LCNF_mkAuxParam(x_668, x_655, x_6, x_7, x_8, x_9, x_669);
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec(x_672);
x_675 = lean_ctor_get(x_673, 0);
lean_inc(x_675);
x_676 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_676 == 0)
{
lean_object* x_705; 
lean_dec(x_27);
lean_dec(x_23);
x_705 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_675, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_674);
if (lean_obj_tag(x_705) == 0)
{
lean_object* x_706; lean_object* x_707; 
x_706 = lean_ctor_get(x_705, 1);
lean_inc(x_706);
lean_dec(x_705);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_707 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_706);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; lean_object* x_709; 
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
lean_dec(x_707);
x_677 = x_708;
x_678 = x_709;
goto block_704;
}
else
{
uint8_t x_710; 
lean_dec(x_673);
lean_dec(x_661);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_710 = !lean_is_exclusive(x_707);
if (x_710 == 0)
{
return x_707;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_711 = lean_ctor_get(x_707, 0);
x_712 = lean_ctor_get(x_707, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_707);
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
lean_dec(x_673);
lean_dec(x_661);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_714 = !lean_is_exclusive(x_705);
if (x_714 == 0)
{
return x_705;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_705, 0);
x_716 = lean_ctor_get(x_705, 1);
lean_inc(x_716);
lean_inc(x_715);
lean_dec(x_705);
x_717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
return x_717;
}
}
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_718 = lean_array_get_size(x_23);
x_719 = l_Array_toSubarray___rarg(x_23, x_27, x_718);
x_720 = l_Array_ofSubarray___rarg(x_719);
x_721 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_721, 0, x_675);
lean_ctor_set(x_721, 1, x_720);
x_722 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_723 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_721, x_722, x_6, x_7, x_8, x_9, x_674);
if (lean_obj_tag(x_723) == 0)
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
x_726 = lean_ctor_get(x_724, 0);
lean_inc(x_726);
x_727 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_726, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_725);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
lean_dec(x_727);
x_729 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_729, 0, x_724);
lean_ctor_set(x_729, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_730 = l_Lean_Compiler_LCNF_Simp_simp(x_729, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_728);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_731; lean_object* x_732; 
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec(x_730);
x_677 = x_731;
x_678 = x_732;
goto block_704;
}
else
{
uint8_t x_733; 
lean_dec(x_673);
lean_dec(x_661);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_733 = !lean_is_exclusive(x_730);
if (x_733 == 0)
{
return x_730;
}
else
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_734 = lean_ctor_get(x_730, 0);
x_735 = lean_ctor_get(x_730, 1);
lean_inc(x_735);
lean_inc(x_734);
lean_dec(x_730);
x_736 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_736, 0, x_734);
lean_ctor_set(x_736, 1, x_735);
return x_736;
}
}
}
else
{
uint8_t x_737; 
lean_dec(x_724);
lean_dec(x_673);
lean_dec(x_661);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_737 = !lean_is_exclusive(x_727);
if (x_737 == 0)
{
return x_727;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_738 = lean_ctor_get(x_727, 0);
x_739 = lean_ctor_get(x_727, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_727);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_738);
lean_ctor_set(x_740, 1, x_739);
return x_740;
}
}
}
else
{
uint8_t x_741; 
lean_dec(x_673);
lean_dec(x_661);
lean_dec(x_3);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_741 = !lean_is_exclusive(x_723);
if (x_741 == 0)
{
return x_723;
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_742 = lean_ctor_get(x_723, 0);
x_743 = lean_ctor_get(x_723, 1);
lean_inc(x_743);
lean_inc(x_742);
lean_dec(x_723);
x_744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_744, 0, x_742);
lean_ctor_set(x_744, 1, x_743);
return x_744;
}
}
}
block_704:
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_679 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_680 = lean_array_push(x_679, x_673);
x_681 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_682 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_680, x_677, x_681, x_6, x_7, x_8, x_9, x_678);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_682, 1);
lean_inc(x_684);
lean_dec(x_682);
lean_inc(x_683);
x_685 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_685, 0, x_683);
lean_closure_set(x_685, 1, x_679);
x_686 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_661, x_685, x_6, x_7, x_8, x_9, x_684);
if (lean_obj_tag(x_686) == 0)
{
uint8_t x_687; 
x_687 = !lean_is_exclusive(x_686);
if (x_687 == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_688 = lean_ctor_get(x_686, 0);
x_689 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_689, 0, x_683);
lean_ctor_set(x_689, 1, x_688);
if (lean_is_scalar(x_22)) {
 x_690 = lean_alloc_ctor(1, 1, 0);
} else {
 x_690 = x_22;
}
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_686, 0, x_690);
return x_686;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_691 = lean_ctor_get(x_686, 0);
x_692 = lean_ctor_get(x_686, 1);
lean_inc(x_692);
lean_inc(x_691);
lean_dec(x_686);
x_693 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_693, 0, x_683);
lean_ctor_set(x_693, 1, x_691);
if (lean_is_scalar(x_22)) {
 x_694 = lean_alloc_ctor(1, 1, 0);
} else {
 x_694 = x_22;
}
lean_ctor_set(x_694, 0, x_693);
x_695 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_692);
return x_695;
}
}
else
{
uint8_t x_696; 
lean_dec(x_683);
lean_dec(x_22);
x_696 = !lean_is_exclusive(x_686);
if (x_696 == 0)
{
return x_686;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_697 = lean_ctor_get(x_686, 0);
x_698 = lean_ctor_get(x_686, 1);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_686);
x_699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_698);
return x_699;
}
}
}
else
{
uint8_t x_700; 
lean_dec(x_661);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_700 = !lean_is_exclusive(x_682);
if (x_700 == 0)
{
return x_682;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_701 = lean_ctor_get(x_682, 0);
x_702 = lean_ctor_get(x_682, 1);
lean_inc(x_702);
lean_inc(x_701);
lean_dec(x_682);
x_703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_703, 0, x_701);
lean_ctor_set(x_703, 1, x_702);
return x_703;
}
}
}
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; 
lean_dec(x_668);
x_745 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_746 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_747 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_745, x_661, x_746, x_6, x_7, x_8, x_9, x_669);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_747, 1);
lean_inc(x_749);
lean_dec(x_747);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_750 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_748, x_6, x_7, x_8, x_9, x_749);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; uint8_t x_754; lean_object* x_755; lean_object* x_756; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
lean_dec(x_750);
x_753 = lean_ctor_get(x_751, 0);
lean_inc(x_753);
x_754 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_754 == 0)
{
lean_object* x_769; 
lean_dec(x_27);
lean_dec(x_23);
x_769 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_753, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_752);
if (lean_obj_tag(x_769) == 0)
{
lean_object* x_770; lean_object* x_771; 
x_770 = lean_ctor_get(x_769, 1);
lean_inc(x_770);
lean_dec(x_769);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_771 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_770);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec(x_771);
x_755 = x_772;
x_756 = x_773;
goto block_768;
}
else
{
uint8_t x_774; 
lean_dec(x_751);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_774 = !lean_is_exclusive(x_771);
if (x_774 == 0)
{
return x_771;
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_775 = lean_ctor_get(x_771, 0);
x_776 = lean_ctor_get(x_771, 1);
lean_inc(x_776);
lean_inc(x_775);
lean_dec(x_771);
x_777 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_777, 0, x_775);
lean_ctor_set(x_777, 1, x_776);
return x_777;
}
}
}
else
{
uint8_t x_778; 
lean_dec(x_751);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_778 = !lean_is_exclusive(x_769);
if (x_778 == 0)
{
return x_769;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_779 = lean_ctor_get(x_769, 0);
x_780 = lean_ctor_get(x_769, 1);
lean_inc(x_780);
lean_inc(x_779);
lean_dec(x_769);
x_781 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_781, 0, x_779);
lean_ctor_set(x_781, 1, x_780);
return x_781;
}
}
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_782 = lean_array_get_size(x_23);
x_783 = l_Array_toSubarray___rarg(x_23, x_27, x_782);
x_784 = l_Array_ofSubarray___rarg(x_783);
x_785 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_785, 0, x_753);
lean_ctor_set(x_785, 1, x_784);
x_786 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_787 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_785, x_786, x_6, x_7, x_8, x_9, x_752);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_787, 1);
lean_inc(x_789);
lean_dec(x_787);
x_790 = lean_ctor_get(x_788, 0);
lean_inc(x_790);
x_791 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_790, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_789);
if (lean_obj_tag(x_791) == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_792 = lean_ctor_get(x_791, 1);
lean_inc(x_792);
lean_dec(x_791);
x_793 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_793, 0, x_788);
lean_ctor_set(x_793, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_794 = l_Lean_Compiler_LCNF_Simp_simp(x_793, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_792);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; 
x_795 = lean_ctor_get(x_794, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_794, 1);
lean_inc(x_796);
lean_dec(x_794);
x_755 = x_795;
x_756 = x_796;
goto block_768;
}
else
{
uint8_t x_797; 
lean_dec(x_751);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_797 = !lean_is_exclusive(x_794);
if (x_797 == 0)
{
return x_794;
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; 
x_798 = lean_ctor_get(x_794, 0);
x_799 = lean_ctor_get(x_794, 1);
lean_inc(x_799);
lean_inc(x_798);
lean_dec(x_794);
x_800 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_800, 0, x_798);
lean_ctor_set(x_800, 1, x_799);
return x_800;
}
}
}
else
{
uint8_t x_801; 
lean_dec(x_788);
lean_dec(x_751);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_801 = !lean_is_exclusive(x_791);
if (x_801 == 0)
{
return x_791;
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_802 = lean_ctor_get(x_791, 0);
x_803 = lean_ctor_get(x_791, 1);
lean_inc(x_803);
lean_inc(x_802);
lean_dec(x_791);
x_804 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_804, 0, x_802);
lean_ctor_set(x_804, 1, x_803);
return x_804;
}
}
}
else
{
uint8_t x_805; 
lean_dec(x_751);
lean_dec(x_3);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_805 = !lean_is_exclusive(x_787);
if (x_805 == 0)
{
return x_787;
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_806 = lean_ctor_get(x_787, 0);
x_807 = lean_ctor_get(x_787, 1);
lean_inc(x_807);
lean_inc(x_806);
lean_dec(x_787);
x_808 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_808, 0, x_806);
lean_ctor_set(x_808, 1, x_807);
return x_808;
}
}
}
block_768:
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; uint8_t x_761; 
x_757 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_757, 0, x_751);
x_758 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_759 = lean_array_push(x_758, x_757);
x_760 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_759, x_755, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_756);
lean_dec(x_759);
x_761 = !lean_is_exclusive(x_760);
if (x_761 == 0)
{
lean_object* x_762; lean_object* x_763; 
x_762 = lean_ctor_get(x_760, 0);
if (lean_is_scalar(x_22)) {
 x_763 = lean_alloc_ctor(1, 1, 0);
} else {
 x_763 = x_22;
}
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_760, 0, x_763);
return x_760;
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; 
x_764 = lean_ctor_get(x_760, 0);
x_765 = lean_ctor_get(x_760, 1);
lean_inc(x_765);
lean_inc(x_764);
lean_dec(x_760);
if (lean_is_scalar(x_22)) {
 x_766 = lean_alloc_ctor(1, 1, 0);
} else {
 x_766 = x_22;
}
lean_ctor_set(x_766, 0, x_764);
x_767 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_765);
return x_767;
}
}
}
else
{
uint8_t x_809; 
lean_dec(x_3);
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
x_809 = !lean_is_exclusive(x_750);
if (x_809 == 0)
{
return x_750;
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_810 = lean_ctor_get(x_750, 0);
x_811 = lean_ctor_get(x_750, 1);
lean_inc(x_811);
lean_inc(x_810);
lean_dec(x_750);
x_812 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_812, 0, x_810);
lean_ctor_set(x_812, 1, x_811);
return x_812;
}
}
}
else
{
uint8_t x_813; 
lean_dec(x_3);
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
x_813 = !lean_is_exclusive(x_747);
if (x_813 == 0)
{
return x_747;
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_814 = lean_ctor_get(x_747, 0);
x_815 = lean_ctor_get(x_747, 1);
lean_inc(x_815);
lean_inc(x_814);
lean_dec(x_747);
x_816 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_816, 0, x_814);
lean_ctor_set(x_816, 1, x_815);
return x_816;
}
}
}
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_dec(x_33);
lean_dec(x_21);
x_817 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_662);
x_818 = lean_ctor_get(x_817, 1);
lean_inc(x_818);
lean_dec(x_817);
x_819 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_819, 0, x_3);
lean_closure_set(x_819, 1, x_4);
lean_closure_set(x_819, 2, x_5);
lean_closure_set(x_819, 3, x_27);
lean_closure_set(x_819, 4, x_24);
lean_closure_set(x_819, 5, x_26);
lean_closure_set(x_819, 6, x_2);
lean_closure_set(x_819, 7, x_23);
x_820 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_661, x_819, x_6, x_7, x_8, x_9, x_818);
if (lean_obj_tag(x_820) == 0)
{
uint8_t x_821; 
x_821 = !lean_is_exclusive(x_820);
if (x_821 == 0)
{
lean_object* x_822; lean_object* x_823; 
x_822 = lean_ctor_get(x_820, 0);
if (lean_is_scalar(x_22)) {
 x_823 = lean_alloc_ctor(1, 1, 0);
} else {
 x_823 = x_22;
}
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_820, 0, x_823);
return x_820;
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_824 = lean_ctor_get(x_820, 0);
x_825 = lean_ctor_get(x_820, 1);
lean_inc(x_825);
lean_inc(x_824);
lean_dec(x_820);
if (lean_is_scalar(x_22)) {
 x_826 = lean_alloc_ctor(1, 1, 0);
} else {
 x_826 = x_22;
}
lean_ctor_set(x_826, 0, x_824);
x_827 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_825);
return x_827;
}
}
else
{
uint8_t x_828; 
lean_dec(x_22);
x_828 = !lean_is_exclusive(x_820);
if (x_828 == 0)
{
return x_820;
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_829 = lean_ctor_get(x_820, 0);
x_830 = lean_ctor_get(x_820, 1);
lean_inc(x_830);
lean_inc(x_829);
lean_dec(x_820);
x_831 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_831, 0, x_829);
lean_ctor_set(x_831, 1, x_830);
return x_831;
}
}
}
}
else
{
uint8_t x_832; 
lean_dec(x_3);
lean_dec(x_33);
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
x_832 = !lean_is_exclusive(x_660);
if (x_832 == 0)
{
return x_660;
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_833 = lean_ctor_get(x_660, 0);
x_834 = lean_ctor_get(x_660, 1);
lean_inc(x_834);
lean_inc(x_833);
lean_dec(x_660);
x_835 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_835, 0, x_833);
lean_ctor_set(x_835, 1, x_834);
return x_835;
}
}
}
}
else
{
uint8_t x_855; 
lean_dec(x_3);
lean_dec(x_33);
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
x_855 = !lean_is_exclusive(x_656);
if (x_855 == 0)
{
return x_656;
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_856 = lean_ctor_get(x_656, 0);
x_857 = lean_ctor_get(x_656, 1);
lean_inc(x_857);
lean_inc(x_856);
lean_dec(x_656);
x_858 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_858, 0, x_856);
lean_ctor_set(x_858, 1, x_857);
return x_858;
}
}
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; uint8_t x_866; lean_object* x_867; 
x_859 = lean_ctor_get(x_3, 0);
x_860 = lean_ctor_get(x_3, 1);
x_861 = lean_ctor_get(x_3, 2);
x_862 = lean_ctor_get(x_3, 3);
lean_inc(x_862);
lean_inc(x_861);
lean_inc(x_860);
lean_inc(x_859);
lean_dec(x_3);
lean_inc(x_646);
x_863 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_863, 0, x_646);
lean_ctor_set(x_863, 1, x_861);
x_864 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_862, x_646, x_648);
x_865 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_865, 0, x_859);
lean_ctor_set(x_865, 1, x_860);
lean_ctor_set(x_865, 2, x_863);
lean_ctor_set(x_865, 3, x_864);
x_866 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_867 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_866, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_649);
lean_dec(x_29);
if (lean_obj_tag(x_867) == 0)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; uint8_t x_1041; 
x_868 = lean_ctor_get(x_867, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_867, 1);
lean_inc(x_869);
lean_dec(x_867);
x_1041 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1041 == 0)
{
lean_object* x_1042; 
x_1042 = lean_box(0);
x_870 = x_1042;
goto block_1040;
}
else
{
uint8_t x_1043; 
x_1043 = lean_nat_dec_eq(x_24, x_27);
if (x_1043 == 0)
{
lean_object* x_1044; 
x_1044 = lean_box(0);
x_870 = x_1044;
goto block_1040;
}
else
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_1045 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_869);
x_1046 = lean_ctor_get(x_1045, 1);
lean_inc(x_1046);
lean_dec(x_1045);
x_1047 = l_Lean_Compiler_LCNF_Simp_simp(x_868, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_1046);
if (lean_obj_tag(x_1047) == 0)
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1048 = lean_ctor_get(x_1047, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1047, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_1047)) {
 lean_ctor_release(x_1047, 0);
 lean_ctor_release(x_1047, 1);
 x_1050 = x_1047;
} else {
 lean_dec_ref(x_1047);
 x_1050 = lean_box(0);
}
x_1051 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1051, 0, x_1048);
if (lean_is_scalar(x_1050)) {
 x_1052 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1052 = x_1050;
}
lean_ctor_set(x_1052, 0, x_1051);
lean_ctor_set(x_1052, 1, x_1049);
return x_1052;
}
else
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1053 = lean_ctor_get(x_1047, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1047, 1);
lean_inc(x_1054);
if (lean_is_exclusive(x_1047)) {
 lean_ctor_release(x_1047, 0);
 lean_ctor_release(x_1047, 1);
 x_1055 = x_1047;
} else {
 lean_dec_ref(x_1047);
 x_1055 = lean_box(0);
}
if (lean_is_scalar(x_1055)) {
 x_1056 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1056 = x_1055;
}
lean_ctor_set(x_1056, 0, x_1053);
lean_ctor_set(x_1056, 1, x_1054);
return x_1056;
}
}
}
block_1040:
{
lean_object* x_871; 
lean_dec(x_870);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_865);
x_871 = l_Lean_Compiler_LCNF_Simp_simp(x_868, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_869);
if (lean_obj_tag(x_871) == 0)
{
lean_object* x_872; lean_object* x_873; uint8_t x_874; 
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_871, 1);
lean_inc(x_873);
lean_dec(x_871);
lean_inc(x_872);
x_874 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_872);
if (x_874 == 0)
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; uint8_t x_882; 
x_875 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_873);
x_876 = lean_ctor_get(x_875, 1);
lean_inc(x_876);
lean_dec(x_875);
x_877 = lean_ctor_get(x_21, 2);
lean_inc(x_877);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_878 = l_Lean_Compiler_LCNF_inferAppType(x_877, x_33, x_6, x_7, x_8, x_9, x_876);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
lean_inc(x_879);
x_881 = l_Lean_Expr_headBeta(x_879);
x_882 = l_Lean_Expr_isForall(x_881);
lean_dec(x_881);
if (x_882 == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; uint8_t x_887; lean_object* x_888; lean_object* x_889; 
x_883 = l_Lean_Compiler_LCNF_mkAuxParam(x_879, x_866, x_6, x_7, x_8, x_9, x_880);
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_883, 1);
lean_inc(x_885);
lean_dec(x_883);
x_886 = lean_ctor_get(x_884, 0);
lean_inc(x_886);
x_887 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_887 == 0)
{
lean_object* x_913; 
lean_dec(x_27);
lean_dec(x_23);
x_913 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_886, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_885);
if (lean_obj_tag(x_913) == 0)
{
lean_object* x_914; lean_object* x_915; 
x_914 = lean_ctor_get(x_913, 1);
lean_inc(x_914);
lean_dec(x_913);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_915 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_914);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec(x_915);
x_888 = x_916;
x_889 = x_917;
goto block_912;
}
else
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
lean_dec(x_884);
lean_dec(x_872);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_918 = lean_ctor_get(x_915, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_915, 1);
lean_inc(x_919);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_920 = x_915;
} else {
 lean_dec_ref(x_915);
 x_920 = lean_box(0);
}
if (lean_is_scalar(x_920)) {
 x_921 = lean_alloc_ctor(1, 2, 0);
} else {
 x_921 = x_920;
}
lean_ctor_set(x_921, 0, x_918);
lean_ctor_set(x_921, 1, x_919);
return x_921;
}
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec(x_884);
lean_dec(x_872);
lean_dec(x_865);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_922 = lean_ctor_get(x_913, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_913, 1);
lean_inc(x_923);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 lean_ctor_release(x_913, 1);
 x_924 = x_913;
} else {
 lean_dec_ref(x_913);
 x_924 = lean_box(0);
}
if (lean_is_scalar(x_924)) {
 x_925 = lean_alloc_ctor(1, 2, 0);
} else {
 x_925 = x_924;
}
lean_ctor_set(x_925, 0, x_922);
lean_ctor_set(x_925, 1, x_923);
return x_925;
}
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; 
x_926 = lean_array_get_size(x_23);
x_927 = l_Array_toSubarray___rarg(x_23, x_27, x_926);
x_928 = l_Array_ofSubarray___rarg(x_927);
x_929 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_929, 0, x_886);
lean_ctor_set(x_929, 1, x_928);
x_930 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_931 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_929, x_930, x_6, x_7, x_8, x_9, x_885);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_931, 1);
lean_inc(x_933);
lean_dec(x_931);
x_934 = lean_ctor_get(x_932, 0);
lean_inc(x_934);
x_935 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_934, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_933);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_936 = lean_ctor_get(x_935, 1);
lean_inc(x_936);
lean_dec(x_935);
x_937 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_937, 0, x_932);
lean_ctor_set(x_937, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_938 = l_Lean_Compiler_LCNF_Simp_simp(x_937, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_936);
if (lean_obj_tag(x_938) == 0)
{
lean_object* x_939; lean_object* x_940; 
x_939 = lean_ctor_get(x_938, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_938, 1);
lean_inc(x_940);
lean_dec(x_938);
x_888 = x_939;
x_889 = x_940;
goto block_912;
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
lean_dec(x_884);
lean_dec(x_872);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_941 = lean_ctor_get(x_938, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_938, 1);
lean_inc(x_942);
if (lean_is_exclusive(x_938)) {
 lean_ctor_release(x_938, 0);
 lean_ctor_release(x_938, 1);
 x_943 = x_938;
} else {
 lean_dec_ref(x_938);
 x_943 = lean_box(0);
}
if (lean_is_scalar(x_943)) {
 x_944 = lean_alloc_ctor(1, 2, 0);
} else {
 x_944 = x_943;
}
lean_ctor_set(x_944, 0, x_941);
lean_ctor_set(x_944, 1, x_942);
return x_944;
}
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
lean_dec(x_932);
lean_dec(x_884);
lean_dec(x_872);
lean_dec(x_865);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_945 = lean_ctor_get(x_935, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_935, 1);
lean_inc(x_946);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_947 = x_935;
} else {
 lean_dec_ref(x_935);
 x_947 = lean_box(0);
}
if (lean_is_scalar(x_947)) {
 x_948 = lean_alloc_ctor(1, 2, 0);
} else {
 x_948 = x_947;
}
lean_ctor_set(x_948, 0, x_945);
lean_ctor_set(x_948, 1, x_946);
return x_948;
}
}
else
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; 
lean_dec(x_884);
lean_dec(x_872);
lean_dec(x_865);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_949 = lean_ctor_get(x_931, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_931, 1);
lean_inc(x_950);
if (lean_is_exclusive(x_931)) {
 lean_ctor_release(x_931, 0);
 lean_ctor_release(x_931, 1);
 x_951 = x_931;
} else {
 lean_dec_ref(x_931);
 x_951 = lean_box(0);
}
if (lean_is_scalar(x_951)) {
 x_952 = lean_alloc_ctor(1, 2, 0);
} else {
 x_952 = x_951;
}
lean_ctor_set(x_952, 0, x_949);
lean_ctor_set(x_952, 1, x_950);
return x_952;
}
}
block_912:
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_890 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_891 = lean_array_push(x_890, x_884);
x_892 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_893 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_891, x_888, x_892, x_6, x_7, x_8, x_9, x_889);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
lean_dec(x_893);
lean_inc(x_894);
x_896 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_896, 0, x_894);
lean_closure_set(x_896, 1, x_890);
x_897 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_872, x_896, x_6, x_7, x_8, x_9, x_895);
if (lean_obj_tag(x_897) == 0)
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; 
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_900 = x_897;
} else {
 lean_dec_ref(x_897);
 x_900 = lean_box(0);
}
x_901 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_901, 0, x_894);
lean_ctor_set(x_901, 1, x_898);
if (lean_is_scalar(x_22)) {
 x_902 = lean_alloc_ctor(1, 1, 0);
} else {
 x_902 = x_22;
}
lean_ctor_set(x_902, 0, x_901);
if (lean_is_scalar(x_900)) {
 x_903 = lean_alloc_ctor(0, 2, 0);
} else {
 x_903 = x_900;
}
lean_ctor_set(x_903, 0, x_902);
lean_ctor_set(x_903, 1, x_899);
return x_903;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
lean_dec(x_894);
lean_dec(x_22);
x_904 = lean_ctor_get(x_897, 0);
lean_inc(x_904);
x_905 = lean_ctor_get(x_897, 1);
lean_inc(x_905);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_906 = x_897;
} else {
 lean_dec_ref(x_897);
 x_906 = lean_box(0);
}
if (lean_is_scalar(x_906)) {
 x_907 = lean_alloc_ctor(1, 2, 0);
} else {
 x_907 = x_906;
}
lean_ctor_set(x_907, 0, x_904);
lean_ctor_set(x_907, 1, x_905);
return x_907;
}
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
lean_dec(x_872);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_908 = lean_ctor_get(x_893, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_893, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_910 = x_893;
} else {
 lean_dec_ref(x_893);
 x_910 = lean_box(0);
}
if (lean_is_scalar(x_910)) {
 x_911 = lean_alloc_ctor(1, 2, 0);
} else {
 x_911 = x_910;
}
lean_ctor_set(x_911, 0, x_908);
lean_ctor_set(x_911, 1, x_909);
return x_911;
}
}
}
else
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; 
lean_dec(x_879);
x_953 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_954 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_955 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_953, x_872, x_954, x_6, x_7, x_8, x_9, x_880);
if (lean_obj_tag(x_955) == 0)
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_956 = lean_ctor_get(x_955, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_955, 1);
lean_inc(x_957);
lean_dec(x_955);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_958 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_956, x_6, x_7, x_8, x_9, x_957);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; uint8_t x_962; lean_object* x_963; lean_object* x_964; 
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
lean_dec(x_958);
x_961 = lean_ctor_get(x_959, 0);
lean_inc(x_961);
x_962 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_962 == 0)
{
lean_object* x_975; 
lean_dec(x_27);
lean_dec(x_23);
x_975 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_961, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_960);
if (lean_obj_tag(x_975) == 0)
{
lean_object* x_976; lean_object* x_977; 
x_976 = lean_ctor_get(x_975, 1);
lean_inc(x_976);
lean_dec(x_975);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_865);
x_977 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_976);
if (lean_obj_tag(x_977) == 0)
{
lean_object* x_978; lean_object* x_979; 
x_978 = lean_ctor_get(x_977, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_977, 1);
lean_inc(x_979);
lean_dec(x_977);
x_963 = x_978;
x_964 = x_979;
goto block_974;
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
lean_dec(x_959);
lean_dec(x_865);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_980 = lean_ctor_get(x_977, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_977, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_977)) {
 lean_ctor_release(x_977, 0);
 lean_ctor_release(x_977, 1);
 x_982 = x_977;
} else {
 lean_dec_ref(x_977);
 x_982 = lean_box(0);
}
if (lean_is_scalar(x_982)) {
 x_983 = lean_alloc_ctor(1, 2, 0);
} else {
 x_983 = x_982;
}
lean_ctor_set(x_983, 0, x_980);
lean_ctor_set(x_983, 1, x_981);
return x_983;
}
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
lean_dec(x_959);
lean_dec(x_865);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_984 = lean_ctor_get(x_975, 0);
lean_inc(x_984);
x_985 = lean_ctor_get(x_975, 1);
lean_inc(x_985);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 lean_ctor_release(x_975, 1);
 x_986 = x_975;
} else {
 lean_dec_ref(x_975);
 x_986 = lean_box(0);
}
if (lean_is_scalar(x_986)) {
 x_987 = lean_alloc_ctor(1, 2, 0);
} else {
 x_987 = x_986;
}
lean_ctor_set(x_987, 0, x_984);
lean_ctor_set(x_987, 1, x_985);
return x_987;
}
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_988 = lean_array_get_size(x_23);
x_989 = l_Array_toSubarray___rarg(x_23, x_27, x_988);
x_990 = l_Array_ofSubarray___rarg(x_989);
x_991 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_991, 0, x_961);
lean_ctor_set(x_991, 1, x_990);
x_992 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_993 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_991, x_992, x_6, x_7, x_8, x_9, x_960);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; 
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_993, 1);
lean_inc(x_995);
lean_dec(x_993);
x_996 = lean_ctor_get(x_994, 0);
lean_inc(x_996);
x_997 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_996, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_995);
if (lean_obj_tag(x_997) == 0)
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_998 = lean_ctor_get(x_997, 1);
lean_inc(x_998);
lean_dec(x_997);
x_999 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_999, 0, x_994);
lean_ctor_set(x_999, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_865);
x_1000 = l_Lean_Compiler_LCNF_Simp_simp(x_999, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_998);
if (lean_obj_tag(x_1000) == 0)
{
lean_object* x_1001; lean_object* x_1002; 
x_1001 = lean_ctor_get(x_1000, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_1000, 1);
lean_inc(x_1002);
lean_dec(x_1000);
x_963 = x_1001;
x_964 = x_1002;
goto block_974;
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_959);
lean_dec(x_865);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1003 = lean_ctor_get(x_1000, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_1000, 1);
lean_inc(x_1004);
if (lean_is_exclusive(x_1000)) {
 lean_ctor_release(x_1000, 0);
 lean_ctor_release(x_1000, 1);
 x_1005 = x_1000;
} else {
 lean_dec_ref(x_1000);
 x_1005 = lean_box(0);
}
if (lean_is_scalar(x_1005)) {
 x_1006 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1006 = x_1005;
}
lean_ctor_set(x_1006, 0, x_1003);
lean_ctor_set(x_1006, 1, x_1004);
return x_1006;
}
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_994);
lean_dec(x_959);
lean_dec(x_865);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1007 = lean_ctor_get(x_997, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_997, 1);
lean_inc(x_1008);
if (lean_is_exclusive(x_997)) {
 lean_ctor_release(x_997, 0);
 lean_ctor_release(x_997, 1);
 x_1009 = x_997;
} else {
 lean_dec_ref(x_997);
 x_1009 = lean_box(0);
}
if (lean_is_scalar(x_1009)) {
 x_1010 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1010 = x_1009;
}
lean_ctor_set(x_1010, 0, x_1007);
lean_ctor_set(x_1010, 1, x_1008);
return x_1010;
}
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
lean_dec(x_959);
lean_dec(x_865);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1011 = lean_ctor_get(x_993, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_993, 1);
lean_inc(x_1012);
if (lean_is_exclusive(x_993)) {
 lean_ctor_release(x_993, 0);
 lean_ctor_release(x_993, 1);
 x_1013 = x_993;
} else {
 lean_dec_ref(x_993);
 x_1013 = lean_box(0);
}
if (lean_is_scalar(x_1013)) {
 x_1014 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1014 = x_1013;
}
lean_ctor_set(x_1014, 0, x_1011);
lean_ctor_set(x_1014, 1, x_1012);
return x_1014;
}
}
block_974:
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_965 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_965, 0, x_959);
x_966 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_967 = lean_array_push(x_966, x_965);
x_968 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_967, x_963, x_865, x_4, x_5, x_6, x_7, x_8, x_9, x_964);
lean_dec(x_967);
x_969 = lean_ctor_get(x_968, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_968, 1);
lean_inc(x_970);
if (lean_is_exclusive(x_968)) {
 lean_ctor_release(x_968, 0);
 lean_ctor_release(x_968, 1);
 x_971 = x_968;
} else {
 lean_dec_ref(x_968);
 x_971 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_972 = lean_alloc_ctor(1, 1, 0);
} else {
 x_972 = x_22;
}
lean_ctor_set(x_972, 0, x_969);
if (lean_is_scalar(x_971)) {
 x_973 = lean_alloc_ctor(0, 2, 0);
} else {
 x_973 = x_971;
}
lean_ctor_set(x_973, 0, x_972);
lean_ctor_set(x_973, 1, x_970);
return x_973;
}
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
lean_dec(x_865);
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
x_1015 = lean_ctor_get(x_958, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_958, 1);
lean_inc(x_1016);
if (lean_is_exclusive(x_958)) {
 lean_ctor_release(x_958, 0);
 lean_ctor_release(x_958, 1);
 x_1017 = x_958;
} else {
 lean_dec_ref(x_958);
 x_1017 = lean_box(0);
}
if (lean_is_scalar(x_1017)) {
 x_1018 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1018 = x_1017;
}
lean_ctor_set(x_1018, 0, x_1015);
lean_ctor_set(x_1018, 1, x_1016);
return x_1018;
}
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
lean_dec(x_865);
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
x_1019 = lean_ctor_get(x_955, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_955, 1);
lean_inc(x_1020);
if (lean_is_exclusive(x_955)) {
 lean_ctor_release(x_955, 0);
 lean_ctor_release(x_955, 1);
 x_1021 = x_955;
} else {
 lean_dec_ref(x_955);
 x_1021 = lean_box(0);
}
if (lean_is_scalar(x_1021)) {
 x_1022 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1022 = x_1021;
}
lean_ctor_set(x_1022, 0, x_1019);
lean_ctor_set(x_1022, 1, x_1020);
return x_1022;
}
}
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
lean_dec(x_33);
lean_dec(x_21);
x_1023 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_873);
x_1024 = lean_ctor_get(x_1023, 1);
lean_inc(x_1024);
lean_dec(x_1023);
x_1025 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_1025, 0, x_865);
lean_closure_set(x_1025, 1, x_4);
lean_closure_set(x_1025, 2, x_5);
lean_closure_set(x_1025, 3, x_27);
lean_closure_set(x_1025, 4, x_24);
lean_closure_set(x_1025, 5, x_26);
lean_closure_set(x_1025, 6, x_2);
lean_closure_set(x_1025, 7, x_23);
x_1026 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_872, x_1025, x_6, x_7, x_8, x_9, x_1024);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1027 = lean_ctor_get(x_1026, 0);
lean_inc(x_1027);
x_1028 = lean_ctor_get(x_1026, 1);
lean_inc(x_1028);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 lean_ctor_release(x_1026, 1);
 x_1029 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1029 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1030 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1030 = x_22;
}
lean_ctor_set(x_1030, 0, x_1027);
if (lean_is_scalar(x_1029)) {
 x_1031 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1031 = x_1029;
}
lean_ctor_set(x_1031, 0, x_1030);
lean_ctor_set(x_1031, 1, x_1028);
return x_1031;
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
lean_dec(x_22);
x_1032 = lean_ctor_get(x_1026, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1026, 1);
lean_inc(x_1033);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 lean_ctor_release(x_1026, 1);
 x_1034 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1034 = lean_box(0);
}
if (lean_is_scalar(x_1034)) {
 x_1035 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1035 = x_1034;
}
lean_ctor_set(x_1035, 0, x_1032);
lean_ctor_set(x_1035, 1, x_1033);
return x_1035;
}
}
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
lean_dec(x_865);
lean_dec(x_33);
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
x_1036 = lean_ctor_get(x_871, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_871, 1);
lean_inc(x_1037);
if (lean_is_exclusive(x_871)) {
 lean_ctor_release(x_871, 0);
 lean_ctor_release(x_871, 1);
 x_1038 = x_871;
} else {
 lean_dec_ref(x_871);
 x_1038 = lean_box(0);
}
if (lean_is_scalar(x_1038)) {
 x_1039 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1039 = x_1038;
}
lean_ctor_set(x_1039, 0, x_1036);
lean_ctor_set(x_1039, 1, x_1037);
return x_1039;
}
}
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_865);
lean_dec(x_33);
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
x_1057 = lean_ctor_get(x_867, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_867, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_867)) {
 lean_ctor_release(x_867, 0);
 lean_ctor_release(x_867, 1);
 x_1059 = x_867;
} else {
 lean_dec_ref(x_867);
 x_1059 = lean_box(0);
}
if (lean_is_scalar(x_1059)) {
 x_1060 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1060 = x_1059;
}
lean_ctor_set(x_1060, 0, x_1057);
lean_ctor_set(x_1060, 1, x_1058);
return x_1060;
}
}
}
else
{
uint8_t x_1061; 
lean_dec(x_646);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
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
x_1061 = !lean_is_exclusive(x_647);
if (x_1061 == 0)
{
return x_647;
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
x_1062 = lean_ctor_get(x_647, 0);
x_1063 = lean_ctor_get(x_647, 1);
lean_inc(x_1063);
lean_inc(x_1062);
lean_dec(x_647);
x_1064 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1064, 0, x_1062);
lean_ctor_set(x_1064, 1, x_1063);
return x_1064;
}
}
}
default: 
{
lean_object* x_1065; uint8_t x_1066; lean_object* x_1067; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1065 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1065 = lean_box(0);
}
x_1066 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_1067 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_1066, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_1067) == 0)
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; uint8_t x_1248; 
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1067, 1);
lean_inc(x_1069);
lean_dec(x_1067);
x_1248 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1248 == 0)
{
lean_object* x_1249; 
x_1249 = lean_box(0);
x_1070 = x_1249;
goto block_1247;
}
else
{
uint8_t x_1250; 
x_1250 = lean_nat_dec_eq(x_24, x_27);
if (x_1250 == 0)
{
lean_object* x_1251; 
x_1251 = lean_box(0);
x_1070 = x_1251;
goto block_1247;
}
else
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; 
lean_dec(x_1065);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_1252 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1069);
x_1253 = lean_ctor_get(x_1252, 1);
lean_inc(x_1253);
lean_dec(x_1252);
x_1254 = l_Lean_Compiler_LCNF_Simp_simp(x_1068, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1253);
if (lean_obj_tag(x_1254) == 0)
{
uint8_t x_1255; 
x_1255 = !lean_is_exclusive(x_1254);
if (x_1255 == 0)
{
lean_object* x_1256; lean_object* x_1257; 
x_1256 = lean_ctor_get(x_1254, 0);
x_1257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1257, 0, x_1256);
lean_ctor_set(x_1254, 0, x_1257);
return x_1254;
}
else
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1258 = lean_ctor_get(x_1254, 0);
x_1259 = lean_ctor_get(x_1254, 1);
lean_inc(x_1259);
lean_inc(x_1258);
lean_dec(x_1254);
x_1260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1260, 0, x_1258);
x_1261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1261, 0, x_1260);
lean_ctor_set(x_1261, 1, x_1259);
return x_1261;
}
}
else
{
uint8_t x_1262; 
x_1262 = !lean_is_exclusive(x_1254);
if (x_1262 == 0)
{
return x_1254;
}
else
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; 
x_1263 = lean_ctor_get(x_1254, 0);
x_1264 = lean_ctor_get(x_1254, 1);
lean_inc(x_1264);
lean_inc(x_1263);
lean_dec(x_1254);
x_1265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1265, 0, x_1263);
lean_ctor_set(x_1265, 1, x_1264);
return x_1265;
}
}
}
}
block_1247:
{
lean_object* x_1071; 
lean_dec(x_1070);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1071 = l_Lean_Compiler_LCNF_Simp_simp(x_1068, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1069);
if (lean_obj_tag(x_1071) == 0)
{
lean_object* x_1072; lean_object* x_1073; uint8_t x_1074; 
x_1072 = lean_ctor_get(x_1071, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1071, 1);
lean_inc(x_1073);
lean_dec(x_1071);
lean_inc(x_1072);
x_1074 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1072);
if (x_1074 == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; uint8_t x_1082; 
x_1075 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1073);
x_1076 = lean_ctor_get(x_1075, 1);
lean_inc(x_1076);
lean_dec(x_1075);
x_1077 = lean_ctor_get(x_21, 2);
lean_inc(x_1077);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1078 = l_Lean_Compiler_LCNF_inferAppType(x_1077, x_33, x_6, x_7, x_8, x_9, x_1076);
x_1079 = lean_ctor_get(x_1078, 0);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_1078, 1);
lean_inc(x_1080);
lean_dec(x_1078);
lean_inc(x_1079);
x_1081 = l_Lean_Expr_headBeta(x_1079);
x_1082 = l_Lean_Expr_isForall(x_1081);
lean_dec(x_1081);
if (x_1082 == 0)
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; uint8_t x_1087; lean_object* x_1088; lean_object* x_1089; 
x_1083 = l_Lean_Compiler_LCNF_mkAuxParam(x_1079, x_1066, x_6, x_7, x_8, x_9, x_1080);
x_1084 = lean_ctor_get(x_1083, 0);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1083, 1);
lean_inc(x_1085);
lean_dec(x_1083);
x_1086 = lean_ctor_get(x_1084, 0);
lean_inc(x_1086);
x_1087 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1087 == 0)
{
lean_object* x_1116; 
lean_dec(x_1065);
lean_dec(x_27);
lean_dec(x_23);
x_1116 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1086, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1085);
if (lean_obj_tag(x_1116) == 0)
{
lean_object* x_1117; lean_object* x_1118; 
x_1117 = lean_ctor_get(x_1116, 1);
lean_inc(x_1117);
lean_dec(x_1116);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1118 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1117);
if (lean_obj_tag(x_1118) == 0)
{
lean_object* x_1119; lean_object* x_1120; 
x_1119 = lean_ctor_get(x_1118, 0);
lean_inc(x_1119);
x_1120 = lean_ctor_get(x_1118, 1);
lean_inc(x_1120);
lean_dec(x_1118);
x_1088 = x_1119;
x_1089 = x_1120;
goto block_1115;
}
else
{
uint8_t x_1121; 
lean_dec(x_1084);
lean_dec(x_1072);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1121 = !lean_is_exclusive(x_1118);
if (x_1121 == 0)
{
return x_1118;
}
else
{
lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
x_1122 = lean_ctor_get(x_1118, 0);
x_1123 = lean_ctor_get(x_1118, 1);
lean_inc(x_1123);
lean_inc(x_1122);
lean_dec(x_1118);
x_1124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1124, 0, x_1122);
lean_ctor_set(x_1124, 1, x_1123);
return x_1124;
}
}
}
else
{
uint8_t x_1125; 
lean_dec(x_1084);
lean_dec(x_1072);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1125 = !lean_is_exclusive(x_1116);
if (x_1125 == 0)
{
return x_1116;
}
else
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1126 = lean_ctor_get(x_1116, 0);
x_1127 = lean_ctor_get(x_1116, 1);
lean_inc(x_1127);
lean_inc(x_1126);
lean_dec(x_1116);
x_1128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1128, 0, x_1126);
lean_ctor_set(x_1128, 1, x_1127);
return x_1128;
}
}
}
else
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; 
x_1129 = lean_array_get_size(x_23);
x_1130 = l_Array_toSubarray___rarg(x_23, x_27, x_1129);
x_1131 = l_Array_ofSubarray___rarg(x_1130);
if (lean_is_scalar(x_1065)) {
 x_1132 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1132 = x_1065;
}
lean_ctor_set(x_1132, 0, x_1086);
lean_ctor_set(x_1132, 1, x_1131);
x_1133 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1134 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1132, x_1133, x_6, x_7, x_8, x_9, x_1085);
if (lean_obj_tag(x_1134) == 0)
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; 
x_1135 = lean_ctor_get(x_1134, 0);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_1134, 1);
lean_inc(x_1136);
lean_dec(x_1134);
x_1137 = lean_ctor_get(x_1135, 0);
lean_inc(x_1137);
x_1138 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1137, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1136);
if (lean_obj_tag(x_1138) == 0)
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; 
x_1139 = lean_ctor_get(x_1138, 1);
lean_inc(x_1139);
lean_dec(x_1138);
x_1140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1140, 0, x_1135);
lean_ctor_set(x_1140, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1141 = l_Lean_Compiler_LCNF_Simp_simp(x_1140, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1139);
if (lean_obj_tag(x_1141) == 0)
{
lean_object* x_1142; lean_object* x_1143; 
x_1142 = lean_ctor_get(x_1141, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1141, 1);
lean_inc(x_1143);
lean_dec(x_1141);
x_1088 = x_1142;
x_1089 = x_1143;
goto block_1115;
}
else
{
uint8_t x_1144; 
lean_dec(x_1084);
lean_dec(x_1072);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1144 = !lean_is_exclusive(x_1141);
if (x_1144 == 0)
{
return x_1141;
}
else
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1145 = lean_ctor_get(x_1141, 0);
x_1146 = lean_ctor_get(x_1141, 1);
lean_inc(x_1146);
lean_inc(x_1145);
lean_dec(x_1141);
x_1147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1147, 0, x_1145);
lean_ctor_set(x_1147, 1, x_1146);
return x_1147;
}
}
}
else
{
uint8_t x_1148; 
lean_dec(x_1135);
lean_dec(x_1084);
lean_dec(x_1072);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1148 = !lean_is_exclusive(x_1138);
if (x_1148 == 0)
{
return x_1138;
}
else
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
x_1149 = lean_ctor_get(x_1138, 0);
x_1150 = lean_ctor_get(x_1138, 1);
lean_inc(x_1150);
lean_inc(x_1149);
lean_dec(x_1138);
x_1151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1151, 0, x_1149);
lean_ctor_set(x_1151, 1, x_1150);
return x_1151;
}
}
}
else
{
uint8_t x_1152; 
lean_dec(x_1084);
lean_dec(x_1072);
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
x_1152 = !lean_is_exclusive(x_1134);
if (x_1152 == 0)
{
return x_1134;
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1153 = lean_ctor_get(x_1134, 0);
x_1154 = lean_ctor_get(x_1134, 1);
lean_inc(x_1154);
lean_inc(x_1153);
lean_dec(x_1134);
x_1155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1155, 0, x_1153);
lean_ctor_set(x_1155, 1, x_1154);
return x_1155;
}
}
}
block_1115:
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
x_1090 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1091 = lean_array_push(x_1090, x_1084);
x_1092 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1093 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1091, x_1088, x_1092, x_6, x_7, x_8, x_9, x_1089);
if (lean_obj_tag(x_1093) == 0)
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
x_1094 = lean_ctor_get(x_1093, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1093, 1);
lean_inc(x_1095);
lean_dec(x_1093);
lean_inc(x_1094);
x_1096 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1096, 0, x_1094);
lean_closure_set(x_1096, 1, x_1090);
x_1097 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1072, x_1096, x_6, x_7, x_8, x_9, x_1095);
if (lean_obj_tag(x_1097) == 0)
{
uint8_t x_1098; 
x_1098 = !lean_is_exclusive(x_1097);
if (x_1098 == 0)
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
x_1099 = lean_ctor_get(x_1097, 0);
x_1100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1100, 0, x_1094);
lean_ctor_set(x_1100, 1, x_1099);
if (lean_is_scalar(x_22)) {
 x_1101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1101 = x_22;
}
lean_ctor_set(x_1101, 0, x_1100);
lean_ctor_set(x_1097, 0, x_1101);
return x_1097;
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
x_1102 = lean_ctor_get(x_1097, 0);
x_1103 = lean_ctor_get(x_1097, 1);
lean_inc(x_1103);
lean_inc(x_1102);
lean_dec(x_1097);
x_1104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1104, 0, x_1094);
lean_ctor_set(x_1104, 1, x_1102);
if (lean_is_scalar(x_22)) {
 x_1105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1105 = x_22;
}
lean_ctor_set(x_1105, 0, x_1104);
x_1106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1106, 0, x_1105);
lean_ctor_set(x_1106, 1, x_1103);
return x_1106;
}
}
else
{
uint8_t x_1107; 
lean_dec(x_1094);
lean_dec(x_22);
x_1107 = !lean_is_exclusive(x_1097);
if (x_1107 == 0)
{
return x_1097;
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
x_1108 = lean_ctor_get(x_1097, 0);
x_1109 = lean_ctor_get(x_1097, 1);
lean_inc(x_1109);
lean_inc(x_1108);
lean_dec(x_1097);
x_1110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1110, 0, x_1108);
lean_ctor_set(x_1110, 1, x_1109);
return x_1110;
}
}
}
else
{
uint8_t x_1111; 
lean_dec(x_1072);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1111 = !lean_is_exclusive(x_1093);
if (x_1111 == 0)
{
return x_1093;
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
x_1112 = lean_ctor_get(x_1093, 0);
x_1113 = lean_ctor_get(x_1093, 1);
lean_inc(x_1113);
lean_inc(x_1112);
lean_dec(x_1093);
x_1114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1114, 0, x_1112);
lean_ctor_set(x_1114, 1, x_1113);
return x_1114;
}
}
}
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
lean_dec(x_1079);
x_1156 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1157 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1158 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1156, x_1072, x_1157, x_6, x_7, x_8, x_9, x_1080);
if (lean_obj_tag(x_1158) == 0)
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
x_1159 = lean_ctor_get(x_1158, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1158, 1);
lean_inc(x_1160);
lean_dec(x_1158);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1161 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1159, x_6, x_7, x_8, x_9, x_1160);
if (lean_obj_tag(x_1161) == 0)
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; uint8_t x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1162 = lean_ctor_get(x_1161, 0);
lean_inc(x_1162);
x_1163 = lean_ctor_get(x_1161, 1);
lean_inc(x_1163);
lean_dec(x_1161);
x_1164 = lean_ctor_get(x_1162, 0);
lean_inc(x_1164);
x_1165 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1165 == 0)
{
lean_object* x_1180; 
lean_dec(x_1065);
lean_dec(x_27);
lean_dec(x_23);
x_1180 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1164, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1163);
if (lean_obj_tag(x_1180) == 0)
{
lean_object* x_1181; lean_object* x_1182; 
x_1181 = lean_ctor_get(x_1180, 1);
lean_inc(x_1181);
lean_dec(x_1180);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1182 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1181);
if (lean_obj_tag(x_1182) == 0)
{
lean_object* x_1183; lean_object* x_1184; 
x_1183 = lean_ctor_get(x_1182, 0);
lean_inc(x_1183);
x_1184 = lean_ctor_get(x_1182, 1);
lean_inc(x_1184);
lean_dec(x_1182);
x_1166 = x_1183;
x_1167 = x_1184;
goto block_1179;
}
else
{
uint8_t x_1185; 
lean_dec(x_1162);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_1162);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1189 = !lean_is_exclusive(x_1180);
if (x_1189 == 0)
{
return x_1180;
}
else
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1190 = lean_ctor_get(x_1180, 0);
x_1191 = lean_ctor_get(x_1180, 1);
lean_inc(x_1191);
lean_inc(x_1190);
lean_dec(x_1180);
x_1192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1192, 0, x_1190);
lean_ctor_set(x_1192, 1, x_1191);
return x_1192;
}
}
}
else
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
x_1193 = lean_array_get_size(x_23);
x_1194 = l_Array_toSubarray___rarg(x_23, x_27, x_1193);
x_1195 = l_Array_ofSubarray___rarg(x_1194);
if (lean_is_scalar(x_1065)) {
 x_1196 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1196 = x_1065;
}
lean_ctor_set(x_1196, 0, x_1164);
lean_ctor_set(x_1196, 1, x_1195);
x_1197 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1198 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1196, x_1197, x_6, x_7, x_8, x_9, x_1163);
if (lean_obj_tag(x_1198) == 0)
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1198, 1);
lean_inc(x_1200);
lean_dec(x_1198);
x_1201 = lean_ctor_get(x_1199, 0);
lean_inc(x_1201);
x_1202 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1201, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1200);
if (lean_obj_tag(x_1202) == 0)
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
x_1203 = lean_ctor_get(x_1202, 1);
lean_inc(x_1203);
lean_dec(x_1202);
x_1204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1204, 0, x_1199);
lean_ctor_set(x_1204, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1205 = l_Lean_Compiler_LCNF_Simp_simp(x_1204, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1203);
if (lean_obj_tag(x_1205) == 0)
{
lean_object* x_1206; lean_object* x_1207; 
x_1206 = lean_ctor_get(x_1205, 0);
lean_inc(x_1206);
x_1207 = lean_ctor_get(x_1205, 1);
lean_inc(x_1207);
lean_dec(x_1205);
x_1166 = x_1206;
x_1167 = x_1207;
goto block_1179;
}
else
{
uint8_t x_1208; 
lean_dec(x_1162);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1208 = !lean_is_exclusive(x_1205);
if (x_1208 == 0)
{
return x_1205;
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
x_1209 = lean_ctor_get(x_1205, 0);
x_1210 = lean_ctor_get(x_1205, 1);
lean_inc(x_1210);
lean_inc(x_1209);
lean_dec(x_1205);
x_1211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1211, 0, x_1209);
lean_ctor_set(x_1211, 1, x_1210);
return x_1211;
}
}
}
else
{
uint8_t x_1212; 
lean_dec(x_1199);
lean_dec(x_1162);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1212 = !lean_is_exclusive(x_1202);
if (x_1212 == 0)
{
return x_1202;
}
else
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1213 = lean_ctor_get(x_1202, 0);
x_1214 = lean_ctor_get(x_1202, 1);
lean_inc(x_1214);
lean_inc(x_1213);
lean_dec(x_1202);
x_1215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1215, 0, x_1213);
lean_ctor_set(x_1215, 1, x_1214);
return x_1215;
}
}
}
else
{
uint8_t x_1216; 
lean_dec(x_1162);
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
x_1216 = !lean_is_exclusive(x_1198);
if (x_1216 == 0)
{
return x_1198;
}
else
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; 
x_1217 = lean_ctor_get(x_1198, 0);
x_1218 = lean_ctor_get(x_1198, 1);
lean_inc(x_1218);
lean_inc(x_1217);
lean_dec(x_1198);
x_1219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1219, 0, x_1217);
lean_ctor_set(x_1219, 1, x_1218);
return x_1219;
}
}
}
block_1179:
{
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; uint8_t x_1172; 
x_1168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1168, 0, x_1162);
x_1169 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1170 = lean_array_push(x_1169, x_1168);
x_1171 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1170, x_1166, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1167);
lean_dec(x_1170);
x_1172 = !lean_is_exclusive(x_1171);
if (x_1172 == 0)
{
lean_object* x_1173; lean_object* x_1174; 
x_1173 = lean_ctor_get(x_1171, 0);
if (lean_is_scalar(x_22)) {
 x_1174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1174 = x_22;
}
lean_ctor_set(x_1174, 0, x_1173);
lean_ctor_set(x_1171, 0, x_1174);
return x_1171;
}
else
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1175 = lean_ctor_get(x_1171, 0);
x_1176 = lean_ctor_get(x_1171, 1);
lean_inc(x_1176);
lean_inc(x_1175);
lean_dec(x_1171);
if (lean_is_scalar(x_22)) {
 x_1177 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1177 = x_22;
}
lean_ctor_set(x_1177, 0, x_1175);
x_1178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1178, 0, x_1177);
lean_ctor_set(x_1178, 1, x_1176);
return x_1178;
}
}
}
else
{
uint8_t x_1220; 
lean_dec(x_1065);
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
x_1220 = !lean_is_exclusive(x_1161);
if (x_1220 == 0)
{
return x_1161;
}
else
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; 
x_1221 = lean_ctor_get(x_1161, 0);
x_1222 = lean_ctor_get(x_1161, 1);
lean_inc(x_1222);
lean_inc(x_1221);
lean_dec(x_1161);
x_1223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1223, 0, x_1221);
lean_ctor_set(x_1223, 1, x_1222);
return x_1223;
}
}
}
else
{
uint8_t x_1224; 
lean_dec(x_1065);
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
x_1224 = !lean_is_exclusive(x_1158);
if (x_1224 == 0)
{
return x_1158;
}
else
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; 
x_1225 = lean_ctor_get(x_1158, 0);
x_1226 = lean_ctor_get(x_1158, 1);
lean_inc(x_1226);
lean_inc(x_1225);
lean_dec(x_1158);
x_1227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1227, 0, x_1225);
lean_ctor_set(x_1227, 1, x_1226);
return x_1227;
}
}
}
}
else
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; 
lean_dec(x_1065);
lean_dec(x_33);
lean_dec(x_21);
x_1228 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1073);
x_1229 = lean_ctor_get(x_1228, 1);
lean_inc(x_1229);
lean_dec(x_1228);
x_1230 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_1230, 0, x_3);
lean_closure_set(x_1230, 1, x_4);
lean_closure_set(x_1230, 2, x_5);
lean_closure_set(x_1230, 3, x_27);
lean_closure_set(x_1230, 4, x_24);
lean_closure_set(x_1230, 5, x_26);
lean_closure_set(x_1230, 6, x_2);
lean_closure_set(x_1230, 7, x_23);
x_1231 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1072, x_1230, x_6, x_7, x_8, x_9, x_1229);
if (lean_obj_tag(x_1231) == 0)
{
uint8_t x_1232; 
x_1232 = !lean_is_exclusive(x_1231);
if (x_1232 == 0)
{
lean_object* x_1233; lean_object* x_1234; 
x_1233 = lean_ctor_get(x_1231, 0);
if (lean_is_scalar(x_22)) {
 x_1234 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1234 = x_22;
}
lean_ctor_set(x_1234, 0, x_1233);
lean_ctor_set(x_1231, 0, x_1234);
return x_1231;
}
else
{
lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; 
x_1235 = lean_ctor_get(x_1231, 0);
x_1236 = lean_ctor_get(x_1231, 1);
lean_inc(x_1236);
lean_inc(x_1235);
lean_dec(x_1231);
if (lean_is_scalar(x_22)) {
 x_1237 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1237 = x_22;
}
lean_ctor_set(x_1237, 0, x_1235);
x_1238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1238, 0, x_1237);
lean_ctor_set(x_1238, 1, x_1236);
return x_1238;
}
}
else
{
uint8_t x_1239; 
lean_dec(x_22);
x_1239 = !lean_is_exclusive(x_1231);
if (x_1239 == 0)
{
return x_1231;
}
else
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; 
x_1240 = lean_ctor_get(x_1231, 0);
x_1241 = lean_ctor_get(x_1231, 1);
lean_inc(x_1241);
lean_inc(x_1240);
lean_dec(x_1231);
x_1242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1242, 0, x_1240);
lean_ctor_set(x_1242, 1, x_1241);
return x_1242;
}
}
}
}
else
{
uint8_t x_1243; 
lean_dec(x_1065);
lean_dec(x_33);
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
x_1243 = !lean_is_exclusive(x_1071);
if (x_1243 == 0)
{
return x_1071;
}
else
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; 
x_1244 = lean_ctor_get(x_1071, 0);
x_1245 = lean_ctor_get(x_1071, 1);
lean_inc(x_1245);
lean_inc(x_1244);
lean_dec(x_1071);
x_1246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1246, 0, x_1244);
lean_ctor_set(x_1246, 1, x_1245);
return x_1246;
}
}
}
}
else
{
uint8_t x_1266; 
lean_dec(x_1065);
lean_dec(x_33);
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
x_1266 = !lean_is_exclusive(x_1067);
if (x_1266 == 0)
{
return x_1067;
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1067, 0);
x_1268 = lean_ctor_get(x_1067, 1);
lean_inc(x_1268);
lean_inc(x_1267);
lean_dec(x_1067);
x_1269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1269, 0, x_1267);
lean_ctor_set(x_1269, 1, x_1268);
return x_1269;
}
}
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_11) == 3)
{
lean_object* x_1270; lean_object* x_1271; 
x_1270 = lean_ctor_get(x_11, 0);
lean_inc(x_1270);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1270);
x_1271 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_1270, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1271) == 0)
{
lean_object* x_1272; lean_object* x_1273; uint8_t x_1274; 
x_1272 = lean_ctor_get(x_1271, 0);
lean_inc(x_1272);
x_1273 = lean_ctor_get(x_1271, 1);
lean_inc(x_1273);
lean_dec(x_1271);
x_1274 = !lean_is_exclusive(x_3);
if (x_1274 == 0)
{
lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; 
x_1275 = lean_ctor_get(x_3, 2);
x_1276 = lean_ctor_get(x_3, 3);
lean_inc(x_1270);
x_1277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1277, 0, x_1270);
lean_ctor_set(x_1277, 1, x_1275);
x_1278 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_1276, x_1270, x_1272);
lean_ctor_set(x_3, 3, x_1278);
lean_ctor_set(x_3, 2, x_1277);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1279 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1273);
if (lean_obj_tag(x_1279) == 0)
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
x_1280 = lean_ctor_get(x_1279, 0);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_1279, 1);
lean_inc(x_1281);
lean_dec(x_1279);
x_1282 = lean_ctor_get(x_1280, 0);
lean_inc(x_1282);
x_1283 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1282, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1281);
if (lean_obj_tag(x_1283) == 0)
{
lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
x_1284 = lean_ctor_get(x_1283, 1);
lean_inc(x_1284);
lean_dec(x_1283);
x_1285 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1284);
x_1286 = lean_ctor_get(x_1285, 1);
lean_inc(x_1286);
lean_dec(x_1285);
x_1287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1287, 0, x_1280);
lean_ctor_set(x_1287, 1, x_2);
x_1288 = l_Lean_Compiler_LCNF_Simp_simp(x_1287, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1286);
if (lean_obj_tag(x_1288) == 0)
{
uint8_t x_1289; 
x_1289 = !lean_is_exclusive(x_1288);
if (x_1289 == 0)
{
lean_object* x_1290; lean_object* x_1291; 
x_1290 = lean_ctor_get(x_1288, 0);
if (lean_is_scalar(x_22)) {
 x_1291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1291 = x_22;
}
lean_ctor_set(x_1291, 0, x_1290);
lean_ctor_set(x_1288, 0, x_1291);
return x_1288;
}
else
{
lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; 
x_1292 = lean_ctor_get(x_1288, 0);
x_1293 = lean_ctor_get(x_1288, 1);
lean_inc(x_1293);
lean_inc(x_1292);
lean_dec(x_1288);
if (lean_is_scalar(x_22)) {
 x_1294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1294 = x_22;
}
lean_ctor_set(x_1294, 0, x_1292);
x_1295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1295, 0, x_1294);
lean_ctor_set(x_1295, 1, x_1293);
return x_1295;
}
}
else
{
uint8_t x_1296; 
lean_dec(x_22);
x_1296 = !lean_is_exclusive(x_1288);
if (x_1296 == 0)
{
return x_1288;
}
else
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; 
x_1297 = lean_ctor_get(x_1288, 0);
x_1298 = lean_ctor_get(x_1288, 1);
lean_inc(x_1298);
lean_inc(x_1297);
lean_dec(x_1288);
x_1299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1299, 0, x_1297);
lean_ctor_set(x_1299, 1, x_1298);
return x_1299;
}
}
}
else
{
uint8_t x_1300; 
lean_dec(x_1280);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1300 = !lean_is_exclusive(x_1283);
if (x_1300 == 0)
{
return x_1283;
}
else
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1301 = lean_ctor_get(x_1283, 0);
x_1302 = lean_ctor_get(x_1283, 1);
lean_inc(x_1302);
lean_inc(x_1301);
lean_dec(x_1283);
x_1303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1303, 0, x_1301);
lean_ctor_set(x_1303, 1, x_1302);
return x_1303;
}
}
}
else
{
uint8_t x_1304; 
lean_dec(x_3);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1304 = !lean_is_exclusive(x_1279);
if (x_1304 == 0)
{
return x_1279;
}
else
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; 
x_1305 = lean_ctor_get(x_1279, 0);
x_1306 = lean_ctor_get(x_1279, 1);
lean_inc(x_1306);
lean_inc(x_1305);
lean_dec(x_1279);
x_1307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1307, 0, x_1305);
lean_ctor_set(x_1307, 1, x_1306);
return x_1307;
}
}
}
else
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
x_1308 = lean_ctor_get(x_3, 0);
x_1309 = lean_ctor_get(x_3, 1);
x_1310 = lean_ctor_get(x_3, 2);
x_1311 = lean_ctor_get(x_3, 3);
lean_inc(x_1311);
lean_inc(x_1310);
lean_inc(x_1309);
lean_inc(x_1308);
lean_dec(x_3);
lean_inc(x_1270);
x_1312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1312, 0, x_1270);
lean_ctor_set(x_1312, 1, x_1310);
x_1313 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_1311, x_1270, x_1272);
x_1314 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1314, 0, x_1308);
lean_ctor_set(x_1314, 1, x_1309);
lean_ctor_set(x_1314, 2, x_1312);
lean_ctor_set(x_1314, 3, x_1313);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1315 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_1314, x_4, x_5, x_6, x_7, x_8, x_9, x_1273);
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; 
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
x_1317 = lean_ctor_get(x_1315, 1);
lean_inc(x_1317);
lean_dec(x_1315);
x_1318 = lean_ctor_get(x_1316, 0);
lean_inc(x_1318);
x_1319 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1318, x_1314, x_4, x_5, x_6, x_7, x_8, x_9, x_1317);
if (lean_obj_tag(x_1319) == 0)
{
lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; 
x_1320 = lean_ctor_get(x_1319, 1);
lean_inc(x_1320);
lean_dec(x_1319);
x_1321 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1320);
x_1322 = lean_ctor_get(x_1321, 1);
lean_inc(x_1322);
lean_dec(x_1321);
x_1323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1323, 0, x_1316);
lean_ctor_set(x_1323, 1, x_2);
x_1324 = l_Lean_Compiler_LCNF_Simp_simp(x_1323, x_1314, x_4, x_5, x_6, x_7, x_8, x_9, x_1322);
if (lean_obj_tag(x_1324) == 0)
{
lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
x_1325 = lean_ctor_get(x_1324, 0);
lean_inc(x_1325);
x_1326 = lean_ctor_get(x_1324, 1);
lean_inc(x_1326);
if (lean_is_exclusive(x_1324)) {
 lean_ctor_release(x_1324, 0);
 lean_ctor_release(x_1324, 1);
 x_1327 = x_1324;
} else {
 lean_dec_ref(x_1324);
 x_1327 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1328 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1328 = x_22;
}
lean_ctor_set(x_1328, 0, x_1325);
if (lean_is_scalar(x_1327)) {
 x_1329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1329 = x_1327;
}
lean_ctor_set(x_1329, 0, x_1328);
lean_ctor_set(x_1329, 1, x_1326);
return x_1329;
}
else
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; 
lean_dec(x_22);
x_1330 = lean_ctor_get(x_1324, 0);
lean_inc(x_1330);
x_1331 = lean_ctor_get(x_1324, 1);
lean_inc(x_1331);
if (lean_is_exclusive(x_1324)) {
 lean_ctor_release(x_1324, 0);
 lean_ctor_release(x_1324, 1);
 x_1332 = x_1324;
} else {
 lean_dec_ref(x_1324);
 x_1332 = lean_box(0);
}
if (lean_is_scalar(x_1332)) {
 x_1333 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1333 = x_1332;
}
lean_ctor_set(x_1333, 0, x_1330);
lean_ctor_set(x_1333, 1, x_1331);
return x_1333;
}
}
else
{
lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; 
lean_dec(x_1316);
lean_dec(x_1314);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1334 = lean_ctor_get(x_1319, 0);
lean_inc(x_1334);
x_1335 = lean_ctor_get(x_1319, 1);
lean_inc(x_1335);
if (lean_is_exclusive(x_1319)) {
 lean_ctor_release(x_1319, 0);
 lean_ctor_release(x_1319, 1);
 x_1336 = x_1319;
} else {
 lean_dec_ref(x_1319);
 x_1336 = lean_box(0);
}
if (lean_is_scalar(x_1336)) {
 x_1337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1337 = x_1336;
}
lean_ctor_set(x_1337, 0, x_1334);
lean_ctor_set(x_1337, 1, x_1335);
return x_1337;
}
}
else
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
lean_dec(x_1314);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1338 = lean_ctor_get(x_1315, 0);
lean_inc(x_1338);
x_1339 = lean_ctor_get(x_1315, 1);
lean_inc(x_1339);
if (lean_is_exclusive(x_1315)) {
 lean_ctor_release(x_1315, 0);
 lean_ctor_release(x_1315, 1);
 x_1340 = x_1315;
} else {
 lean_dec_ref(x_1315);
 x_1340 = lean_box(0);
}
if (lean_is_scalar(x_1340)) {
 x_1341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1341 = x_1340;
}
lean_ctor_set(x_1341, 0, x_1338);
lean_ctor_set(x_1341, 1, x_1339);
return x_1341;
}
}
}
else
{
uint8_t x_1342; 
lean_dec(x_1270);
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
x_1342 = !lean_is_exclusive(x_1271);
if (x_1342 == 0)
{
return x_1271;
}
else
{
lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; 
x_1343 = lean_ctor_get(x_1271, 0);
x_1344 = lean_ctor_get(x_1271, 1);
lean_inc(x_1344);
lean_inc(x_1343);
lean_dec(x_1271);
x_1345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1345, 0, x_1343);
lean_ctor_set(x_1345, 1, x_1344);
return x_1345;
}
}
}
else
{
lean_object* x_1346; 
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1346 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1346) == 0)
{
lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1347 = lean_ctor_get(x_1346, 0);
lean_inc(x_1347);
x_1348 = lean_ctor_get(x_1346, 1);
lean_inc(x_1348);
lean_dec(x_1346);
x_1349 = lean_ctor_get(x_1347, 0);
lean_inc(x_1349);
x_1350 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1349, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1348);
if (lean_obj_tag(x_1350) == 0)
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
x_1351 = lean_ctor_get(x_1350, 1);
lean_inc(x_1351);
lean_dec(x_1350);
x_1352 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1351);
x_1353 = lean_ctor_get(x_1352, 1);
lean_inc(x_1353);
lean_dec(x_1352);
x_1354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1354, 0, x_1347);
lean_ctor_set(x_1354, 1, x_2);
x_1355 = l_Lean_Compiler_LCNF_Simp_simp(x_1354, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1353);
if (lean_obj_tag(x_1355) == 0)
{
uint8_t x_1356; 
x_1356 = !lean_is_exclusive(x_1355);
if (x_1356 == 0)
{
lean_object* x_1357; lean_object* x_1358; 
x_1357 = lean_ctor_get(x_1355, 0);
if (lean_is_scalar(x_22)) {
 x_1358 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1358 = x_22;
}
lean_ctor_set(x_1358, 0, x_1357);
lean_ctor_set(x_1355, 0, x_1358);
return x_1355;
}
else
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; 
x_1359 = lean_ctor_get(x_1355, 0);
x_1360 = lean_ctor_get(x_1355, 1);
lean_inc(x_1360);
lean_inc(x_1359);
lean_dec(x_1355);
if (lean_is_scalar(x_22)) {
 x_1361 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1361 = x_22;
}
lean_ctor_set(x_1361, 0, x_1359);
x_1362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1362, 0, x_1361);
lean_ctor_set(x_1362, 1, x_1360);
return x_1362;
}
}
else
{
uint8_t x_1363; 
lean_dec(x_22);
x_1363 = !lean_is_exclusive(x_1355);
if (x_1363 == 0)
{
return x_1355;
}
else
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
x_1364 = lean_ctor_get(x_1355, 0);
x_1365 = lean_ctor_get(x_1355, 1);
lean_inc(x_1365);
lean_inc(x_1364);
lean_dec(x_1355);
x_1366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1366, 0, x_1364);
lean_ctor_set(x_1366, 1, x_1365);
return x_1366;
}
}
}
else
{
uint8_t x_1367; 
lean_dec(x_1347);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1367 = !lean_is_exclusive(x_1350);
if (x_1367 == 0)
{
return x_1350;
}
else
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; 
x_1368 = lean_ctor_get(x_1350, 0);
x_1369 = lean_ctor_get(x_1350, 1);
lean_inc(x_1369);
lean_inc(x_1368);
lean_dec(x_1350);
x_1370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1370, 0, x_1368);
lean_ctor_set(x_1370, 1, x_1369);
return x_1370;
}
}
}
else
{
uint8_t x_1371; 
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
x_1371 = !lean_is_exclusive(x_1346);
if (x_1371 == 0)
{
return x_1346;
}
else
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
x_1372 = lean_ctor_get(x_1346, 0);
x_1373 = lean_ctor_get(x_1346, 1);
lean_inc(x_1373);
lean_inc(x_1372);
lean_dec(x_1346);
x_1374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1374, 0, x_1372);
lean_ctor_set(x_1374, 1, x_1373);
return x_1374;
}
}
}
}
}
}
else
{
uint8_t x_1375; 
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
x_1375 = !lean_is_exclusive(x_12);
if (x_1375 == 0)
{
return x_12;
}
else
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
x_1376 = lean_ctor_get(x_12, 0);
x_1377 = lean_ctor_get(x_12, 1);
lean_inc(x_1377);
lean_inc(x_1376);
lean_dec(x_12);
x_1378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1378, 0, x_1376);
lean_ctor_set(x_1378, 1, x_1377);
return x_1378;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_st_ref_get(x_4, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_15, x_1, x_11);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_17);
x_18 = lean_st_ref_get(x_4, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_21, x_17, x_1);
x_23 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(x_2, x_16, x_22, x_6, x_7, x_8, x_9, x_20);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_4, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_14, x_2, x_1);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_18, x_2, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_4, 3);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_20);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_4, x_21, x_9, x_10, x_11, x_12, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_1, x_2, x_3, x_25, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
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
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_30 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_1, x_16, x_5, x_2, x_3, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
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
x_35 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_1, x_16, x_5, x_2, x_3, x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_34);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_30 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_1, x_16, x_5, x_2, x_3, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
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
x_35 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_1, x_16, x_5, x_2, x_3, x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_34);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
size_t x_80; size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = 0;
x_81 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_82 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__3(x_12, x_80, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_unbox(x_83);
lean_dec(x_83);
x_17 = x_85;
x_18 = x_84;
goto block_78;
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
lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_86 = lean_ctor_get(x_2, 0);
lean_inc(x_86);
x_87 = l_Lean_Compiler_LCNF_Simp_simp(x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_89);
lean_ctor_set(x_87, 0, x_90);
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_87);
x_93 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_87);
if (x_95 == 0)
{
return x_87;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_87, 0);
x_97 = lean_ctor_get(x_87, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_87);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
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
x_21 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
x_22 = lean_nat_dec_eq(x_13, x_14);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_7, 10);
lean_dec(x_24);
x_25 = lean_ctor_get(x_7, 9);
lean_dec(x_25);
x_26 = lean_ctor_get(x_7, 8);
lean_dec(x_26);
x_27 = lean_ctor_get(x_7, 7);
lean_dec(x_27);
x_28 = lean_ctor_get(x_7, 6);
lean_dec(x_28);
x_29 = lean_ctor_get(x_7, 5);
lean_dec(x_29);
x_30 = lean_ctor_get(x_7, 4);
lean_dec(x_30);
x_31 = lean_ctor_get(x_7, 3);
lean_dec(x_31);
x_32 = lean_ctor_get(x_7, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_7, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_7, 0);
lean_dec(x_34);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_13, x_35);
lean_dec(x_13);
lean_ctor_set(x_7, 3, x_36);
x_37 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = 0;
lean_inc(x_39);
x_42 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_41, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1940_(x_39, x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_40, x_39, x_1, x_43, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_40, x_39, x_1, x_43, x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
return x_51;
}
}
case 1:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_dec(x_37);
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
lean_inc(x_1);
lean_inc(x_53);
x_60 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed), 14, 4);
lean_closure_set(x_60, 0, x_54);
lean_closure_set(x_60, 1, x_53);
lean_closure_set(x_60, 2, x_1);
lean_closure_set(x_60, 3, x_57);
x_61 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_box(0);
x_63 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_60, x_53, x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_59);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_53, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_53, 2);
lean_inc(x_65);
x_66 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_64, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_box(0);
x_68 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_60, x_53, x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_59);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_69 = lean_st_ref_get(x_3, x_59);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_74 = l_Lean_Compiler_LCNF_normFunDeclImp(x_73, x_53, x_72, x_5, x_6, x_7, x_8, x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_77 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_75, x_5, x_6, x_7, x_8, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_60, x_78, x_81, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_82);
lean_dec(x_81);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_74);
if (x_88 == 0)
{
return x_74;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_74, 0);
x_90 = lean_ctor_get(x_74, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_74);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_56, 1);
lean_inc(x_92);
lean_dec(x_56);
x_93 = lean_st_ref_get(x_3, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_53);
x_98 = l_Lean_Compiler_LCNF_normFunDeclImp(x_97, x_53, x_96, x_5, x_6, x_7, x_8, x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_box(0);
x_102 = lean_unbox(x_57);
lean_dec(x_57);
x_103 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_54, x_53, x_1, x_102, x_99, x_101, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_100);
return x_103;
}
else
{
uint8_t x_104; 
lean_dec(x_57);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_98);
if (x_104 == 0)
{
return x_98;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_98, 0);
x_106 = lean_ctor_get(x_98, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_98);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
case 2:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_108 = lean_ctor_get(x_37, 1);
lean_inc(x_108);
lean_dec(x_37);
x_109 = lean_ctor_get(x_1, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_1, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_111, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_108);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_unbox(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
lean_inc(x_1);
lean_inc(x_109);
x_116 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed), 14, 4);
lean_closure_set(x_116, 0, x_110);
lean_closure_set(x_116, 1, x_109);
lean_closure_set(x_116, 2, x_1);
lean_closure_set(x_116, 3, x_113);
x_117 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_box(0);
x_119 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_116, x_109, x_118, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_115);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_109, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_109, 2);
lean_inc(x_121);
x_122 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_120, x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_box(0);
x_124 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_116, x_109, x_123, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_115);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; 
x_125 = lean_st_ref_get(x_3, x_115);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_130 = l_Lean_Compiler_LCNF_normFunDeclImp(x_129, x_109, x_128, x_5, x_6, x_7, x_8, x_127);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_133 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_131, x_5, x_6, x_7, x_8, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_116, x_134, x_137, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_138);
lean_dec(x_137);
return x_139;
}
else
{
uint8_t x_140; 
lean_dec(x_116);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_140 = !lean_is_exclusive(x_133);
if (x_140 == 0)
{
return x_133;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_133, 0);
x_142 = lean_ctor_get(x_133, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_133);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_116);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_130);
if (x_144 == 0)
{
return x_130;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_130, 0);
x_146 = lean_ctor_get(x_130, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_130);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; 
x_148 = lean_ctor_get(x_112, 1);
lean_inc(x_148);
lean_dec(x_112);
x_149 = lean_st_ref_get(x_3, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_153 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_109);
x_154 = l_Lean_Compiler_LCNF_normFunDeclImp(x_153, x_109, x_152, x_5, x_6, x_7, x_8, x_151);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_box(0);
x_158 = lean_unbox(x_113);
lean_dec(x_113);
x_159 = l_Lean_Compiler_LCNF_Simp_simp___lambda__7(x_110, x_109, x_1, x_158, x_155, x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_156);
return x_159;
}
else
{
uint8_t x_160; 
lean_dec(x_113);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_154);
if (x_160 == 0)
{
return x_154;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_154, 0);
x_162 = lean_ctor_get(x_154, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_154);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
case 3:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; 
x_164 = lean_ctor_get(x_37, 1);
lean_inc(x_164);
lean_dec(x_37);
x_165 = lean_ctor_get(x_1, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_1, 1);
lean_inc(x_166);
x_167 = lean_st_ref_get(x_3, x_164);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
lean_dec(x_168);
x_171 = 0;
lean_inc(x_165);
x_172 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_170, x_165, x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_197; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec(x_172);
lean_inc(x_166);
x_174 = l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_171, x_166, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_169);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_175);
lean_inc(x_173);
x_197 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_173, x_175, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_176);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
lean_inc(x_173);
x_200 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_173, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_199);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_array_get_size(x_175);
x_203 = lean_unsigned_to_nat(0u);
x_204 = lean_nat_dec_lt(x_203, x_202);
if (x_204 == 0)
{
lean_dec(x_202);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = x_201;
goto block_196;
}
else
{
uint8_t x_205; 
x_205 = lean_nat_dec_le(x_202, x_202);
if (x_205 == 0)
{
lean_dec(x_202);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = x_201;
goto block_196;
}
else
{
size_t x_206; size_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = 0;
x_207 = lean_usize_of_nat(x_202);
lean_dec(x_202);
x_208 = lean_box(0);
x_209 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedLetValue___spec__1(x_175, x_206, x_207, x_208, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_201);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_178 = x_210;
goto block_196;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_173);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_1);
x_211 = lean_ctor_get(x_197, 1);
lean_inc(x_211);
lean_dec(x_197);
x_212 = lean_ctor_get(x_198, 0);
lean_inc(x_212);
lean_dec(x_198);
x_1 = x_212;
x_9 = x_211;
goto _start;
}
}
else
{
uint8_t x_214; 
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_173);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_197);
if (x_214 == 0)
{
return x_197;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_197, 0);
x_216 = lean_ctor_get(x_197, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_197);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
block_196:
{
uint8_t x_179; 
x_179 = lean_name_eq(x_165, x_173);
lean_dec(x_165);
if (x_179 == 0)
{
uint8_t x_180; 
lean_dec(x_166);
x_180 = !lean_is_exclusive(x_1);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_1, 1);
lean_dec(x_181);
x_182 = lean_ctor_get(x_1, 0);
lean_dec(x_182);
lean_ctor_set(x_1, 1, x_175);
lean_ctor_set(x_1, 0, x_173);
if (lean_is_scalar(x_177)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_177;
}
lean_ctor_set(x_183, 0, x_1);
lean_ctor_set(x_183, 1, x_178);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_1);
x_184 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_184, 0, x_173);
lean_ctor_set(x_184, 1, x_175);
if (lean_is_scalar(x_177)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_177;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_178);
return x_185;
}
}
else
{
size_t x_186; size_t x_187; uint8_t x_188; 
x_186 = lean_ptr_addr(x_166);
lean_dec(x_166);
x_187 = lean_ptr_addr(x_175);
x_188 = lean_usize_dec_eq(x_186, x_187);
if (x_188 == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_1);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_1, 1);
lean_dec(x_190);
x_191 = lean_ctor_get(x_1, 0);
lean_dec(x_191);
lean_ctor_set(x_1, 1, x_175);
lean_ctor_set(x_1, 0, x_173);
if (lean_is_scalar(x_177)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_177;
}
lean_ctor_set(x_192, 0, x_1);
lean_ctor_set(x_192, 1, x_178);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_1);
x_193 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_193, 0, x_173);
lean_ctor_set(x_193, 1, x_175);
if (lean_is_scalar(x_177)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_177;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_178);
return x_194;
}
}
else
{
lean_object* x_195; 
lean_dec(x_175);
lean_dec(x_173);
if (lean_is_scalar(x_177)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_177;
}
lean_ctor_set(x_195, 0, x_1);
lean_ctor_set(x_195, 1, x_178);
return x_195;
}
}
}
}
else
{
lean_object* x_218; 
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_218 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_169);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_218;
}
}
case 4:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_37, 1);
lean_inc(x_219);
lean_dec(x_37);
x_220 = lean_ctor_get(x_1, 0);
lean_inc(x_220);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_220);
x_221 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_220, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_219);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; 
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_220, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_220, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_220, 3);
lean_inc(x_227);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 lean_ctor_release(x_220, 2);
 lean_ctor_release(x_220, 3);
 x_228 = x_220;
} else {
 lean_dec_ref(x_220);
 x_228 = lean_box(0);
}
x_229 = lean_st_ref_get(x_3, x_223);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
lean_dec(x_230);
x_233 = 0;
lean_inc(x_226);
x_234 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_232, x_226, x_233);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec(x_234);
x_236 = lean_st_ref_get(x_3, x_231);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
lean_dec(x_237);
lean_inc(x_225);
x_240 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_239, x_233, x_225);
lean_inc(x_235);
x_241 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_235, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_238);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
lean_inc(x_235);
x_243 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__8), 10, 1);
lean_closure_set(x_243, 0, x_235);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_227);
x_244 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(x_227, x_243, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_242);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
x_248 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_245, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_246);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_283; lean_object* x_284; uint8_t x_295; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_251 = x_248;
} else {
 lean_dec_ref(x_248);
 x_251 = lean_box(0);
}
x_283 = lean_array_get_size(x_249);
x_295 = lean_nat_dec_eq(x_283, x_35);
if (x_295 == 0)
{
lean_object* x_296; 
lean_dec(x_283);
lean_dec(x_247);
x_296 = lean_box(0);
x_252 = x_296;
goto block_282;
}
else
{
lean_object* x_297; uint8_t x_298; 
x_297 = lean_unsigned_to_nat(0u);
x_298 = lean_nat_dec_lt(x_297, x_283);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; 
x_299 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_300 = l___private_Init_Util_0__outOfBounds___rarg(x_299);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; 
lean_dec(x_300);
lean_dec(x_283);
lean_dec(x_247);
x_301 = lean_box(0);
x_252 = x_301;
goto block_282;
}
else
{
lean_object* x_302; 
lean_dec(x_300);
lean_dec(x_251);
lean_dec(x_240);
lean_dec(x_235);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_1);
x_302 = lean_box(0);
x_284 = x_302;
goto block_294;
}
}
else
{
lean_object* x_303; 
x_303 = lean_array_fget(x_249, x_297);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; 
lean_dec(x_303);
lean_dec(x_283);
lean_dec(x_247);
x_304 = lean_box(0);
x_252 = x_304;
goto block_282;
}
else
{
lean_object* x_305; 
lean_dec(x_303);
lean_dec(x_251);
lean_dec(x_240);
lean_dec(x_235);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_1);
x_305 = lean_box(0);
x_284 = x_305;
goto block_294;
}
}
}
block_282:
{
size_t x_253; size_t x_254; uint8_t x_255; 
lean_dec(x_252);
x_253 = lean_ptr_addr(x_227);
lean_dec(x_227);
x_254 = lean_ptr_addr(x_249);
x_255 = lean_usize_dec_eq(x_253, x_254);
if (x_255 == 0)
{
uint8_t x_256; 
lean_dec(x_226);
lean_dec(x_225);
x_256 = !lean_is_exclusive(x_1);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_1, 0);
lean_dec(x_257);
if (lean_is_scalar(x_228)) {
 x_258 = lean_alloc_ctor(0, 4, 0);
} else {
 x_258 = x_228;
}
lean_ctor_set(x_258, 0, x_224);
lean_ctor_set(x_258, 1, x_240);
lean_ctor_set(x_258, 2, x_235);
lean_ctor_set(x_258, 3, x_249);
lean_ctor_set(x_1, 0, x_258);
if (lean_is_scalar(x_251)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_251;
}
lean_ctor_set(x_259, 0, x_1);
lean_ctor_set(x_259, 1, x_250);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_1);
if (lean_is_scalar(x_228)) {
 x_260 = lean_alloc_ctor(0, 4, 0);
} else {
 x_260 = x_228;
}
lean_ctor_set(x_260, 0, x_224);
lean_ctor_set(x_260, 1, x_240);
lean_ctor_set(x_260, 2, x_235);
lean_ctor_set(x_260, 3, x_249);
x_261 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_261, 0, x_260);
if (lean_is_scalar(x_251)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_251;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_250);
return x_262;
}
}
else
{
size_t x_263; size_t x_264; uint8_t x_265; 
x_263 = lean_ptr_addr(x_225);
lean_dec(x_225);
x_264 = lean_ptr_addr(x_240);
x_265 = lean_usize_dec_eq(x_263, x_264);
if (x_265 == 0)
{
uint8_t x_266; 
lean_dec(x_226);
x_266 = !lean_is_exclusive(x_1);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_1, 0);
lean_dec(x_267);
if (lean_is_scalar(x_228)) {
 x_268 = lean_alloc_ctor(0, 4, 0);
} else {
 x_268 = x_228;
}
lean_ctor_set(x_268, 0, x_224);
lean_ctor_set(x_268, 1, x_240);
lean_ctor_set(x_268, 2, x_235);
lean_ctor_set(x_268, 3, x_249);
lean_ctor_set(x_1, 0, x_268);
if (lean_is_scalar(x_251)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_251;
}
lean_ctor_set(x_269, 0, x_1);
lean_ctor_set(x_269, 1, x_250);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_1);
if (lean_is_scalar(x_228)) {
 x_270 = lean_alloc_ctor(0, 4, 0);
} else {
 x_270 = x_228;
}
lean_ctor_set(x_270, 0, x_224);
lean_ctor_set(x_270, 1, x_240);
lean_ctor_set(x_270, 2, x_235);
lean_ctor_set(x_270, 3, x_249);
x_271 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_271, 0, x_270);
if (lean_is_scalar(x_251)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_251;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_250);
return x_272;
}
}
else
{
uint8_t x_273; 
x_273 = lean_name_eq(x_226, x_235);
lean_dec(x_226);
if (x_273 == 0)
{
uint8_t x_274; 
x_274 = !lean_is_exclusive(x_1);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_1, 0);
lean_dec(x_275);
if (lean_is_scalar(x_228)) {
 x_276 = lean_alloc_ctor(0, 4, 0);
} else {
 x_276 = x_228;
}
lean_ctor_set(x_276, 0, x_224);
lean_ctor_set(x_276, 1, x_240);
lean_ctor_set(x_276, 2, x_235);
lean_ctor_set(x_276, 3, x_249);
lean_ctor_set(x_1, 0, x_276);
if (lean_is_scalar(x_251)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_251;
}
lean_ctor_set(x_277, 0, x_1);
lean_ctor_set(x_277, 1, x_250);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_1);
if (lean_is_scalar(x_228)) {
 x_278 = lean_alloc_ctor(0, 4, 0);
} else {
 x_278 = x_228;
}
lean_ctor_set(x_278, 0, x_224);
lean_ctor_set(x_278, 1, x_240);
lean_ctor_set(x_278, 2, x_235);
lean_ctor_set(x_278, 3, x_249);
x_279 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_279, 0, x_278);
if (lean_is_scalar(x_251)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_251;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_250);
return x_280;
}
}
else
{
lean_object* x_281; 
lean_dec(x_249);
lean_dec(x_240);
lean_dec(x_235);
lean_dec(x_228);
lean_dec(x_224);
if (lean_is_scalar(x_251)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_251;
}
lean_ctor_set(x_281, 0, x_1);
lean_ctor_set(x_281, 1, x_250);
return x_281;
}
}
}
}
block_294:
{
lean_object* x_285; uint8_t x_286; 
lean_dec(x_284);
x_285 = lean_unsigned_to_nat(0u);
x_286 = lean_nat_dec_lt(x_285, x_283);
lean_dec(x_283);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_249);
x_287 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_288 = l___private_Init_Util_0__outOfBounds___rarg(x_287);
x_289 = l_Lean_Compiler_LCNF_AltCore_getCode(x_288);
lean_dec(x_288);
if (lean_is_scalar(x_247)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_247;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_250);
return x_290;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_array_fget(x_249, x_285);
lean_dec(x_249);
x_292 = l_Lean_Compiler_LCNF_AltCore_getCode(x_291);
lean_dec(x_291);
if (lean_is_scalar(x_247)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_247;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_250);
return x_293;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_247);
lean_dec(x_240);
lean_dec(x_235);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_248);
if (x_306 == 0)
{
return x_248;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_248, 0);
x_308 = lean_ctor_get(x_248, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_248);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_240);
lean_dec(x_235);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_310 = !lean_is_exclusive(x_244);
if (x_310 == 0)
{
return x_244;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_244, 0);
x_312 = lean_ctor_get(x_244, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_244);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
lean_object* x_314; 
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_314 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_231);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_314;
}
}
else
{
uint8_t x_315; 
lean_dec(x_220);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_315 = !lean_is_exclusive(x_221);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_221, 0);
lean_dec(x_316);
x_317 = lean_ctor_get(x_222, 0);
lean_inc(x_317);
lean_dec(x_222);
lean_ctor_set(x_221, 0, x_317);
return x_221;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_221, 1);
lean_inc(x_318);
lean_dec(x_221);
x_319 = lean_ctor_get(x_222, 0);
lean_inc(x_319);
lean_dec(x_222);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
}
else
{
uint8_t x_321; 
lean_dec(x_220);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_321 = !lean_is_exclusive(x_221);
if (x_321 == 0)
{
return x_221;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_221, 0);
x_323 = lean_ctor_get(x_221, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_221);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
}
case 5:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; 
x_325 = lean_ctor_get(x_37, 1);
lean_inc(x_325);
lean_dec(x_37);
x_326 = lean_ctor_get(x_1, 0);
lean_inc(x_326);
x_327 = lean_st_ref_get(x_3, x_325);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_ctor_get(x_328, 0);
lean_inc(x_330);
lean_dec(x_328);
x_331 = 0;
lean_inc(x_326);
x_332 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_330, x_326, x_331);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
lean_dec(x_332);
lean_inc(x_333);
x_334 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_333, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_329);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_335 = !lean_is_exclusive(x_334);
if (x_335 == 0)
{
lean_object* x_336; uint8_t x_337; 
x_336 = lean_ctor_get(x_334, 0);
lean_dec(x_336);
x_337 = lean_name_eq(x_326, x_333);
lean_dec(x_326);
if (x_337 == 0)
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_1);
if (x_338 == 0)
{
lean_object* x_339; 
x_339 = lean_ctor_get(x_1, 0);
lean_dec(x_339);
lean_ctor_set(x_1, 0, x_333);
lean_ctor_set(x_334, 0, x_1);
return x_334;
}
else
{
lean_object* x_340; 
lean_dec(x_1);
x_340 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_340, 0, x_333);
lean_ctor_set(x_334, 0, x_340);
return x_334;
}
}
else
{
lean_dec(x_333);
lean_ctor_set(x_334, 0, x_1);
return x_334;
}
}
else
{
lean_object* x_341; uint8_t x_342; 
x_341 = lean_ctor_get(x_334, 1);
lean_inc(x_341);
lean_dec(x_334);
x_342 = lean_name_eq(x_326, x_333);
lean_dec(x_326);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_343 = x_1;
} else {
 lean_dec_ref(x_1);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(5, 1, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_333);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_341);
return x_345;
}
else
{
lean_object* x_346; 
lean_dec(x_333);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_1);
lean_ctor_set(x_346, 1, x_341);
return x_346;
}
}
}
else
{
lean_object* x_347; 
lean_dec(x_326);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_347 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_329);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_347;
}
}
default: 
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_348 = lean_ctor_get(x_37, 1);
lean_inc(x_348);
lean_dec(x_37);
x_349 = lean_ctor_get(x_1, 0);
lean_inc(x_349);
x_350 = lean_st_ref_get(x_3, x_348);
lean_dec(x_3);
x_351 = !lean_is_exclusive(x_350);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; uint8_t x_354; lean_object* x_355; size_t x_356; size_t x_357; uint8_t x_358; 
x_352 = lean_ctor_get(x_350, 0);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec(x_352);
x_354 = 0;
lean_inc(x_349);
x_355 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_353, x_354, x_349);
x_356 = lean_ptr_addr(x_349);
lean_dec(x_349);
x_357 = lean_ptr_addr(x_355);
x_358 = lean_usize_dec_eq(x_356, x_357);
if (x_358 == 0)
{
uint8_t x_359; 
x_359 = !lean_is_exclusive(x_1);
if (x_359 == 0)
{
lean_object* x_360; 
x_360 = lean_ctor_get(x_1, 0);
lean_dec(x_360);
lean_ctor_set(x_1, 0, x_355);
lean_ctor_set(x_350, 0, x_1);
return x_350;
}
else
{
lean_object* x_361; 
lean_dec(x_1);
x_361 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_361, 0, x_355);
lean_ctor_set(x_350, 0, x_361);
return x_350;
}
}
else
{
lean_dec(x_355);
lean_ctor_set(x_350, 0, x_1);
return x_350;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; lean_object* x_366; size_t x_367; size_t x_368; uint8_t x_369; 
x_362 = lean_ctor_get(x_350, 0);
x_363 = lean_ctor_get(x_350, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_350);
x_364 = lean_ctor_get(x_362, 0);
lean_inc(x_364);
lean_dec(x_362);
x_365 = 0;
lean_inc(x_349);
x_366 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_364, x_365, x_349);
x_367 = lean_ptr_addr(x_349);
lean_dec(x_349);
x_368 = lean_ptr_addr(x_366);
x_369 = lean_usize_dec_eq(x_367, x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_370 = x_1;
} else {
 lean_dec_ref(x_1);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(6, 1, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_366);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_363);
return x_372;
}
else
{
lean_object* x_373; 
lean_dec(x_366);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_1);
lean_ctor_set(x_373, 1, x_363);
return x_373;
}
}
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_7);
x_374 = lean_unsigned_to_nat(1u);
x_375 = lean_nat_add(x_13, x_374);
lean_dec(x_13);
x_376 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_376, 0, x_10);
lean_ctor_set(x_376, 1, x_11);
lean_ctor_set(x_376, 2, x_12);
lean_ctor_set(x_376, 3, x_375);
lean_ctor_set(x_376, 4, x_14);
lean_ctor_set(x_376, 5, x_15);
lean_ctor_set(x_376, 6, x_16);
lean_ctor_set(x_376, 7, x_17);
lean_ctor_set(x_376, 8, x_18);
lean_ctor_set(x_376, 9, x_19);
lean_ctor_set(x_376, 10, x_20);
lean_ctor_set_uint8(x_376, sizeof(void*)*11, x_21);
x_377 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_5, x_6, x_376, x_8, x_9);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
lean_dec(x_377);
x_379 = lean_ctor_get(x_1, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_1, 1);
lean_inc(x_380);
x_381 = 0;
lean_inc(x_379);
x_382 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_381, x_379, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_378);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
x_385 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1940_(x_379, x_383);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_386 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_376, x_8, x_384);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_380, x_379, x_1, x_383, x_387, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_388);
return x_389;
}
else
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_box(0);
x_391 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_380, x_379, x_1, x_383, x_390, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_384);
return x_391;
}
}
case 1:
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_392 = lean_ctor_get(x_377, 1);
lean_inc(x_392);
lean_dec(x_377);
x_393 = lean_ctor_get(x_1, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_1, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 0);
lean_inc(x_395);
x_396 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_395, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_392);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_unbox(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_dec(x_396);
lean_inc(x_1);
lean_inc(x_393);
x_400 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed), 14, 4);
lean_closure_set(x_400, 0, x_394);
lean_closure_set(x_400, 1, x_393);
lean_closure_set(x_400, 2, x_1);
lean_closure_set(x_400, 3, x_397);
x_401 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_box(0);
x_403 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_400, x_393, x_402, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_399);
return x_403;
}
else
{
lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_404 = lean_ctor_get(x_393, 3);
lean_inc(x_404);
x_405 = lean_ctor_get(x_393, 2);
lean_inc(x_405);
x_406 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_404, x_405);
lean_dec(x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_box(0);
x_408 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_400, x_393, x_407, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_399);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; lean_object* x_414; 
x_409 = lean_st_ref_get(x_3, x_399);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
lean_dec(x_410);
x_413 = 0;
lean_inc(x_8);
lean_inc(x_376);
lean_inc(x_6);
lean_inc(x_5);
x_414 = l_Lean_Compiler_LCNF_normFunDeclImp(x_413, x_393, x_412, x_5, x_6, x_376, x_8, x_411);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
lean_inc(x_8);
lean_inc(x_376);
lean_inc(x_6);
lean_inc(x_5);
x_417 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_415, x_5, x_6, x_376, x_8, x_416);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_376, x_8, x_419);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_400, x_418, x_421, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_422);
lean_dec(x_421);
return x_423;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_400);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_424 = lean_ctor_get(x_417, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_417, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_426 = x_417;
} else {
 lean_dec_ref(x_417);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_426)) {
 x_427 = lean_alloc_ctor(1, 2, 0);
} else {
 x_427 = x_426;
}
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_425);
return x_427;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_400);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_428 = lean_ctor_get(x_414, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_414, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_430 = x_414;
} else {
 lean_dec_ref(x_414);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_428);
lean_ctor_set(x_431, 1, x_429);
return x_431;
}
}
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; lean_object* x_438; 
x_432 = lean_ctor_get(x_396, 1);
lean_inc(x_432);
lean_dec(x_396);
x_433 = lean_st_ref_get(x_3, x_432);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_436 = lean_ctor_get(x_434, 0);
lean_inc(x_436);
lean_dec(x_434);
x_437 = 0;
lean_inc(x_8);
lean_inc(x_376);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_393);
x_438 = l_Lean_Compiler_LCNF_normFunDeclImp(x_437, x_393, x_436, x_5, x_6, x_376, x_8, x_435);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_441 = lean_box(0);
x_442 = lean_unbox(x_397);
lean_dec(x_397);
x_443 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_394, x_393, x_1, x_442, x_439, x_441, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_440);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_397);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_444 = lean_ctor_get(x_438, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_438, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_446 = x_438;
} else {
 lean_dec_ref(x_438);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 2, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_445);
return x_447;
}
}
}
case 2:
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_448 = lean_ctor_get(x_377, 1);
lean_inc(x_448);
lean_dec(x_377);
x_449 = lean_ctor_get(x_1, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_1, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 0);
lean_inc(x_451);
x_452 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_451, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_448);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_unbox(x_453);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_455 = lean_ctor_get(x_452, 1);
lean_inc(x_455);
lean_dec(x_452);
lean_inc(x_1);
lean_inc(x_449);
x_456 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed), 14, 4);
lean_closure_set(x_456, 0, x_450);
lean_closure_set(x_456, 1, x_449);
lean_closure_set(x_456, 2, x_1);
lean_closure_set(x_456, 3, x_453);
x_457 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; 
x_458 = lean_box(0);
x_459 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_456, x_449, x_458, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_455);
return x_459;
}
else
{
lean_object* x_460; lean_object* x_461; uint8_t x_462; 
x_460 = lean_ctor_get(x_449, 3);
lean_inc(x_460);
x_461 = lean_ctor_get(x_449, 2);
lean_inc(x_461);
x_462 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_460, x_461);
lean_dec(x_461);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; 
x_463 = lean_box(0);
x_464 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_456, x_449, x_463, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_455);
return x_464;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; 
x_465 = lean_st_ref_get(x_3, x_455);
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_468 = lean_ctor_get(x_466, 0);
lean_inc(x_468);
lean_dec(x_466);
x_469 = 0;
lean_inc(x_8);
lean_inc(x_376);
lean_inc(x_6);
lean_inc(x_5);
x_470 = l_Lean_Compiler_LCNF_normFunDeclImp(x_469, x_449, x_468, x_5, x_6, x_376, x_8, x_467);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
lean_inc(x_8);
lean_inc(x_376);
lean_inc(x_6);
lean_inc(x_5);
x_473 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_471, x_5, x_6, x_376, x_8, x_472);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
lean_dec(x_473);
x_476 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_376, x_8, x_475);
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
x_479 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_456, x_474, x_477, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_478);
lean_dec(x_477);
return x_479;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_456);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_480 = lean_ctor_get(x_473, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_473, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_482 = x_473;
} else {
 lean_dec_ref(x_473);
 x_482 = lean_box(0);
}
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 2, 0);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_480);
lean_ctor_set(x_483, 1, x_481);
return x_483;
}
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
lean_dec(x_456);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_484 = lean_ctor_get(x_470, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_470, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_486 = x_470;
} else {
 lean_dec_ref(x_470);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 2, 0);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_485);
return x_487;
}
}
}
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; lean_object* x_494; 
x_488 = lean_ctor_get(x_452, 1);
lean_inc(x_488);
lean_dec(x_452);
x_489 = lean_st_ref_get(x_3, x_488);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
lean_dec(x_489);
x_492 = lean_ctor_get(x_490, 0);
lean_inc(x_492);
lean_dec(x_490);
x_493 = 0;
lean_inc(x_8);
lean_inc(x_376);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_449);
x_494 = l_Lean_Compiler_LCNF_normFunDeclImp(x_493, x_449, x_492, x_5, x_6, x_376, x_8, x_491);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; lean_object* x_499; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = lean_box(0);
x_498 = lean_unbox(x_453);
lean_dec(x_453);
x_499 = l_Lean_Compiler_LCNF_Simp_simp___lambda__7(x_450, x_449, x_1, x_498, x_495, x_497, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_496);
return x_499;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_453);
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_500 = lean_ctor_get(x_494, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_494, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_502 = x_494;
} else {
 lean_dec_ref(x_494);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_501);
return x_503;
}
}
}
case 3:
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_504 = lean_ctor_get(x_377, 1);
lean_inc(x_504);
lean_dec(x_377);
x_505 = lean_ctor_get(x_1, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_1, 1);
lean_inc(x_506);
x_507 = lean_st_ref_get(x_3, x_504);
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
lean_dec(x_508);
x_511 = 0;
lean_inc(x_505);
x_512 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_510, x_505, x_511);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_531; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
lean_dec(x_512);
lean_inc(x_506);
x_514 = l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_511, x_506, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_509);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 x_517 = x_514;
} else {
 lean_dec_ref(x_514);
 x_517 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_376);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_515);
lean_inc(x_513);
x_531 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_513, x_515, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_516);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec(x_531);
lean_inc(x_513);
x_534 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_513, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_533);
x_535 = lean_ctor_get(x_534, 1);
lean_inc(x_535);
lean_dec(x_534);
x_536 = lean_array_get_size(x_515);
x_537 = lean_unsigned_to_nat(0u);
x_538 = lean_nat_dec_lt(x_537, x_536);
if (x_538 == 0)
{
lean_dec(x_536);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_518 = x_535;
goto block_530;
}
else
{
uint8_t x_539; 
x_539 = lean_nat_dec_le(x_536, x_536);
if (x_539 == 0)
{
lean_dec(x_536);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_518 = x_535;
goto block_530;
}
else
{
size_t x_540; size_t x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_540 = 0;
x_541 = lean_usize_of_nat(x_536);
lean_dec(x_536);
x_542 = lean_box(0);
x_543 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedLetValue___spec__1(x_515, x_540, x_541, x_542, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_535);
lean_dec(x_8);
lean_dec(x_376);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_544 = lean_ctor_get(x_543, 1);
lean_inc(x_544);
lean_dec(x_543);
x_518 = x_544;
goto block_530;
}
}
}
else
{
lean_object* x_545; lean_object* x_546; 
lean_dec(x_517);
lean_dec(x_515);
lean_dec(x_513);
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_1);
x_545 = lean_ctor_get(x_531, 1);
lean_inc(x_545);
lean_dec(x_531);
x_546 = lean_ctor_get(x_532, 0);
lean_inc(x_546);
lean_dec(x_532);
x_1 = x_546;
x_7 = x_376;
x_9 = x_545;
goto _start;
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_517);
lean_dec(x_515);
lean_dec(x_513);
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_548 = lean_ctor_get(x_531, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_531, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_550 = x_531;
} else {
 lean_dec_ref(x_531);
 x_550 = lean_box(0);
}
if (lean_is_scalar(x_550)) {
 x_551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_551 = x_550;
}
lean_ctor_set(x_551, 0, x_548);
lean_ctor_set(x_551, 1, x_549);
return x_551;
}
block_530:
{
uint8_t x_519; 
x_519 = lean_name_eq(x_505, x_513);
lean_dec(x_505);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_506);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_520 = x_1;
} else {
 lean_dec_ref(x_1);
 x_520 = lean_box(0);
}
if (lean_is_scalar(x_520)) {
 x_521 = lean_alloc_ctor(3, 2, 0);
} else {
 x_521 = x_520;
}
lean_ctor_set(x_521, 0, x_513);
lean_ctor_set(x_521, 1, x_515);
if (lean_is_scalar(x_517)) {
 x_522 = lean_alloc_ctor(0, 2, 0);
} else {
 x_522 = x_517;
}
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_518);
return x_522;
}
else
{
size_t x_523; size_t x_524; uint8_t x_525; 
x_523 = lean_ptr_addr(x_506);
lean_dec(x_506);
x_524 = lean_ptr_addr(x_515);
x_525 = lean_usize_dec_eq(x_523, x_524);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_526 = x_1;
} else {
 lean_dec_ref(x_1);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(3, 2, 0);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_513);
lean_ctor_set(x_527, 1, x_515);
if (lean_is_scalar(x_517)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_517;
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_518);
return x_528;
}
else
{
lean_object* x_529; 
lean_dec(x_515);
lean_dec(x_513);
if (lean_is_scalar(x_517)) {
 x_529 = lean_alloc_ctor(0, 2, 0);
} else {
 x_529 = x_517;
}
lean_ctor_set(x_529, 0, x_1);
lean_ctor_set(x_529, 1, x_518);
return x_529;
}
}
}
}
else
{
lean_object* x_552; 
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_552 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_376, x_8, x_509);
lean_dec(x_8);
lean_dec(x_376);
lean_dec(x_6);
lean_dec(x_5);
return x_552;
}
}
case 4:
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_377, 1);
lean_inc(x_553);
lean_dec(x_377);
x_554 = lean_ctor_get(x_1, 0);
lean_inc(x_554);
lean_inc(x_8);
lean_inc(x_376);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_554);
x_555 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_554, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_553);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; lean_object* x_568; 
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = lean_ctor_get(x_554, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_554, 1);
lean_inc(x_559);
x_560 = lean_ctor_get(x_554, 2);
lean_inc(x_560);
x_561 = lean_ctor_get(x_554, 3);
lean_inc(x_561);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 lean_ctor_release(x_554, 2);
 lean_ctor_release(x_554, 3);
 x_562 = x_554;
} else {
 lean_dec_ref(x_554);
 x_562 = lean_box(0);
}
x_563 = lean_st_ref_get(x_3, x_557);
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_563, 1);
lean_inc(x_565);
lean_dec(x_563);
x_566 = lean_ctor_get(x_564, 0);
lean_inc(x_566);
lean_dec(x_564);
x_567 = 0;
lean_inc(x_560);
x_568 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_566, x_560, x_567);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
lean_dec(x_568);
x_570 = lean_st_ref_get(x_3, x_565);
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec(x_570);
x_573 = lean_ctor_get(x_571, 0);
lean_inc(x_573);
lean_dec(x_571);
lean_inc(x_559);
x_574 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_573, x_567, x_559);
lean_inc(x_569);
x_575 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_569, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_572);
x_576 = lean_ctor_get(x_575, 1);
lean_inc(x_576);
lean_dec(x_575);
lean_inc(x_569);
x_577 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__8), 10, 1);
lean_closure_set(x_577, 0, x_569);
lean_inc(x_8);
lean_inc(x_376);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_561);
x_578 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(x_561, x_577, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_576);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_578, 1);
lean_inc(x_580);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 x_581 = x_578;
} else {
 lean_dec_ref(x_578);
 x_581 = lean_box(0);
}
x_582 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_579, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_580);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_608; lean_object* x_609; uint8_t x_620; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_585 = x_582;
} else {
 lean_dec_ref(x_582);
 x_585 = lean_box(0);
}
x_608 = lean_array_get_size(x_583);
x_620 = lean_nat_dec_eq(x_608, x_374);
if (x_620 == 0)
{
lean_object* x_621; 
lean_dec(x_608);
lean_dec(x_581);
x_621 = lean_box(0);
x_586 = x_621;
goto block_607;
}
else
{
lean_object* x_622; uint8_t x_623; 
x_622 = lean_unsigned_to_nat(0u);
x_623 = lean_nat_dec_lt(x_622, x_608);
if (x_623 == 0)
{
lean_object* x_624; lean_object* x_625; 
x_624 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_625 = l___private_Init_Util_0__outOfBounds___rarg(x_624);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; 
lean_dec(x_625);
lean_dec(x_608);
lean_dec(x_581);
x_626 = lean_box(0);
x_586 = x_626;
goto block_607;
}
else
{
lean_object* x_627; 
lean_dec(x_625);
lean_dec(x_585);
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_1);
x_627 = lean_box(0);
x_609 = x_627;
goto block_619;
}
}
else
{
lean_object* x_628; 
x_628 = lean_array_fget(x_583, x_622);
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; 
lean_dec(x_628);
lean_dec(x_608);
lean_dec(x_581);
x_629 = lean_box(0);
x_586 = x_629;
goto block_607;
}
else
{
lean_object* x_630; 
lean_dec(x_628);
lean_dec(x_585);
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_1);
x_630 = lean_box(0);
x_609 = x_630;
goto block_619;
}
}
}
block_607:
{
size_t x_587; size_t x_588; uint8_t x_589; 
lean_dec(x_586);
x_587 = lean_ptr_addr(x_561);
lean_dec(x_561);
x_588 = lean_ptr_addr(x_583);
x_589 = lean_usize_dec_eq(x_587, x_588);
if (x_589 == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_560);
lean_dec(x_559);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_590 = x_1;
} else {
 lean_dec_ref(x_1);
 x_590 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_591 = lean_alloc_ctor(0, 4, 0);
} else {
 x_591 = x_562;
}
lean_ctor_set(x_591, 0, x_558);
lean_ctor_set(x_591, 1, x_574);
lean_ctor_set(x_591, 2, x_569);
lean_ctor_set(x_591, 3, x_583);
if (lean_is_scalar(x_590)) {
 x_592 = lean_alloc_ctor(4, 1, 0);
} else {
 x_592 = x_590;
}
lean_ctor_set(x_592, 0, x_591);
if (lean_is_scalar(x_585)) {
 x_593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_593 = x_585;
}
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_584);
return x_593;
}
else
{
size_t x_594; size_t x_595; uint8_t x_596; 
x_594 = lean_ptr_addr(x_559);
lean_dec(x_559);
x_595 = lean_ptr_addr(x_574);
x_596 = lean_usize_dec_eq(x_594, x_595);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_560);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_597 = x_1;
} else {
 lean_dec_ref(x_1);
 x_597 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_598 = lean_alloc_ctor(0, 4, 0);
} else {
 x_598 = x_562;
}
lean_ctor_set(x_598, 0, x_558);
lean_ctor_set(x_598, 1, x_574);
lean_ctor_set(x_598, 2, x_569);
lean_ctor_set(x_598, 3, x_583);
if (lean_is_scalar(x_597)) {
 x_599 = lean_alloc_ctor(4, 1, 0);
} else {
 x_599 = x_597;
}
lean_ctor_set(x_599, 0, x_598);
if (lean_is_scalar(x_585)) {
 x_600 = lean_alloc_ctor(0, 2, 0);
} else {
 x_600 = x_585;
}
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_584);
return x_600;
}
else
{
uint8_t x_601; 
x_601 = lean_name_eq(x_560, x_569);
lean_dec(x_560);
if (x_601 == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_602 = x_1;
} else {
 lean_dec_ref(x_1);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_603 = lean_alloc_ctor(0, 4, 0);
} else {
 x_603 = x_562;
}
lean_ctor_set(x_603, 0, x_558);
lean_ctor_set(x_603, 1, x_574);
lean_ctor_set(x_603, 2, x_569);
lean_ctor_set(x_603, 3, x_583);
if (lean_is_scalar(x_602)) {
 x_604 = lean_alloc_ctor(4, 1, 0);
} else {
 x_604 = x_602;
}
lean_ctor_set(x_604, 0, x_603);
if (lean_is_scalar(x_585)) {
 x_605 = lean_alloc_ctor(0, 2, 0);
} else {
 x_605 = x_585;
}
lean_ctor_set(x_605, 0, x_604);
lean_ctor_set(x_605, 1, x_584);
return x_605;
}
else
{
lean_object* x_606; 
lean_dec(x_583);
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_562);
lean_dec(x_558);
if (lean_is_scalar(x_585)) {
 x_606 = lean_alloc_ctor(0, 2, 0);
} else {
 x_606 = x_585;
}
lean_ctor_set(x_606, 0, x_1);
lean_ctor_set(x_606, 1, x_584);
return x_606;
}
}
}
}
block_619:
{
lean_object* x_610; uint8_t x_611; 
lean_dec(x_609);
x_610 = lean_unsigned_to_nat(0u);
x_611 = lean_nat_dec_lt(x_610, x_608);
lean_dec(x_608);
if (x_611 == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_583);
x_612 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_613 = l___private_Init_Util_0__outOfBounds___rarg(x_612);
x_614 = l_Lean_Compiler_LCNF_AltCore_getCode(x_613);
lean_dec(x_613);
if (lean_is_scalar(x_581)) {
 x_615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_615 = x_581;
}
lean_ctor_set(x_615, 0, x_614);
lean_ctor_set(x_615, 1, x_584);
return x_615;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_array_fget(x_583, x_610);
lean_dec(x_583);
x_617 = l_Lean_Compiler_LCNF_AltCore_getCode(x_616);
lean_dec(x_616);
if (lean_is_scalar(x_581)) {
 x_618 = lean_alloc_ctor(0, 2, 0);
} else {
 x_618 = x_581;
}
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_584);
return x_618;
}
}
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_581);
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_1);
x_631 = lean_ctor_get(x_582, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_582, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_633 = x_582;
} else {
 lean_dec_ref(x_582);
 x_633 = lean_box(0);
}
if (lean_is_scalar(x_633)) {
 x_634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_634 = x_633;
}
lean_ctor_set(x_634, 0, x_631);
lean_ctor_set(x_634, 1, x_632);
return x_634;
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_635 = lean_ctor_get(x_578, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_578, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 x_637 = x_578;
} else {
 lean_dec_ref(x_578);
 x_637 = lean_box(0);
}
if (lean_is_scalar(x_637)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_637;
}
lean_ctor_set(x_638, 0, x_635);
lean_ctor_set(x_638, 1, x_636);
return x_638;
}
}
else
{
lean_object* x_639; 
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_639 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_376, x_8, x_565);
lean_dec(x_8);
lean_dec(x_376);
lean_dec(x_6);
lean_dec(x_5);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_554);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_640 = lean_ctor_get(x_555, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_641 = x_555;
} else {
 lean_dec_ref(x_555);
 x_641 = lean_box(0);
}
x_642 = lean_ctor_get(x_556, 0);
lean_inc(x_642);
lean_dec(x_556);
if (lean_is_scalar(x_641)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_641;
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_640);
return x_643;
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_dec(x_554);
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_644 = lean_ctor_get(x_555, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_555, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_646 = x_555;
} else {
 lean_dec_ref(x_555);
 x_646 = lean_box(0);
}
if (lean_is_scalar(x_646)) {
 x_647 = lean_alloc_ctor(1, 2, 0);
} else {
 x_647 = x_646;
}
lean_ctor_set(x_647, 0, x_644);
lean_ctor_set(x_647, 1, x_645);
return x_647;
}
}
case 5:
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; uint8_t x_654; lean_object* x_655; 
x_648 = lean_ctor_get(x_377, 1);
lean_inc(x_648);
lean_dec(x_377);
x_649 = lean_ctor_get(x_1, 0);
lean_inc(x_649);
x_650 = lean_st_ref_get(x_3, x_648);
x_651 = lean_ctor_get(x_650, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_650, 1);
lean_inc(x_652);
lean_dec(x_650);
x_653 = lean_ctor_get(x_651, 0);
lean_inc(x_653);
lean_dec(x_651);
x_654 = 0;
lean_inc(x_649);
x_655 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_653, x_649, x_654);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_660; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
lean_dec(x_655);
lean_inc(x_656);
x_657 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_656, x_2, x_3, x_4, x_5, x_6, x_376, x_8, x_652);
lean_dec(x_8);
lean_dec(x_376);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_658 = lean_ctor_get(x_657, 1);
lean_inc(x_658);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_659 = x_657;
} else {
 lean_dec_ref(x_657);
 x_659 = lean_box(0);
}
x_660 = lean_name_eq(x_649, x_656);
lean_dec(x_649);
if (x_660 == 0)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_661 = x_1;
} else {
 lean_dec_ref(x_1);
 x_661 = lean_box(0);
}
if (lean_is_scalar(x_661)) {
 x_662 = lean_alloc_ctor(5, 1, 0);
} else {
 x_662 = x_661;
}
lean_ctor_set(x_662, 0, x_656);
if (lean_is_scalar(x_659)) {
 x_663 = lean_alloc_ctor(0, 2, 0);
} else {
 x_663 = x_659;
}
lean_ctor_set(x_663, 0, x_662);
lean_ctor_set(x_663, 1, x_658);
return x_663;
}
else
{
lean_object* x_664; 
lean_dec(x_656);
if (lean_is_scalar(x_659)) {
 x_664 = lean_alloc_ctor(0, 2, 0);
} else {
 x_664 = x_659;
}
lean_ctor_set(x_664, 0, x_1);
lean_ctor_set(x_664, 1, x_658);
return x_664;
}
}
else
{
lean_object* x_665; 
lean_dec(x_649);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_665 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_376, x_8, x_652);
lean_dec(x_8);
lean_dec(x_376);
lean_dec(x_6);
lean_dec(x_5);
return x_665;
}
}
default: 
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; uint8_t x_673; lean_object* x_674; size_t x_675; size_t x_676; uint8_t x_677; 
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_666 = lean_ctor_get(x_377, 1);
lean_inc(x_666);
lean_dec(x_377);
x_667 = lean_ctor_get(x_1, 0);
lean_inc(x_667);
x_668 = lean_st_ref_get(x_3, x_666);
lean_dec(x_3);
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_671 = x_668;
} else {
 lean_dec_ref(x_668);
 x_671 = lean_box(0);
}
x_672 = lean_ctor_get(x_669, 0);
lean_inc(x_672);
lean_dec(x_669);
x_673 = 0;
lean_inc(x_667);
x_674 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_672, x_673, x_667);
x_675 = lean_ptr_addr(x_667);
lean_dec(x_667);
x_676 = lean_ptr_addr(x_674);
x_677 = lean_usize_dec_eq(x_675, x_676);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_678 = x_1;
} else {
 lean_dec_ref(x_1);
 x_678 = lean_box(0);
}
if (lean_is_scalar(x_678)) {
 x_679 = lean_alloc_ctor(6, 1, 0);
} else {
 x_679 = x_678;
}
lean_ctor_set(x_679, 0, x_674);
if (lean_is_scalar(x_671)) {
 x_680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_680 = x_671;
}
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_670);
return x_680;
}
else
{
lean_object* x_681; 
lean_dec(x_674);
if (lean_is_scalar(x_671)) {
 x_681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_681 = x_671;
}
lean_ctor_set(x_681, 0, x_1);
lean_ctor_set(x_681, 1, x_670);
return x_681;
}
}
}
}
}
else
{
lean_object* x_682; 
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
x_682 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_682;
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
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_array_uget(x_1, x_3);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_4, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = lean_array_fget(x_16, x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_17, x_26);
lean_dec(x_17);
lean_ctor_set(x_4, 1, x_27);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = l_Lean_Compiler_LCNF_Arg_toExpr(x_25);
x_30 = lean_st_ref_take(x_6, x_12);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_34, x_28, x_29);
lean_ctor_set(x_31, 0, x_35);
x_36 = lean_st_ref_set(x_6, x_31, x_32);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = 1;
x_39 = lean_usize_add(x_3, x_38);
x_3 = x_39;
x_12 = x_37;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
x_43 = lean_ctor_get(x_31, 2);
x_44 = lean_ctor_get(x_31, 3);
x_45 = lean_ctor_get_uint8(x_31, sizeof(void*)*7);
x_46 = lean_ctor_get(x_31, 4);
x_47 = lean_ctor_get(x_31, 5);
x_48 = lean_ctor_get(x_31, 6);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
x_49 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_41, x_28, x_29);
x_50 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
lean_ctor_set(x_50, 6, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*7, x_45);
x_51 = lean_st_ref_set(x_6, x_50, x_32);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = 1;
x_54 = lean_usize_add(x_3, x_53);
x_3 = x_54;
x_12 = x_52;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; 
lean_dec(x_4);
x_56 = lean_array_fget(x_16, x_17);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_17, x_57);
lean_dec(x_17);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_16);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_18);
x_60 = lean_ctor_get(x_15, 0);
lean_inc(x_60);
lean_dec(x_15);
x_61 = l_Lean_Compiler_LCNF_Arg_toExpr(x_56);
x_62 = lean_st_ref_take(x_6, x_12);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_63, sizeof(void*)*7);
x_70 = lean_ctor_get(x_63, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 5);
lean_inc(x_71);
x_72 = lean_ctor_get(x_63, 6);
lean_inc(x_72);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 lean_ctor_release(x_63, 5);
 lean_ctor_release(x_63, 6);
 x_73 = x_63;
} else {
 lean_dec_ref(x_63);
 x_73 = lean_box(0);
}
x_74 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_65, x_60, x_61);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 7, 1);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_66);
lean_ctor_set(x_75, 2, x_67);
lean_ctor_set(x_75, 3, x_68);
lean_ctor_set(x_75, 4, x_70);
lean_ctor_set(x_75, 5, x_71);
lean_ctor_set(x_75, 6, x_72);
lean_ctor_set_uint8(x_75, sizeof(void*)*7, x_69);
x_76 = lean_st_ref_set(x_6, x_75, x_64);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = 1;
x_79 = lean_usize_add(x_3, x_78);
x_3 = x_79;
x_4 = x_59;
x_12 = x_77;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_st_ref_get(x_3, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_14, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f(x_17, x_4, x_5, x_6, x_7, x_8, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_28);
x_30 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_Compiler_LCNF_eraseCode(x_33, x_5, x_6, x_7, x_8, x_26);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_31) == 0)
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 2);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
x_42 = lean_ctor_get(x_40, 3);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_array_get_size(x_41);
x_44 = l_Array_toSubarray___rarg(x_41, x_42, x_43);
x_45 = lean_array_get_size(x_38);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_38, x_46, x_47, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_50 = l_Lean_Compiler_LCNF_Simp_simp(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Compiler_LCNF_eraseParams(x_38, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_38);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_19, 0, x_51);
lean_ctor_set(x_53, 0, x_19);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
lean_ctor_set(x_19, 0, x_51);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_19);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_38);
lean_free_object(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_36, 1);
lean_inc(x_62);
lean_dec(x_36);
x_63 = lean_ctor_get(x_31, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_31, 2);
lean_inc(x_64);
lean_dec(x_31);
x_65 = lean_ctor_get(x_28, 0);
lean_inc(x_65);
lean_dec(x_28);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_sub(x_65, x_68);
lean_dec(x_65);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_73 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_71, x_72, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_array_get_size(x_63);
x_77 = lean_nat_dec_lt(x_66, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
x_79 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_80 = l___private_Init_Util_0__outOfBounds___rarg(x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_81, x_78, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_75);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_84 = l_Lean_Compiler_LCNF_Simp_simp(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Compiler_LCNF_eraseParams(x_63, x_5, x_6, x_7, x_8, x_86);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_63);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_74);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set(x_19, 0, x_90);
lean_ctor_set(x_87, 0, x_19);
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_74);
lean_ctor_set(x_92, 1, x_85);
lean_ctor_set(x_19, 0, x_92);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_19);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_74);
lean_dec(x_63);
lean_free_object(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_94 = !lean_is_exclusive(x_84);
if (x_94 == 0)
{
return x_84;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_84, 0);
x_96 = lean_ctor_get(x_84, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_84);
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
lean_dec(x_74);
lean_dec(x_64);
lean_dec(x_63);
lean_free_object(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_82);
if (x_98 == 0)
{
return x_82;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_82, 0);
x_100 = lean_ctor_get(x_82, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_82);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_74, 0);
lean_inc(x_102);
x_103 = lean_array_fget(x_63, x_66);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_104, x_102, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_75);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_107 = l_Lean_Compiler_LCNF_Simp_simp(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Compiler_LCNF_eraseParams(x_63, x_5, x_6, x_7, x_8, x_109);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_63);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_110, 0);
lean_dec(x_112);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_74);
lean_ctor_set(x_113, 1, x_108);
lean_ctor_set(x_19, 0, x_113);
lean_ctor_set(x_110, 0, x_19);
return x_110;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_74);
lean_ctor_set(x_115, 1, x_108);
lean_ctor_set(x_19, 0, x_115);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_19);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_74);
lean_dec(x_63);
lean_free_object(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_117 = !lean_is_exclusive(x_107);
if (x_117 == 0)
{
return x_107;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_107, 0);
x_119 = lean_ctor_get(x_107, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_107);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_74);
lean_dec(x_64);
lean_dec(x_63);
lean_free_object(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_105);
if (x_121 == 0)
{
return x_105;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_105, 0);
x_123 = lean_ctor_get(x_105, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_105);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_64);
lean_dec(x_63);
lean_free_object(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = !lean_is_exclusive(x_73);
if (x_125 == 0)
{
return x_73;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_73, 0);
x_127 = lean_ctor_get(x_73, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_73);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; 
lean_dec(x_65);
lean_dec(x_63);
x_129 = l_Lean_Compiler_LCNF_Simp_simp(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
lean_ctor_set(x_19, 0, x_131);
lean_ctor_set(x_129, 0, x_19);
return x_129;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_129, 0);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_129);
lean_ctor_set(x_19, 0, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_19);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_free_object(x_19);
x_135 = !lean_is_exclusive(x_129);
if (x_135 == 0)
{
return x_129;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_129, 0);
x_137 = lean_ctor_get(x_129, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_129);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_28);
x_139 = lean_ctor_get(x_36, 1);
lean_inc(x_139);
lean_dec(x_36);
x_140 = lean_ctor_get(x_31, 0);
lean_inc(x_140);
lean_dec(x_31);
x_141 = l_Lean_Compiler_LCNF_Simp_simp(x_140, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_139);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_141, 0);
lean_ctor_set(x_19, 0, x_143);
lean_ctor_set(x_141, 0, x_19);
return x_141;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_141, 0);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_141);
lean_ctor_set(x_19, 0, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_19);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
else
{
uint8_t x_147; 
lean_free_object(x_19);
x_147 = !lean_is_exclusive(x_141);
if (x_147 == 0)
{
return x_141;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_141, 0);
x_149 = lean_ctor_get(x_141, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_141);
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
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_19, 0);
lean_inc(x_151);
lean_dec(x_19);
x_152 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_151);
x_153 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = l_Lean_Compiler_LCNF_eraseCode(x_156, x_5, x_6, x_7, x_8, x_26);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_158);
if (lean_obj_tag(x_154) == 0)
{
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_ctor_get(x_154, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_154, 2);
lean_inc(x_162);
lean_dec(x_154);
x_163 = lean_ctor_get(x_151, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_151, 1);
lean_inc(x_164);
lean_dec(x_151);
x_165 = lean_ctor_get(x_163, 3);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_array_get_size(x_164);
x_167 = l_Array_toSubarray___rarg(x_164, x_165, x_166);
x_168 = lean_array_get_size(x_161);
x_169 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_170 = 0;
x_171 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_161, x_169, x_170, x_167, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_160);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_173 = l_Lean_Compiler_LCNF_Simp_simp(x_162, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l_Lean_Compiler_LCNF_eraseParams(x_161, x_5, x_6, x_7, x_8, x_175);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_161);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_178 = x_176;
} else {
 lean_dec_ref(x_176);
 x_178 = lean_box(0);
}
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_174);
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_178;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_161);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_181 = lean_ctor_get(x_173, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_173, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_183 = x_173;
} else {
 lean_dec_ref(x_173);
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
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_185 = lean_ctor_get(x_159, 1);
lean_inc(x_185);
lean_dec(x_159);
x_186 = lean_ctor_get(x_154, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_154, 2);
lean_inc(x_187);
lean_dec(x_154);
x_188 = lean_ctor_get(x_151, 0);
lean_inc(x_188);
lean_dec(x_151);
x_189 = lean_unsigned_to_nat(0u);
x_190 = lean_nat_dec_eq(x_188, x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_191 = lean_unsigned_to_nat(1u);
x_192 = lean_nat_sub(x_188, x_191);
lean_dec(x_188);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_192);
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_196 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_194, x_195, x_5, x_6, x_7, x_8, x_185);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_array_get_size(x_186);
x_200 = lean_nat_dec_lt(x_189, x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_197, 0);
lean_inc(x_201);
x_202 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_203 = l___private_Init_Util_0__outOfBounds___rarg(x_202);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec(x_203);
x_205 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_204, x_201, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_198);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_207 = l_Lean_Compiler_LCNF_Simp_simp(x_187, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = l_Lean_Compiler_LCNF_eraseParams(x_186, x_5, x_6, x_7, x_8, x_209);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_186);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_212 = x_210;
} else {
 lean_dec_ref(x_210);
 x_212 = lean_box(0);
}
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_197);
lean_ctor_set(x_213, 1, x_208);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
if (lean_is_scalar(x_212)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_212;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_211);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_197);
lean_dec(x_186);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_216 = lean_ctor_get(x_207, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_207, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_218 = x_207;
} else {
 lean_dec_ref(x_207);
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
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_197);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_220 = lean_ctor_get(x_205, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_205, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_222 = x_205;
} else {
 lean_dec_ref(x_205);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_197, 0);
lean_inc(x_224);
x_225 = lean_array_fget(x_186, x_189);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec(x_225);
x_227 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_226, x_224, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_198);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_229 = l_Lean_Compiler_LCNF_Simp_simp(x_187, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_228);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = l_Lean_Compiler_LCNF_eraseParams(x_186, x_5, x_6, x_7, x_8, x_231);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_186);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_234 = x_232;
} else {
 lean_dec_ref(x_232);
 x_234 = lean_box(0);
}
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_197);
lean_ctor_set(x_235, 1, x_230);
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_235);
if (lean_is_scalar(x_234)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_234;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_233);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_197);
lean_dec(x_186);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_238 = lean_ctor_get(x_229, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_229, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_240 = x_229;
} else {
 lean_dec_ref(x_229);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_197);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_242 = lean_ctor_get(x_227, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_227, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_244 = x_227;
} else {
 lean_dec_ref(x_227);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_246 = lean_ctor_get(x_196, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_196, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_248 = x_196;
} else {
 lean_dec_ref(x_196);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; 
lean_dec(x_188);
lean_dec(x_186);
x_250 = l_Lean_Compiler_LCNF_Simp_simp(x_187, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_185);
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
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_151);
x_260 = lean_ctor_get(x_159, 1);
lean_inc(x_260);
lean_dec(x_159);
x_261 = lean_ctor_get(x_154, 0);
lean_inc(x_261);
lean_dec(x_154);
x_262 = l_Lean_Compiler_LCNF_Simp_simp(x_261, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_260);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_263);
if (lean_is_scalar(x_265)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_265;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_264);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_262, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_262, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_270 = x_262;
} else {
 lean_dec_ref(x_262);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
}
}
}
else
{
lean_object* x_272; uint8_t x_273; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_272 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_273 = !lean_is_exclusive(x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_272, 0);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_272, 0, x_275);
return x_272;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_272, 0);
x_277 = lean_ctor_get(x_272, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_272);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_276);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_st_ref_get(x_4, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_15, x_1, x_11);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(x_2, x_16, x_6, x_7, x_8, x_9, x_14);
return x_17;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_st_ref_get(x_3, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_14, x_15, x_10);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(x_15, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Compiler_LCNF_Simp_simp(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_16, x_19, x_23, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
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
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Compiler_LCNF_Simp_simp___lambda__7(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
